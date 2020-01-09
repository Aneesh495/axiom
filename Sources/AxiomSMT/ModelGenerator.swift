import Foundation
import AxiomCore
import AxiomAST
import AxiomSAT
import AxiomTheories

/// Complete First-Order Logic SMT Model representing a satisfying assignment across all theories.
public struct SMTModel: CustomStringConvertible, Sendable {
    public var boolValues: [Symbol: Bool]
    public var intValues: [Symbol: BigInt]
    public var realValues: [Symbol: Rational]
    public var bvValues: [Symbol: BitVector]
    public var arrayValues: [Symbol: (defaultValue: Expr?, storeMap: [Expr: Expr])]
    public var functionValues: [Symbol: [([Expr], Expr)]]

    public init(
        boolValues: [Symbol: Bool] = [:],
        intValues: [Symbol: BigInt] = [:],
        realValues: [Symbol: Rational] = [:],
        bvValues: [Symbol: BitVector] = [:],
        arrayValues: [Symbol: (defaultValue: Expr?, storeMap: [Expr: Expr])] = [:],
        functionValues: [Symbol: [([Expr], Expr)]] = [:]
    ) {
        self.boolValues = boolValues
        self.intValues = intValues
        self.realValues = realValues
        self.bvValues = bvValues
        self.arrayValues = arrayValues
        self.functionValues = functionValues
    }

    // MARK: - Term Evaluation

    /// Evaluate an AST expression under this model, returning the concrete value term.
    public func evaluate(_ expr: Expr) -> Expr? {
        switch expr {
        case .boolConst, .intConst, .realConst, .bvConst, .stringConst:
            return expr

        case let .variable(name, sort):
            switch sort {
            case .bool:
                return boolValues[name].map { .boolConst($0) }
            case .int:
                return intValues[name].map { .intConst($0) }
            case .real:
                return realValues[name].map { .realConst($0) }
            case .bitVec:
                return bvValues[name].map { .bvConst($0) }
            default:
                return nil
            }

        case let .not(child):
            guard let v = evaluate(child), case let .boolConst(b) = v else { return nil }
            return .boolConst(!b)

        case let .and(children):
            for c in children {
                guard let v = evaluate(c), case let .boolConst(b) = v else { return nil }
                if !b { return .boolConst(false) }
            }
            return .boolConst(true)

        case let .or(children):
            for c in children {
                guard let v = evaluate(c), case let .boolConst(b) = v else { return nil }
                if b { return .boolConst(true) }
            }
            return .boolConst(false)

        case let .eq(lhs, rhs):
            guard let l = evaluate(lhs), let r = evaluate(rhs) else { return nil }
            return .boolConst(l == r)

        case let .add(args):
            if expr.sort.isReal {
                var sum = Rational.zero
                for a in args {
                    guard let v = evaluate(a), case let .realConst(r) = v else { return nil }
                    sum = sum + r
                }
                return .realConst(sum)
            } else {
                var sum = BigInt.zero
                for a in args {
                    guard let v = evaluate(a), case let .intConst(i) = v else { return nil }
                    sum = sum + i
                }
                return .intConst(sum)
            }

        case let .sub(lhs, rhs):
            guard let l = evaluate(lhs), let r = evaluate(rhs) else { return nil }
            if expr.sort.isReal, case let .realConst(r1) = l, case let .realConst(r2) = r {
                return .realConst(r1 - r2)
            } else if case let .intConst(i1) = l, case let .intConst(i2) = r {
                return .intConst(i1 - i2)
            }
            return nil

        case let .mul(args):
            if expr.sort.isReal {
                var prod = Rational.one
                for a in args {
                    guard let v = evaluate(a), case let .realConst(r) = v else { return nil }
                    prod = prod * r
                }
                return .realConst(prod)
            } else {
                var prod = BigInt.one
                for a in args {
                    guard let v = evaluate(a), case let .intConst(i) = v else { return nil }
                    prod = prod * i
                }
                return .intConst(prod)
            }

        case let .bvAdd(lhs, rhs):
            guard let l = evaluate(lhs), let r = evaluate(rhs),
                  case let .bvConst(bv1) = l, case let .bvConst(bv2) = r else { return nil }
            return .bvConst(bv1 + bv2)

        case let .bvSub(lhs, rhs):
            guard let l = evaluate(lhs), let r = evaluate(rhs),
                  case let .bvConst(bv1) = l, case let .bvConst(bv2) = r else { return nil }
            return .bvConst(bv1 - bv2)

        case let .bvMul(lhs, rhs):
            guard let l = evaluate(lhs), let r = evaluate(rhs),
                  case let .bvConst(bv1) = l, case let .bvConst(bv2) = r else { return nil }
            return .bvConst(bv1 * bv2)

        case let .select(array, index):
            guard case let .variable(arrName, _) = array,
                  let arrModel = arrayValues[arrName],
                  let evalIdx = evaluate(index) else { return nil }
            if let storedVal = arrModel.storeMap[evalIdx] {
                return storedVal
            }
            return arrModel.defaultValue

        default:
            return nil
        }
    }

    // MARK: - Pretty Printing

    public var description: String {
        return formatSMTLIB()
    }

    public func formatSMTLIB() -> String {
        var lines: [String] = ["(model"]

        for (sym, b) in boolValues.sorted(by: { $0.key.name < $1.key.name }) {
            lines.append("  (define-fun \(sym.name) () Bool \(b))")
        }

        for (sym, i) in intValues.sorted(by: { $0.key.name < $1.key.name }) {
            lines.append("  (define-fun \(sym.name) () Int \(i))")
        }

        for (sym, r) in realValues.sorted(by: { $0.key.name < $1.key.name }) {
            lines.append("  (define-fun \(sym.name) () Real \(r))")
        }

        for (sym, bv) in bvValues.sorted(by: { $0.key.name < $1.key.name }) {
            lines.append("  (define-fun \(sym.name) () (_ BitVec \(bv.width)) \(bv))")
        }

        lines.append(")")
        return lines.joined(separator: "\n")
    }
}

/// SMT Model Generator synthesizing joint valuations across multiple theory solvers.
public final class ModelGenerator: @unchecked Sendable {
    public init() {}

    /// Extract a unified SMTModel from the current state of theory solvers and SAT engine.
    public func generateModel(
        variables: Set<Expr>,
        satSolver: SATSolver?,
        lraSolver: LRASolver?,
        liaSolver: LIASolver?,
        bvSolver: BVSolver?,
        arraySolver: ArraySolver?
    ) -> SMTModel {
        var model = SMTModel()

        for v in variables {
            guard case let .variable(sym, sort) = v else { continue }

            switch sort {
            case .bool:
                if let sat = satSolver {
                    let boolVal = sat.modelValue(for: Int32(sym.name.hashValue & 0x7FFFFFFF))
                    model.boolValues[sym] = boolVal
                } else {
                    model.boolValues[sym] = true
                }

            case .real:
                if let lra = lraSolver, let val = lra.variableValue(v) {
                    model.realValues[sym] = val
                } else {
                    model.realValues[sym] = Rational.zero
                }

            case .int:
                if let lia = liaSolver, let val = lia.integerVariableValue(v) {
                    model.intValues[sym] = val
                } else if let lra = lraSolver, let val = lra.variableValue(v) {
                    model.intValues[sym] = val.floor
                } else {
                    model.intValues[sym] = BigInt.zero
                }

            case .bitVec(let width):
                if let bv = bvSolver, let val = bv.getValue(of: v) {
                    model.bvValues[sym] = val
                } else {
                    model.bvValues[sym] = BitVector.zero(width: width)
                }

            case .array:
                model.arrayValues[sym] = (defaultValue: nil, storeMap: [:])

            default:
                break
            }
        }

        return model
    }
}
