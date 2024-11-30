import Foundation
import AxiomCore

/// SMT-LIB 2.6 AST serializer, mathematical infix printer, and ANSI syntax colorizer.
public struct ASTPrinter: Sendable {
    public enum Style: Sendable {
        case smtlib
        case infix
        case ansiColored
        case latex
    }

    public let style: Style

    public init(style: Style = .smtlib) {
        self.style = style
    }

    public func printExpr(_ expr: Expr) -> String {
        switch style {
        case .smtlib:
            return expr.description
        case .infix:
            return formatInfix(expr)
        case .ansiColored:
            return formatANSI(expr)
        case .latex:
            return formatLaTeX(expr)
        }
    }

    // MARK: - Mathematical Infix Formatting

    private func formatInfix(_ expr: Expr, parentPrecedence: Int = 0) -> String {
        switch expr {
        case let .boolConst(b):
            return b ? "true" : "false"
        case let .intConst(i):
            return i.description
        case let .realConst(r):
            return r.description
        case let .bvConst(bv):
            return bv.hexDescription
        case let .stringConst(s):
            return "\"\(s)\""
        case let .variable(name, _):
            return name.name

        case let .not(inner):
            return "¬" + formatInfix(inner, parentPrecedence: 90)

        case let .and(args):
            let formatted = args.map { formatInfix($0, parentPrecedence: 40) }.joined(separator: " ∧ ")
            return parentPrecedence > 40 ? "(\(formatted))" : formatted

        case let .or(args):
            let formatted = args.map { formatInfix($0, parentPrecedence: 30) }.joined(separator: " ∨ ")
            return parentPrecedence > 30 ? "(\(formatted))" : formatted

        case let .implies(lhs, rhs):
            let formatted = "\(formatInfix(lhs, parentPrecedence: 25)) ⇒ \(formatInfix(rhs, parentPrecedence: 20))"
            return parentPrecedence > 20 ? "(\(formatted))" : formatted

        case let .eq(lhs, rhs):
            return "\(formatInfix(lhs, parentPrecedence: 50)) = \(formatInfix(rhs, parentPrecedence: 50))"

        case let .lt(lhs, rhs):
            return "\(formatInfix(lhs, parentPrecedence: 50)) < \(formatInfix(rhs, parentPrecedence: 50))"

        case let .le(lhs, rhs):
            return "\(formatInfix(lhs, parentPrecedence: 50)) ≤ \(formatInfix(rhs, parentPrecedence: 50))"

        case let .gt(lhs, rhs):
            return "\(formatInfix(lhs, parentPrecedence: 50)) > \(formatInfix(rhs, parentPrecedence: 50))"

        case let .ge(lhs, rhs):
            return "\(formatInfix(lhs, parentPrecedence: 50)) ≥ \(formatInfix(rhs, parentPrecedence: 50))"

        case let .add(args):
            let formatted = args.map { formatInfix($0, parentPrecedence: 60) }.joined(separator: " + ")
            return parentPrecedence > 60 ? "(\(formatted))" : formatted

        case let .sub(lhs, rhs):
            let formatted = "\(formatInfix(lhs, parentPrecedence: 60)) - \(formatInfix(rhs, parentPrecedence: 65))"
            return parentPrecedence > 60 ? "(\(formatted))" : formatted

        case let .mul(args):
            let formatted = args.map { formatInfix($0, parentPrecedence: 70) }.joined(separator: " * ")
            return parentPrecedence > 70 ? "(\(formatted))" : formatted

        case let .div(lhs, rhs):
            let formatted = "\(formatInfix(lhs, parentPrecedence: 70)) / \(formatInfix(rhs, parentPrecedence: 75))"
            return parentPrecedence > 70 ? "(\(formatted))" : formatted

        case let .apply(f, args, _):
            return "\(f.name)(\(args.map { formatInfix($0) }.joined(separator: ", ")))"

        case let .select(arr, idx):
            return "\(formatInfix(arr))[\(formatInfix(idx))]"

        case let .store(arr, idx, val):
            return "\(formatInfix(arr)){\(formatInfix(idx)) ↦ \(formatInfix(val))}"

        default:
            return expr.description
        }
    }

    // MARK: - ANSI Color Formatting

    private func formatANSI(_ expr: Expr) -> String {
        let blue = "\u{001B}[34m"
        let green = "\u{001B}[32m"
        let yellow = "\u{001B}[33m"
        let magenta = "\u{001B}[35m"
        let cyan = "\u{001B}[36m"
        let reset = "\u{001B}[0m"

        switch expr {
        case let .boolConst(b):
            return "\(yellow)\(b)\(reset)"
        case let .intConst(i):
            return "\(yellow)\(i)\(reset)"
        case let .realConst(r):
            return "\(yellow)\(r)\(reset)"
        case let .bvConst(bv):
            return "\(yellow)\(bv.hexDescription)\(reset)"
        case let .stringConst(s):
            return "\(green)\"\(s)\"\(reset)"
        case let .variable(name, sort):
            return "\(green)\(name.name)\(reset):\(cyan)\(sort.description)\(reset)"
        case let .not(inner):
            return "(\(magenta)not\(reset) \(formatANSI(inner)))"
        case let .and(args):
            return "(\(magenta)and\(reset) \(args.map { formatANSI($0) }.joined(separator: " ")))"
        case let .or(args):
            return "(\(magenta)or\(reset) \(args.map { formatANSI($0) }.joined(separator: " ")))"
        case let .eq(a, b):
            return "(\(blue)=\(reset) \(formatANSI(a)) \(formatANSI(b)))"
        case let .lt(a, b):
            return "(\(blue)<\(reset) \(formatANSI(a)) \(formatANSI(b)))"
        case let .le(a, b):
            return "(\(blue)<=\(reset) \(formatANSI(a)) \(formatANSI(b)))"
        case let .add(args):
            return "(\(blue)+\(reset) \(args.map { formatANSI($0) }.joined(separator: " ")))"
        case let .mul(args):
            return "(\(blue)*\(reset) \(args.map { formatANSI($0) }.joined(separator: " ")))"
        default:
            return expr.description
        }
    }

    // MARK: - LaTeX Formatting

    private func formatLaTeX(_ expr: Expr) -> String {
        switch expr {
        case let .boolConst(b):
            return b ? "\\top" : "\\bot"
        case let .intConst(i):
            return i.description
        case let .realConst(r):
            if r.denominator == BigInt.one { return r.numerator.description }
            return "\\frac{\(r.numerator)}{\(r.denominator)}"
        case let .variable(name, _):
            return name.name
        case let .not(inner):
            return "\\neg \(formatLaTeX(inner))"
        case let .and(args):
            return args.map { formatLaTeX($0) }.joined(separator: " \\land ")
        case let .or(args):
            return args.map { formatLaTeX($0) }.joined(separator: " \\lor ")
        case let .implies(lhs, rhs):
            return "\(formatLaTeX(lhs)) \\implies \(formatLaTeX(rhs))"
        case let .eq(lhs, rhs):
            return "\(formatLaTeX(lhs)) = \(formatLaTeX(rhs))"
        case let .le(lhs, rhs):
            return "\(formatLaTeX(lhs)) \\le \(formatLaTeX(rhs))"
        case let .lt(lhs, rhs):
            return "\(formatLaTeX(lhs)) < \(formatLaTeX(rhs))"
        case let .add(args):
            return args.map { formatLaTeX($0) }.joined(separator: " + ")
        case let .mul(args):
            return args.map { formatLaTeX($0) }.joined(separator: " \\cdot ")
        default:
            return expr.description
        }
    }
}
