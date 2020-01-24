import Foundation
import AxiomCore
import AxiomAST
import AxiomSMT

/// Execution environment for SMT-LIB 2.6 scripts.
/// Dispatches declarative and execution commands to an underlying SMTSolver
/// and formats responses according to the official SMT-LIB 2.6 standard.
public final class SMTLIBEnvironment: @unchecked Sendable {
    public let solver: SMTSolver
    public private(set) var logic: String?
    public private(set) var options: [String: String]
    public private(set) var info: [String: String]
    private var outputs: [String]

    public init() {
        self.solver = SMTSolver()
        self.logic = nil
        self.options = [:]
        self.info = [:]
        self.outputs = []
    }

    /// Reset environment to default state.
    public func reset() {
        solver.reset()
        logic = nil
        options.removeAll(keepingCapacity: true)
        info.removeAll(keepingCapacity: true)
        outputs.removeAll(keepingCapacity: true)
    }

    /// Execute a sequence of parsed SMT-LIB commands, returning the combined output lines.
    public func execute(commands: [SMTLIBCommand]) -> [String] {
        outputs.removeAll(keepingCapacity: true)
        for cmd in commands {
            execute(command: cmd)
        }
        return outputs
    }

    /// Execute a complete SMT-LIB script string.
    public func execute(script: String) throws -> [String] {
        let parser = SMTLIBParser(input: script)
        let commands = try parser.parseCommands()
        return execute(commands: commands)
    }

    /// Execute a single SMT-LIB command.
    public func execute(command: SMTLIBCommand) {
        switch command {
        case let .setLogic(l):
            self.logic = l

        case let .setOption(keyword, value):
            self.options[keyword] = value

        case let .setInfo(keyword, value):
            self.info[keyword] = value

        case .declareSort:
            break

        case .declareConst:
            break

        case .declareFun:
            break

        case .defineFun:
            break

        case let .assert(expr):
            solver.assert(expr)

        case .checkSat:
            let res = solver.check()
            outputs.append(res.rawValue)

        case let .checkSatAssuming(assumptions):
            let res = solver.check(assumptions: assumptions)
            outputs.append(res.rawValue)

        case .getModel:
            if let model = solver.getModel() {
                outputs.append(model.formatSMTLIB())
            } else {
                outputs.append("(error \"model is not available\")")
            }

        case let .getValue(terms):
            if let model = solver.getModel() {
                var lines = ["("]
                for t in terms {
                    let val = model.evaluate(t)?.description ?? "unknown"
                    lines.append("  (\(t.description) \(val))")
                }
                lines.append(")")
                outputs.append(lines.joined(separator: "\n"))
            } else {
                outputs.append("(error \"model is not available\")")
            }

        case .getUnsatCore:
            if let core = solver.getUnsatCore() {
                outputs.append(core.description)
            } else {
                outputs.append("(error \"unsat core is not available\")")
            }

        case let .push(n):
            for _ in 0..<n {
                solver.push()
            }

        case let .pop(n):
            for _ in 0..<n {
                solver.pop()
            }

        case .exit:
            break
        }
    }
}
