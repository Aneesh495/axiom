import Foundation
import AxiomCore
import AxiomAST
import AxiomSAT
import AxiomTheories
import AxiomSMT
import AxiomParser
import AxiomVerify
import AxiomUI

@main
struct AxiomMain {
    static func main() {
        let args = CommandLine.arguments

        if args.count == 1 {
            runREPL()
            return
        }

        var showModel = false
        var showUnsatCore = false
        var showStats = false
        var filePath: String?

        var idx = 1
        while idx < args.count {
            let arg = args[idx]
            switch arg {
            case "-h", "--help":
                printHelp()
                return

            case "-v", "--version":
                print("Axiom Formal Verification Kernel v\(AxiomCoreModule.version)")
                print("Architectures: CDCL(T), Nelson-Oppen, QF_LRA, QF_LIA, QF_BV, QF_AX, Dijkstra VCGen")
                return

            case "--repl":
                runREPL()
                return

            case "-m", "--model":
                showModel = true

            case "-u", "--unsat-core":
                showUnsatCore = true

            case "-s", "--stats":
                showStats = true

            default:
                if arg == "-" || !arg.hasPrefix("-") {
                    filePath = arg
                } else {
                    print("Unknown option: \(arg)")
                    printHelp()
                    exit(1)
                }
            }
            idx += 1
        }

        guard let path = filePath else {
            runREPL()
            return
        }

        executeFile(path: path, showModel: showModel, showUnsatCore: showUnsatCore, showStats: showStats)
    }

    private static func printHelp() {
        print("""
        Usage: axiom [options] [file.smt2 | -]

        Options:
          -h, --help        Show this help manual
          -v, --version     Show version and build specifications
          --repl            Start interactive SMT-LIB 2.6 read-eval-print loop
          -m, --model       Output satisfying variable assignments on SAT
          -u, --unsat-core  Extract minimal unsatisfiable core on UNSAT
          -s, --stats       Display execution timing and solver heuristics
        """)
    }

    private static func executeFile(path: String, showModel: Bool, showUnsatCore: Bool, showStats: Bool) {
        let content: String
        if path == "-" {
            // Read from standard input
            var lines: [String] = []
            while let line = readLine() {
                lines.append(line)
            }
            content = lines.joined(separator: "\n")
        } else {
            guard let fileContent = try? String(contentsOfFile: path, encoding: .utf8) else {
                print("Error: Could not read file at \(path)")
                exit(1)
            }
            content = fileContent
        }

        let start = DispatchTime.now()
        let parser = SMTLIBParser(input: content)
        let commands: [SMTLIBCommand]
        do {
            commands = try parser.parseCommands()
        } catch {
            print("Parser Error: \(error)")
            exit(1)
        }

        let solver = SMTSolver()
        var lastRes: SMTResult = .unknown

        for cmd in commands {
            switch cmd {
            case let .setLogic(logic):
                _ = logic

            case let .declareConst(name, sort):
                _ = solver.assert(.variable(name: name, sort: sort))

            case .declareFun, .declareSort, .defineFun, .setOption, .setInfo, .getValue:
                break

            case let .assert(expr):
                _ = solver.assert(expr)

            case .checkSat:
                lastRes = solver.check()
                switch lastRes {
                case .sat:
                    print("sat")
                    if showModel, let model = solver.getModel() {
                        print(model.description)
                    }
                case .unsat:
                    print("unsat")
                    if showUnsatCore, let core = solver.getUnsatCore() {
                        print(core.description)
                    }
                case .unknown:
                    print("unknown")
                }

            case let .checkSatAssuming(assumptions):
                lastRes = solver.check(assumptions: assumptions)
                print(lastRes.description)

            case .getModel:
                if let model = solver.getModel() {
                    print(model.description)
                } else {
                    print("(error \"model not available\")")
                }

            case .getUnsatCore:
                if let core = solver.getUnsatCore() {
                    print(core.description)
                } else {
                    print("(error \"unsat core not available\")")
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
                if showStats {
                    printStats(start: start)
                }
                return
            }
        }

        if showStats {
            printStats(start: start)
        }
    }

    private static func runREPL() {
        print("Axiom Interactive SMT-LIB 2.6 REPL")
        print("Type '(exit)' or press Ctrl+D to terminate session.\n")

        let solver = SMTSolver()

        while true {
            print("axiom> ", terminator: "")
            fflush(stdout)
            guard let line = readLine() else {
                print("\nSession terminated.")
                break
            }

            let trimmed = line.trimmingCharacters(in: .whitespacesAndNewlines)
            if trimmed.isEmpty { continue }
            if trimmed == "(exit)" || trimmed == "exit" || trimmed == "quit" {
                print("Bye.")
                break
            }

            let parser = SMTLIBParser(input: trimmed)
            do {
                let commands = try parser.parseCommands()
                for cmd in commands {
                    switch cmd {
                    case let .assert(expr):
                        _ = solver.assert(expr)
                        print("success")
                    case .checkSat:
                        let res = solver.check()
                        print(res.description)
                    case .getModel:
                        if let model = solver.getModel() {
                            print(model.description)
                        } else {
                            print("(error \"model not available\")")
                        }
                    case let .push(n):
                        for _ in 0..<n { solver.push() }
                        print("success")
                    case let .pop(n):
                        for _ in 0..<n { solver.pop() }
                        print("success")
                    case .exit:
                        print("Bye.")
                        return
                    default:
                        print("success")
                    }
                }
            } catch {
                print("(error \"\(error)\")")
            }
        }
    }

    private static func printStats(start: DispatchTime) {
        let end = DispatchTime.now()
        let nanos = end.uptimeNanoseconds - start.uptimeNanoseconds
        let ms = Double(nanos) / 1_000_000.0
        print(String(format: "\nExecution Time: %.3f ms", ms))
    }
}
