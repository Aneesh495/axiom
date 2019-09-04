import Foundation

/// Minimalist test framework and test runner for Axiom.
public final class TestHarness: @unchecked Sendable {
    public static let shared = TestHarness()

    private var passedCount = 0
    private var failedCount = 0
    private var currentSuite = ""

    public init() {}

    public func suite(_ name: String, execute: () -> Void) {
        currentSuite = name
        print("\n\u{001B}[1;34m=== Test Suite: \(name) ===\u{001B}[0m")
        execute()
    }

    public func test(_ name: String, execute: () throws -> Void) {
        let start = DispatchTime.now()
        do {
            try execute()
            let end = DispatchTime.now()
            let nanos = end.uptimeNanoseconds - start.uptimeNanoseconds
            let ms = Double(nanos) / 1_000_000.0
            passedCount += 1
            print("  \u{001B}[32m✓\u{001B}[0m \(name) (\(String(format: "%.3f", ms)) ms)")
        } catch {
            failedCount += 1
            print("  \u{001B}[31m✗\u{001B}[0m \(name): \(error)")
        }
    }

    public func expectEqual<T: Equatable>(_ a: T, _ b: T, _ message: String = "", file: StaticString = #file, line: UInt = #line) {
        if a != b {
            fatalError("Assertion failure: \(a) != \(b) [\(message)] at \(file):\(line)")
        }
    }

    public func expectNotEqual<T: Equatable>(_ a: T, _ b: T, _ message: String = "", file: StaticString = #file, line: UInt = #line) {
        if a == b {
            fatalError("Assertion failure: \(a) == \(b) [\(message)] at \(file):\(line)")
        }
    }

    public func expectTrue(_ condition: Bool, _ message: String = "", file: StaticString = #file, line: UInt = #line) {
        if !condition {
            fatalError("Assertion failure: expected true [\(message)] at \(file):\(line)")
        }
    }

    public func expectFalse(_ condition: Bool, _ message: String = "", file: StaticString = #file, line: UInt = #line) {
        if condition {
            fatalError("Assertion failure: expected false [\(message)] at \(file):\(line)")
        }
    }

    public func expectNil<T>(_ value: T?, _ message: String = "", file: StaticString = #file, line: UInt = #line) {
        if value != nil {
            fatalError("Assertion failure: expected nil [\(message)] at \(file):\(line)")
        }
    }

    public func expectNotNil<T>(_ value: T?, _ message: String = "", file: StaticString = #file, line: UInt = #line) {
        if value == nil {
            fatalError("Assertion failure: expected not nil [\(message)] at \(file):\(line)")
        }
    }

    public func reportAndExit() -> Never {
        print("\n\u{001B}[1;36m----------------------------------------\u{001B}[0m")
        print("\u{001B}[1mTest Summary:\u{001B}[0m \u{001B}[32m\(passedCount) passed\u{001B}[0m, \u{001B}[31m\(failedCount) failed\u{001B}[0m")
        if failedCount > 0 {
            print("\u{001B}[1;31mFAILED TESTS DETECTED\u{001B}[0m\n")
            exit(1)
        } else {
            print("\u{001B}[1;32mALL TESTS PASSED SMOOTHLY\u{001B}[0m\n")
            exit(0)
        }
    }
}
