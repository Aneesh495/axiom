import Foundation

/// Watcher entry storing clause reference and a cached blocking literal.
/// The blocker avoids dereferencing the clause when the blocker literal is already satisfied.
public struct Watcher: Sendable {
    public let clauseIndex: Int
    public var blocker: Literal

    public init(clauseIndex: Int, blocker: Literal) {
        self.clauseIndex = clauseIndex
        self.blocker = blocker
    }
}

/// Two-Watched-Literal (2WL) tracking lists indexed by Literal.rawValue.
public final class WatchedList: @unchecked Sendable {
    private var watches: [[Watcher]]

    public init() {
        self.watches = []
    }

    public func initForVariables(count: Int) {
        let litCount = count * 2
        watches = [[Watcher]](repeating: [], count: litCount)
    }

    public func ensureCapacity(forLiteral lit: Literal) {
        let needed = Int(lit.rawValue) + 1
        if needed > watches.count {
            let addCount = needed - watches.count
            watches.append(contentsOf: repeatElement([], count: addCount))
        }
    }

    public func addWatch(literal: Literal, watcher: Watcher) {
        ensureCapacity(forLiteral: literal)
        watches[Int(literal.rawValue)].append(watcher)
    }

    public func watchers(for literal: Literal) -> [Watcher] {
        let idx = Int(literal.rawValue)
        guard idx < watches.count else { return [] }
        return watches[idx]
    }

    public func clearWatchers(for literal: Literal) {
        let idx = Int(literal.rawValue)
        guard idx < watches.count else { return }
        watches[idx].removeAll(keepingCapacity: true)
    }

    public func setWatchers(for literal: Literal, to newWatchers: [Watcher]) {
        ensureCapacity(forLiteral: literal)
        watches[Int(literal.rawValue)] = newWatchers
    }
}
