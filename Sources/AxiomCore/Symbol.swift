import Foundation

/// Fast string interning for AST identifiers, function symbols, and sort names.
/// Provides O(1) equality comparison, O(1) hashing, and thread-safe global interning.
public struct Symbol: Hashable, Comparable, CustomStringConvertible, ExpressibleByStringLiteral, Sendable {
    /// Unique 32-bit integer identifier
    public let id: UInt32

    // MARK: - Initializer

    public init(id: UInt32) {
        self.id = id
    }

    public init(_ string: String) {
        self = SymbolPool.shared.intern(string)
    }

    public init(stringLiteral value: String) {
        self.init(value)
    }

    // MARK: - Properties

    public var name: String {
        return SymbolPool.shared.resolve(self)
    }

    public var description: String {
        return name
    }

    // MARK: - Equatable & Comparable

    public static func == (lhs: Symbol, rhs: Symbol) -> Bool {
        return lhs.id == rhs.id
    }

    public func hash(into hasher: inout Hasher) {
        hasher.combine(id)
    }

    public static func < (lhs: Symbol, rhs: Symbol) -> Bool {
        return lhs.id < rhs.id
    }
}

/// Global thread-safe symbol interning pool
public final class SymbolPool: @unchecked Sendable {
    public static let shared = SymbolPool()

    private let lock = NSLock()
    private var stringToId: [String: UInt32] = [:]
    private var idToString: [String] = []

    public init() {
        // Reserve id 0 as empty or null symbol
        idToString.append("")
        stringToId[""] = 0
    }

    public func intern(_ string: String) -> Symbol {
        lock.lock()
        defer { lock.unlock() }

        if let existingId = stringToId[string] {
            return Symbol(id: existingId)
        }

        let newId = UInt32(idToString.count)
        idToString.append(string)
        stringToId[string] = newId
        return Symbol(id: newId)
    }

    public func resolve(_ symbol: Symbol) -> String {
        lock.lock()
        defer { lock.unlock() }

        let idx = Int(symbol.id)
        guard idx >= 0 && idx < idToString.count else {
            return "<invalid-symbol:\(symbol.id)>"
        }
        return idToString[idx]
    }

    public var count: Int {
        lock.lock()
        defer { lock.unlock() }
        return idToString.count
    }
}

/// Scoped symbol table supporting hierarchical environments and push/pop scopes
public final class SymbolTable<T>: @unchecked Sendable {
    private var scopes: [[Symbol: T]]

    public init() {
        self.scopes = [[:]]
    }

    public func pushScope() {
        scopes.append([:])
    }

    public func popScope() {
        precondition(scopes.count > 1, "Cannot pop the root scope in SymbolTable")
        scopes.removeLast()
    }

    public func insert(symbol: Symbol, value: T) {
        let lastIdx = scopes.count - 1
        scopes[lastIdx][symbol] = value
    }

    public func lookup(symbol: Symbol) -> T? {
        for scope in scopes.reversed() {
            if let val = scope[symbol] {
                return val
            }
        }
        return nil
    }

    public func lookupCurrentScope(symbol: Symbol) -> T? {
        return scopes.last?[symbol]
    }

    public var currentDepth: Int {
        return scopes.count
    }
}
