import Foundation
import CAxiomKernel

/// Cache-conscious, 64-bit word-packed dynamic bit-set for SAT visited sets and clause filters.
/// Features hardware popcount, fast trailing-zero bit iteration, and SIMD acceleration.
public struct BitSet: Hashable, Sequence, Sendable {
    public private(set) var words: [UInt64]
    public private(set) var capacity: Int

    // MARK: - Initializer

    public init(capacity: Int = 64) {
        self.capacity = capacity
        let wordCount = (capacity + 63) / 64
        self.words = [UInt64](repeating: 0, count: Swift.max(1, wordCount))
    }

    public init(words: [UInt64], capacity: Int) {
        self.capacity = capacity
        self.words = words
    }

    // MARK: - Element Mutation

    public mutating func insert(_ index: Int) {
        ensureCapacity(index + 1)
        let wordIdx = index / 64
        let bitOffset = index % 64
        words[wordIdx] |= (UInt64(1) << bitOffset)
    }

    public mutating func remove(_ index: Int) {
        guard index < capacity else { return }
        let wordIdx = index / 64
        let bitOffset = index % 64
        words[wordIdx] &= ~(UInt64(1) << bitOffset)
    }

    public func contains(_ index: Int) -> Bool {
        guard index < capacity else { return false }
        let wordIdx = index / 64
        let bitOffset = index % 64
        return (words[wordIdx] & (UInt64(1) << bitOffset)) != 0
    }

    public mutating func clear() {
        for i in 0..<words.count {
            words[i] = 0
        }
    }

    private mutating func ensureCapacity(_ minCapacity: Int) {
        if minCapacity > capacity {
            capacity = Swift.max(minCapacity, capacity * 2)
            let wordCount = (capacity + 63) / 64
            if wordCount > words.count {
                words.append(contentsOf: repeatElement(0, count: wordCount - words.count))
            }
        }
    }

    // MARK: - Population Count & Iteration

    public var count: Int {
        return words.withUnsafeBufferPointer { buf in
            Int(axiom_popcount64_array(buf.baseAddress, buf.count))
        }
    }

    public var isEmpty: Bool {
        return words.withUnsafeBufferPointer { buf in
            axiom_vec_is_zero(buf.baseAddress, buf.count) != 0
        }
    }

    public func nextSetBit(after start: Int) -> Int? {
        let bitIndex = start + 1
        guard bitIndex < capacity else { return nil }

        let wordIdx = bitIndex / 64
        let bitOffset = bitIndex % 64

        if wordIdx >= words.count { return nil }

        // Check remaining bits in current word
        let currentWord = words[wordIdx] >> bitOffset
        if currentWord != 0 {
            return bitIndex + currentWord.trailingZeroBitCount
        }

        // Scan subsequent words
        var scanIdx = wordIdx + 1
        while scanIdx < words.count {
            let w = words[scanIdx]
            if w != 0 {
                return scanIdx * 64 + w.trailingZeroBitCount
            }
            scanIdx += 1
        }
        return nil
    }

    // MARK: - Sequence Conformance

    public struct Iterator: IteratorProtocol {
        private let bitSet: BitSet
        private var current: Int?

        init(bitSet: BitSet) {
            self.bitSet = bitSet
            self.current = bitSet.nextSetBit(after: -1)
        }

        public mutating func next() -> Int? {
            guard let curr = current else { return nil }
            current = bitSet.nextSetBit(after: curr)
            return curr
        }
    }

    public func makeIterator() -> Iterator {
        return Iterator(bitSet: self)
    }

    // MARK: - Set Algebra

    public mutating func formUnion(_ other: BitSet) {
        ensureCapacity(other.capacity)
        let minWords = Swift.min(words.count, other.words.count)
        words.withUnsafeMutableBufferPointer { dst in
            other.words.withUnsafeBufferPointer { src in
                axiom_vec_or(dst.baseAddress, dst.baseAddress, src.baseAddress, minWords)
            }
        }
    }

    public mutating func formIntersection(_ other: BitSet) {
        let minWords = Swift.min(words.count, other.words.count)
        words.withUnsafeMutableBufferPointer { dst in
            other.words.withUnsafeBufferPointer { src in
                axiom_vec_and(dst.baseAddress, dst.baseAddress, src.baseAddress, minWords)
            }
        }
        if words.count > minWords {
            for i in minWords..<words.count {
                words[i] = 0
            }
        }
    }
}
