import Foundation

/// Fast monotonic bump-pointer arena allocator for AST nodes and solver working memory.
/// Allocates large contiguous memory blocks and resets in O(1) time without fragmentation.
public final class ArenaAllocator: @unchecked Sendable {
    public static let defaultChunkSize: Int = 1024 * 1024 // 1 MB chunk size

    private final class Chunk {
        let memory: UnsafeMutableRawPointer
        let capacity: Int
        var offset: Int
        var next: Chunk?

        init(capacity: Int) {
            self.capacity = capacity
            self.memory = UnsafeMutableRawPointer.allocate(byteCount: capacity, alignment: 16)
            self.offset = 0
            self.next = nil
        }

        deinit {
            memory.deallocate()
        }

        func allocate(byteCount: Int, alignment: Int) -> UnsafeMutableRawPointer? {
            // Align current offset
            let remainder = offset % alignment
            let alignedOffset = remainder == 0 ? offset : offset + (alignment - remainder)
            if alignedOffset + byteCount <= capacity {
                offset = alignedOffset + byteCount
                return memory.advanced(by: alignedOffset)
            }
            return nil
        }

        func reset() {
            offset = 0
        }
    }

    private var headChunk: Chunk
    private var currentChunk: Chunk
    private let chunkSize: Int
    private var totalAllocatedBytes: Int = 0

    public init(chunkSize: Int = ArenaAllocator.defaultChunkSize) {
        self.chunkSize = chunkSize
        let initial = Chunk(capacity: chunkSize)
        self.headChunk = initial
        self.currentChunk = initial
    }

    /// Allocate raw bytes with the specified alignment
    public func allocate(byteCount: Int, alignment: Int = 8) -> UnsafeMutableRawPointer {
        precondition(byteCount > 0, "Byte count must be positive")
        totalAllocatedBytes += byteCount

        if let ptr = currentChunk.allocate(byteCount: byteCount, alignment: alignment) {
            return ptr
        }

        // Current chunk is full; allocate new chunk
        let nextChunkSize = max(chunkSize, byteCount * 2)
        let newChunk = Chunk(capacity: nextChunkSize)
        currentChunk.next = newChunk
        currentChunk = newChunk

        guard let ptr = currentChunk.allocate(byteCount: byteCount, alignment: alignment) else {
            fatalError("Failed to allocate in fresh arena chunk")
        }
        return ptr
    }

    /// Allocate and initialize a typed instance
    public func create<T>(_ value: T) -> UnsafeMutablePointer<T> {
        let rawPtr = allocate(byteCount: MemoryLayout<T>.size, alignment: MemoryLayout<T>.alignment)
        let typedPtr = rawPtr.bindMemory(to: T.self, capacity: 1)
        typedPtr.initialize(to: value)
        return typedPtr
    }

    /// Fast O(1) reset of all allocations in the arena
    public func reset() {
        var chunk: Chunk? = headChunk
        while let c = chunk {
            c.reset()
            chunk = c.next
        }
        currentChunk = headChunk
        totalAllocatedBytes = 0
    }

    public var bytesAllocated: Int {
        return totalAllocatedBytes
    }
}
