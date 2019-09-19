import Foundation

/// High-performance indexed binary heap priority queue supporting O(1) key lookup,
/// O(log n) priority updates, and O(log n) min/max extraction for SAT VSIDS heuristics.
public struct IndexedPriorityQueue<Element: Hashable, Priority: Comparable>: Sendable where Priority: Sendable, Element: Sendable {
    public struct Entry: Sendable {
        public let element: Element
        public var priority: Priority
    }

    private var heap: [Entry]
    private var indexMap: [Element: Int]
    private let isHigherPriority: @Sendable (Priority, Priority) -> Bool

    // MARK: - Initializer

    public init(comparator: @escaping @Sendable (Priority, Priority) -> Bool) {
        self.heap = []
        self.indexMap = [:]
        self.isHigherPriority = comparator
    }

    public static func maxHeap() -> IndexedPriorityQueue<Element, Priority> {
        return IndexedPriorityQueue { $0 > $1 }
    }

    public static func minHeap() -> IndexedPriorityQueue<Element, Priority> {
        return IndexedPriorityQueue { $0 < $1 }
    }

    // MARK: - Properties

    public var count: Int {
        return heap.count
    }

    public var isEmpty: Bool {
        return heap.isEmpty
    }

    public func contains(_ element: Element) -> Bool {
        return indexMap[element] != nil
    }

    public func priority(of element: Element) -> Priority? {
        guard let idx = indexMap[element] else { return nil }
        return heap[idx].priority
    }

    public func peek() -> (element: Element, priority: Priority)? {
        guard let first = heap.first else { return nil }
        return (first.element, first.priority)
    }

    // MARK: - Insert and Update

    public mutating func insert(element: Element, priority: Priority) {
        if let idx = indexMap[element] {
            update(element: element, newPriority: priority, at: idx)
            return
        }
        let idx = heap.count
        heap.append(Entry(element: element, priority: priority))
        indexMap[element] = idx
        siftUp(idx)
    }

    public mutating func updatePriority(element: Element, newPriority: Priority) {
        guard let idx = indexMap[element] else {
            insert(element: element, priority: newPriority)
            return
        }
        update(element: element, newPriority: newPriority, at: idx)
    }

    private mutating func update(element: Element, newPriority: Priority, at idx: Int) {
        let oldPriority = heap[idx].priority
        heap[idx].priority = newPriority
        if isHigherPriority(newPriority, oldPriority) {
            siftUp(idx)
        } else {
            siftDown(idx)
        }
    }

    // MARK: - Pop and Remove

    @discardableResult
    public mutating func pop() -> (element: Element, priority: Priority)? {
        guard !heap.isEmpty else { return nil }
        if heap.count == 1 {
            let last = heap.removeLast()
            indexMap.removeValue(forKey: last.element)
            return (last.element, last.priority)
        }

        let root = heap[0]
        let last = heap.removeLast()
        indexMap.removeValue(forKey: root.element)

        if !heap.isEmpty {
            heap[0] = last
            indexMap[last.element] = 0
            siftDown(0)
        }
        return (root.element, root.priority)
    }

    @discardableResult
    public mutating func remove(_ element: Element) -> Priority? {
        guard let idx = indexMap[element] else { return nil }
        let prio = heap[idx].priority
        let lastIdx = heap.count - 1

        if idx == lastIdx {
            heap.removeLast()
            indexMap.removeValue(forKey: element)
            return prio
        }

        swapAt(idx, lastIdx)
        heap.removeLast()
        indexMap.removeValue(forKey: element)

        siftUp(idx)
        siftDown(idx)
        return prio
    }

    public mutating func clear() {
        heap.removeAll(keepingCapacity: true)
        indexMap.removeAll(keepingCapacity: true)
    }

    // MARK: - Heap Maintenance

    private mutating func siftUp(_ index: Int) {
        var child = index
        while child > 0 {
            let parent = (child - 1) / 2
            if isHigherPriority(heap[child].priority, heap[parent].priority) {
                swapAt(child, parent)
                child = parent
            } else {
                break
            }
        }
    }

    private mutating func siftDown(_ index: Int) {
        var parent = index
        let count = heap.count

        while true {
            let left = 2 * parent + 1
            let right = left + 1
            var best = parent

            if left < count && isHigherPriority(heap[left].priority, heap[best].priority) {
                best = left
            }
            if right < count && isHigherPriority(heap[right].priority, heap[best].priority) {
                best = right
            }

            if best != parent {
                swapAt(parent, best)
                parent = best
            } else {
                break
            }
        }
    }

    private mutating func swapAt(_ i: Int, _ j: Int) {
        heap.swapAt(i, j)
        indexMap[heap[i].element] = i
        indexMap[heap[j].element] = j
    }
}
