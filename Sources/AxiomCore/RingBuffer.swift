import Foundation

/// Fixed-capacity circular ring buffer with O(1) push, rolling sum,
/// moving average, and variance for Glucose dynamic restart heuristics.
public struct RingBuffer<Element: BinaryFloatingPoint>: Sendable where Element: Sendable {
    private var buffer: [Element]
    private var writeIndex: Int = 0
    private var currentCount: Int = 0
    private var rollingSum: Double = 0.0

    public let capacity: Int

    // MARK: - Initializer

    public init(capacity: Int) {
        precondition(capacity > 0, "RingBuffer capacity must be positive")
        self.capacity = capacity
        self.buffer = [Element](repeating: 0, count: capacity)
    }

    // MARK: - Properties

    public var count: Int {
        return currentCount
    }

    public var isFull: Bool {
        return currentCount == capacity
    }

    public var isEmpty: Bool {
        return currentCount == 0
    }

    // MARK: - Push and Query

    public mutating func push(_ value: Element) {
        let valDouble = Double(value)
        if currentCount == capacity {
            // Overwriting old element
            let oldVal = Double(buffer[writeIndex])
            rollingSum += (valDouble - oldVal)
        } else {
            rollingSum += valDouble
            currentCount += 1
        }

        buffer[writeIndex] = value
        writeIndex = (writeIndex + 1) % capacity
    }

    public var sum: Double {
        return rollingSum
    }

    public var average: Double {
        guard currentCount > 0 else { return 0.0 }
        return rollingSum / Double(currentCount)
    }

    public var variance: Double {
        guard currentCount > 1 else { return 0.0 }
        let mean = average
        var sumSquares: Double = 0.0
        for i in 0..<currentCount {
            let diff = Double(buffer[i]) - mean
            sumSquares += diff * diff
        }
        return sumSquares / Double(currentCount - 1)
    }

    public mutating func clear() {
        writeIndex = 0
        currentCount = 0
        rollingSum = 0.0
    }
}
