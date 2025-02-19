// swift-tools-version: 6.0
import PackageDescription

let package = Package(
    name: "axiom",
    platforms: [
        .macOS(.v14)
    ],
    products: [
        .executable(name: "axiom", targets: ["AxiomCLI"]),
        .library(name: "AxiomCore", targets: ["AxiomCore"]),
        .library(name: "AxiomAST", targets: ["AxiomAST"]),
        .library(name: "AxiomSAT", targets: ["AxiomSAT"]),
        .library(name: "AxiomTheories", targets: ["AxiomTheories"]),
        .library(name: "AxiomSMT", targets: ["AxiomSMT"]),
        .library(name: "AxiomParser", targets: ["AxiomParser"]),
        .library(name: "AxiomVerify", targets: ["AxiomVerify"]),
        .library(name: "AxiomUI", targets: ["AxiomUI"])
    ],
    targets: [
        .target(
            name: "CAxiomKernel",
            path: "Sources/CAxiomKernel",
            publicHeadersPath: "include"
        ),
        .target(
            name: "AxiomCore",
            dependencies: ["CAxiomKernel"],
            path: "Sources/AxiomCore"
        ),
        .target(
            name: "AxiomAST",
            dependencies: ["AxiomCore"],
            path: "Sources/AxiomAST"
        ),
        .target(
            name: "AxiomSAT",
            dependencies: ["AxiomCore", "CAxiomKernel"],
            path: "Sources/AxiomSAT"
        ),
        .target(
            name: "AxiomTheories",
            dependencies: ["AxiomCore", "AxiomAST", "AxiomSAT", "CAxiomKernel"],
            path: "Sources/AxiomTheories"
        ),
        .target(
            name: "AxiomSMT",
            dependencies: ["AxiomCore", "AxiomAST", "AxiomSAT", "AxiomTheories"],
            path: "Sources/AxiomSMT"
        ),
        .target(
            name: "AxiomParser",
            dependencies: ["AxiomCore", "AxiomAST", "AxiomSMT"],
            path: "Sources/AxiomParser"
        ),
        .target(
            name: "AxiomVerify",
            dependencies: ["AxiomCore", "AxiomAST", "AxiomSMT"],
            path: "Sources/AxiomVerify"
        ),
        .target(
            name: "AxiomUI",
            dependencies: ["AxiomCore", "AxiomAST", "AxiomSAT", "AxiomTheories", "AxiomSMT", "AxiomParser", "AxiomVerify"],
            path: "Sources/AxiomUI"
        ),
        .executableTarget(
            name: "AxiomCLI",
            dependencies: [
                "AxiomCore",
                "AxiomAST",
                "AxiomSAT",
                "AxiomTheories",
                "AxiomSMT",
                "AxiomParser",
                "AxiomVerify",
                "AxiomUI"
            ],
            path: "Sources/AxiomCLI"
        ),
        .executableTarget(
            name: "AxiomTestRunner",
            dependencies: [
                "AxiomCore",
                "AxiomAST",
                "AxiomSAT",
                "AxiomTheories",
                "AxiomSMT",
                "AxiomParser",
                "AxiomVerify",
                "AxiomUI"
            ],
            path: "Sources/AxiomTestRunner"
        )
    ]
)
