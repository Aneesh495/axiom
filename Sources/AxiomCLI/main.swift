// Main entrypoint for Axiom CLI
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
        print("Axiom SMT Verification Engine v\(AxiomCoreModule.version)")
    }
}
