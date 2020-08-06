#include "voqc.h"
#include "VoqcOptimizer.hpp"
namespace xacc {
namespace quantum {
void VoqcCircuitOptimizer::apply(std::shared_ptr<CompositeInstruction> program, const std::shared_ptr<Accelerator> accelerator, const HeterogeneousMap& options) 
{
  std::cout << "Hello apply \n";
  // TODO:
  // Steps:
  // (1) Use Staq to translate the program to OpenQASM
  // (2) Write OpenQASM to temp file
  // (3) Use voqc(in_file, out_file) to optimize the OpenQASM circuit.
  // (4) Use Staq to re-compile the output file.
  // (5) Clean-up the temporary files.
}
}}