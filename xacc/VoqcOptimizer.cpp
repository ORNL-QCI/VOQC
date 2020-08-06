#include "VoqcOptimizer.hpp"
#include "xacc.hpp"
#include <cstdio>
#include <filesystem>

// VOQC entry-point
extern "C" {
void voqc(const char* in_file, const char* out_file);
}

namespace xacc {
namespace quantum {
void VoqcCircuitOptimizer::apply(std::shared_ptr<CompositeInstruction> program, const std::shared_ptr<Accelerator> accelerator, const HeterogeneousMap& options) 
{
  // (1) Use Staq to translate the program to OpenQASM
  auto staq = xacc::getCompiler("staq");
  const auto src = staq->translate(program);
  
  // (2) Write OpenQASM to temp file
  char inTemplate[] = "/tmp/inQasmFileXXXXXX";
  mkstemp(inTemplate);
  char outTemplate[] = "/tmp/outQasmFileXXXXXX";
  mkstemp(outTemplate);

  const std::string in_fName(inTemplate);
  const std::string out_fName(outTemplate);

  std::ofstream inFile(in_fName);
  inFile << src;
  inFile.close();

  // (3) Use voqc(in_file, out_file) to optimize the OpenQASM circuit.
  voqc(in_fName.c_str(), out_fName.c_str());
  std::ifstream outFile(out_fName);
  std::string optSrc((std::istreambuf_iterator<char>(outFile)), std::istreambuf_iterator<char>());

  // (4) Use Staq to re-compile the output file.
  auto ir = staq->compile(optSrc);
  // reset the program and add optimized instructions
  program->clear();
  program->addInstructions(ir->getComposites()[0]->getInstructions());
  
  // (5) Clean-up the temporary files.
  remove(in_fName.c_str());
  remove(out_fName.c_str());    
}
}}