#include "VoqcOptimizer.hpp"
#include "xacc.hpp"
#include "InstructionIterator.hpp"
#include <cstdio>
#include <filesystem>

// VOQC entry-point
extern "C" {
void voqc(const char* in_file, const char* out_file);
}

namespace {
std::string convertRzGate(const std::string& in_src)
{
  auto str = in_src;
  auto start_pos = str.find("rz(", 0);
  
  while (start_pos != std::string::npos) 
  {
    const auto start_angle = str.find("(", start_pos);
    const auto stop_angle =  str.find(")", start_pos);
    const auto originalLength = stop_angle - start_angle - 1;
    const double angle = std::stod(str.substr(start_angle + 1, originalLength));  
    const double normalizedAngle = angle / M_PI;
    const std::string newThetaStr = std::to_string(normalizedAngle) + "*pi";
    str.replace(start_angle + 1, originalLength, newThetaStr);
    start_pos = str.find("rz(", stop_angle);
  }
  return str;
}

std::string convertRzqGate(const std::string& in_src)
{
  auto str = in_src;
  auto start_pos = str.find("rzq(", 0);
  
  while (start_pos != std::string::npos) 
  {
    const auto start_angle = str.find("(", start_pos);
    const auto stop_angle =  str.find(")", start_pos);
    const auto originalLength = stop_angle - start_angle - 1;
    const auto pairStr = str.substr(start_angle + 1, originalLength);  
    const auto delim_pos = pairStr.find(",", 0);
    const auto num = static_cast<double>(std::stoi(pairStr.substr(0, delim_pos)));
    const auto den = static_cast<double>(std::stoi(pairStr.substr(delim_pos + 1)));
    const double angle = (num / den) * M_PI;
    const std::string angleStr = std::to_string(angle);
    str.replace(start_pos + 2, originalLength + 2, "(" + angleStr);
    start_pos = str.find("rzq(", stop_angle);
  }
  return str;
}

const std::vector<std::string> SUPPORTED_GATES = {
  "T", "Tdg",
  "S", "Sdg",
  "Z", "Rz",
  "H", "X", "CNOT"
};

bool allGatesSupported(std::shared_ptr<xacc::CompositeInstruction> program)
{
  xacc::InstructionIterator it(program);
  while (it.hasNext())
  {
    auto nextInst = it.next();
    if (nextInst->isEnabled() && !nextInst->isComposite())
    {
      if (!xacc::container::contains(SUPPORTED_GATES, nextInst->name()))
      {
        return false;
      }
    }
  }
  return true;
}
}

namespace xacc {
namespace quantum {
void VoqcCircuitOptimizer::apply(std::shared_ptr<CompositeInstruction> program, const std::shared_ptr<Accelerator> accelerator, const HeterogeneousMap& options) 
{
  if(!allGatesSupported(program))
  {
    return;
  }

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
  inFile << convertRzGate(src);
  inFile.close();

  // (3) Use voqc(in_file, out_file) to optimize the OpenQASM circuit.
  voqc(in_fName.c_str(), out_fName.c_str());
  std::ifstream outFile(out_fName);
  std::string optSrc((std::istreambuf_iterator<char>(outFile)), std::istreambuf_iterator<char>());
  
  // (4) Use Staq to re-compile the output file.
  auto ir = staq->compile(convertRzqGate(optSrc));
  // reset the program and add optimized instructions
  program->clear();
  program->addInstructions(ir->getComposites()[0]->getInstructions());
  
  // (5) Clean-up the temporary files.
  remove(in_fName.c_str());
  remove(out_fName.c_str());    
}
}}