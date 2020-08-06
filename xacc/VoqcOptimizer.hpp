#pragma once

namespace xacc {
namespace quantum {
class VoqcCircuitOptimizer : public IRTransformation, public OptionsProvider {

public:
  VoqcCircuitOptimizer() {}
  void apply(std::shared_ptr<CompositeInstruction> program,
                     const std::shared_ptr<Accelerator> accelerator,
                     const HeterogeneousMap& options = {}) override {};
  const IRTransformationType type() const override {return IRTransformationType::Optimization;}

  const std::string name() const override { return "voqc"; }
  const std::string description() const override { return ""; }
};
} // namespace quantum
} // namespace xacc
