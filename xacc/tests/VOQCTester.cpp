#include <gtest/gtest.h>
#include "xacc.hpp"
#include "xacc_service.hpp"
#include "IRTransformation.hpp"

TEST(VOQCTester, checkSimple) 
{
    auto irt = xacc::getIRTransformation("voqc");
    auto compiler = xacc::getCompiler("xasm");
    auto program = compiler->compile(R"(__qpu__ void test_t_t(qreg q) {
      T(q[0]);
      T(q[0]);
    })")->getComposite("test_t_t");
    std::cout << "HOWDY: \n" << program->toString() << "\n";
    irt->apply(program, nullptr);
    std::cout << "HOWDY: \n" << program->toString() << "\n";
}

int main(int argc, char **argv) 
{
  xacc::Initialize(argc, argv);
  ::testing::InitGoogleTest(&argc, argv);
  auto ret = RUN_ALL_TESTS();
  xacc::Finalize();
  return ret;
}