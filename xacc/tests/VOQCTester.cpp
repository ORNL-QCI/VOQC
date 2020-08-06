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
    
    EXPECT_EQ(2, program->nInstructions());
    EXPECT_EQ("T", program->getInstruction(0)->name());
    EXPECT_EQ("T", program->getInstruction(1)->name());

    irt->apply(program, nullptr);

    EXPECT_EQ(1, program->nInstructions());
    EXPECT_EQ("S", program->getInstruction(0)->name());


    program = compiler->compile(R"(__qpu__ void test_t_tdg(qreg q) {
        T(q[0]);
        Tdg(q[0]);
    })")->getComposite("test_t_tdg");

    EXPECT_EQ(2, program->nInstructions());
    EXPECT_EQ("T", program->getInstruction(0)->name());
    EXPECT_EQ("Tdg", program->getInstruction(1)->name());

    irt->apply(program, nullptr);

    EXPECT_EQ(0, program->nInstructions());

    program = compiler->compile(R"(__qpu__ void test_conj_merge(qreg q) {
        H(q[0]);
        T(q[0]);
        H(q[0]);
        X(q[0]);
        H(q[0]);
        T(q[0]);
        H(q[0]);
    })")->getComposite("test_conj_merge");

    irt->apply(program, nullptr);
    std::cout << "HOWDY:\n" << program->toString() << "\n"; 
    EXPECT_EQ(3, program->nInstructions());

    program = compiler->compile(R"(__qpu__ void test_cx_merge(qreg q) {
      CX(q[0],q[1]);
      T(q[1]);
      CX(q[0], q[1]);
      CX(q[1], q[0]);
      T(q[0]);
      CX(q[1],q[0]);
    })")->getComposite("test_cx_merge");
    irt->apply(program, nullptr);
    std::cout << "HOWDY:\n" << program->toString() << "\n"; 

    EXPECT_EQ(3, program->nInstructions());
    EXPECT_EQ("CNOT", program->getInstruction(0)->name());
    EXPECT_EQ("S", program->getInstruction(1)->name());
    EXPECT_EQ("CNOT", program->getInstruction(2)->name());
}

int main(int argc, char **argv) 
{
  xacc::Initialize(argc, argv);
  ::testing::InitGoogleTest(&argc, argv);
  auto ret = RUN_ALL_TESTS();
  xacc::Finalize();
  return ret;
}