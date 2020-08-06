#include <gtest/gtest.h>
#include "xacc.hpp"
#include "xacc_service.hpp"
#include "IRTransformation.hpp"

TEST(VOQCTester, checkSimple) 
{
}

int main(int argc, char **argv) 
{
  xacc::Initialize(argc, argv);
  ::testing::InitGoogleTest(&argc, argv);
  auto ret = RUN_ALL_TESTS();
  xacc::Finalize();
  return ret;
}