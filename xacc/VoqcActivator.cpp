#include "cppmicroservices/BundleActivator.h"
#include "cppmicroservices/BundleContext.h"
#include "cppmicroservices/ServiceProperties.h"
#include "VoqcOptimizer.hpp"

using namespace cppmicroservices;

class US_ABI_LOCAL VOQC_Activator : public BundleActivator {
public:
  VOQC_Activator() {}

  void Start(BundleContext context) 
  {
    context.RegisterService<xacc::IRTransformation>(std::make_shared<xacc::quantum::VoqcCircuitOptimizer>());
  }

  void Stop(BundleContext context) {}
};

CPPMICROSERVICES_EXPORT_BUNDLE_ACTIVATOR(VOQC_Activator)
