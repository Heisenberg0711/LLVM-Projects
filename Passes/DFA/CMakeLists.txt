add_llvm_library( submission_pt4 MODULE
  231DFA.h

  LivenessAnalysis.cpp
  MayPointToAnalysis.cpp
  ReachingDefinitionAnalysis.cpp
  ConstantPropAnalysis.cpp

  PLUGIN_TOOL
  opt
)
