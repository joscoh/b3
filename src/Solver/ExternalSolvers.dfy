module ExternalSolvers {
  import opened Basics
  import Smt
  import Z3SmtSolver
  import CVC5SmtSolver

  export
    reveals ExternalSolver
    provides Create
    provides Smt, Basics

  datatype ExternalSolver = Z3 | CVC5

  method Create(which: ExternalSolver, printLog: bool) returns (smtEngine: Smt.SolverEngine)
    ensures !smtEngine.Disposed()
    ensures smtEngine.CommandStacks() == Cons(Nil, Nil)
    ensures fresh(smtEngine) && fresh(smtEngine.process)
  {
    var process;
    match which {
      case Z3 => process := Z3SmtSolver.CreateZ3Process();
      case CVC5 => process := CVC5SmtSolver.CreateCVC5Process();
    }
    smtEngine := new Smt.SolverEngine(process, printLog);
  }

  @Test
  method DemonstrateExternalSolvers() {
    var z3 := Create(ExternalSolver.Z3, false);
    Demonstrate(z3);
    var cvc5 := Create(ExternalSolver.CVC5, false);
    Demonstrate(cvc5);
  }

  method Demonstrate(smtEngine: Smt.SolverEngine)
    requires !smtEngine.Disposed()
    requires smtEngine.CommandStacks() == Cons(Nil, Nil)
    modifies smtEngine, smtEngine.process
  {
    smtEngine.DeclareFunction("x", "()", "Int");

    smtEngine.Push();
    
    // Example: Check if x > y and y > x is satisfiable
    smtEngine.DeclareFunction("y", "()", "Int");

    // Assert x > y
    smtEngine.Assume("(> x y)");
    
    // Assert y > x
    smtEngine.Assume("(> y x)");
    
    // Check satisfiability
    var result := smtEngine.CheckSat();
    
    // Print result (should be "unsat")
    print "Checking if x > y and y > x is satisfiable: ", result, "\n";
    expect result == "unsat";
    
    // Pop back to clean state
    smtEngine.Pop();
    
    // Example: Check if x >= 0 and x <= 10 is satisfiable
    smtEngine.Push();
    
    // Assert x >= 0
    smtEngine.Assume("(>= x 0)");
    
    // Assert x <= 10
    smtEngine.Assume("(<= x 10)");
    
    // Check satisfiability
    result := smtEngine.CheckSat();
    
    // Print result (should be "sat")
    print "Checking if x >= 0 and x <= 10 is satisfiable: ", result, "\n";
    expect result == "sat";
    
    // If satisfiable, get a model
    var model := smtEngine.GetModel();
    print "Model: ", model, "\n";
    
    // Pop back to clean state
    smtEngine.Pop();
    
    // Clean up
    smtEngine.Dispose();
  }
}

module Z3SmtSolver {
  import Smt

  // Factory method to create a Z3 solver instance
  @Axiom
  method {:extern} CreateZ3Process() returns (process: Smt.SmtProcess)
    ensures !process.Disposed()
    ensures fresh(process)
}

module CVC5SmtSolver {
  import Smt

  // Factory method to create a CVC5 solver instance
  @Axiom
  method {:extern} CreateCVC5Process() returns (process: Smt.SmtProcess)
    ensures !process.Disposed()
    ensures fresh(process)
}
