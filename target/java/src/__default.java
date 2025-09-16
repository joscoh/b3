package Z3SmtSolver;

public class __default {
    public static Smt.SmtProcess CreateZ3Process() {
        return new Z3SmtProcess();
    }
    public static Smt.SmtProcess CreateCVC5Process() {
        return new CVC5SmtProcess();
    }
}
