package com.lexicalscope.bl.compiler;

import com.lexicalscope.bl.procedures.Multiversion;
import com.lexicalscope.bl.procedures.StatementAdaptor;

public class CloneProgram {
    public static Multiversion clone(final Multiversion programs) {
        return clonePrograms(programs, new StatementAdaptor());
    }

    public static Multiversion clonePrograms(final Multiversion programs, final StatementAdaptor programCloner) {
        return programs.accept(programCloner);
    }
}
