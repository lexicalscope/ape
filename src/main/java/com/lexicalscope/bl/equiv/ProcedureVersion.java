package com.lexicalscope.bl.equiv;

import com.lexicalscope.bl.procedures.Procedure;

public class ProcedureVersion {
    private final String version;
    private final Procedure procedure;

    public ProcedureVersion(final String version, final Procedure procedure) {
        this.version = version;
        this.procedure = procedure;
    }

    public String getVersion() {
        return version;
    }

    public Procedure getProcedure() {
        return procedure;
    }

    @Override public String toString() {
        return "_"+version;
    }
}
