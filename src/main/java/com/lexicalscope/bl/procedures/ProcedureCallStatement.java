package com.lexicalscope.bl.procedures;

import static com.lexicalscope.bl.procedures.VariableName.asVariableNames;

import java.util.List;

import com.lexicalscope.Jc;
import com.lexicalscope.bl.compiler.Visitors;
import com.lexicalscope.bl.equiv.Statement;
import com.lexicalscope.bl.parser.BlParser.ParamsContext;
import com.lexicalscope.bl.parser.BlParser.ProcedureCallContext;

public class ProcedureCallStatement implements Statement {
    private final String name;
    private final List<VariableName> params;

    public ProcedureCallStatement(final ProcedureCallContext u) {
        this(u.id.getText(), params(u.params()));
    }

    private static List<VariableName> params(final ParamsContext params) {
        return Jc.$(params.vars).map(p -> VariableName.variableName(p.IDENTIFIER().getText(), Type.Ref))._$();
    }

    public ProcedureCallStatement(final String name, final String ... params) {
        this(name, asVariableNames(params));
    }

    public ProcedureCallStatement(final String name, final List<VariableName> params) {
        this.name = name;
        this.params = params;
    }

    @Override public List<Statement> accept(final Visitors.StatementVisitor visitor) {
        return visitor.visitProcedureCall(this);
    }

    public String getName() {
        return name;
    }

    public List<VariableName> getParams() {
        return params;
    }

    @Override public String getType() {
        return "ProcedureCall";
    }

    @Override public boolean isAlloc() {
        return false;
    }

    @Override public int hashCode() {
        final int prime = 31;
        int result = 1;
        result = prime * result + (name == null ? 0 : name.hashCode());
        result = prime * result + (params == null ? 0 : params.hashCode());
        return result;
    }

    @Override public boolean equals(final Object obj) {
        if (this == obj) {
            return true;
        }
        if (obj == null) {
            return false;
        }
        if (getClass() != obj.getClass()) {
            return false;
        }
        final ProcedureCallStatement other = (ProcedureCallStatement) obj;
        if (name == null) {
            if (other.name != null) {
                return false;
            }
        } else if (!name.equals(other.name)) {
            return false;
        }
        if (params == null) {
            if (other.params != null) {
                return false;
            }
        } else if (!params.equals(other.params)) {
            return false;
        }
        return true;
    }

    @Override public String toString() {
        return "ProcedureCallStatement [name=" + name + ", params=" + params + "]";
    }
}
