package com.lexicalscope.bl.procedures;

import static com.lexicalscope.bl.procedures.VariableName.refVariableName;

import java.util.List;

import com.lexicalscope.bl.compiler.Visitors;
import com.lexicalscope.bl.equiv.Statement;

public class HeapUpdateStatement implements Statement {
    private final VariableName lhs;
    private final VariableName rhs;
    private final String field;

    public HeapUpdateStatement(final String lhs, final String field, final String rhsVar) {
        this(refVariableName(lhs), field, refVariableName(rhsVar));
    }

    public HeapUpdateStatement(final VariableName lhs, final String field, final String rhsVar) {
        this(lhs, field, refVariableName(rhsVar));
    }

    public HeapUpdateStatement(final String lhs, final String field, final VariableName rhs) {
        this(refVariableName(lhs), field, rhs);
    }

    public HeapUpdateStatement(final VariableName lhs, final String field, final VariableName rhs) {
        this.lhs = lhs;
        this.field = field;
        this.rhs = rhs;
    }

    public VariableName getLhs() {
        return lhs;
    }

    public VariableName getRhs() {
        return rhs;
    }

    public String getField() {
        return field;
    }

    @Override public String getType() {
        return "HeapUpdate";
    }

    @Override public boolean isAlloc() {
        return false;
    }

    @Override public List<Statement> accept(final Visitors.StatementVisitor visitor) {
        return visitor.visitHeapUpdate(this);
    }

    @Override public int hashCode() {
        final int prime = 31;
        int result = 1;
        result = prime * result + (lhs == null ? 0 : lhs.hashCode());
        result = prime * result + (rhs == null ? 0 : rhs.hashCode());
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
        final HeapUpdateStatement other = (HeapUpdateStatement) obj;
        if (lhs == null) {
            if (other.lhs != null) {
                return false;
            }
        } else if (!lhs.equals(other.lhs)) {
            return false;
        }
        if (rhs == null) {
            if (other.rhs != null) {
                return false;
            }
        } else if (!rhs.equals(other.rhs)) {
            return false;
        }
        return true;
    }

    @Override public String toString() {
        return "HeapUpdateStatement [lhs=" + lhs + ", field=" + field + ", rhs=" + rhs + "]";
    }

}
