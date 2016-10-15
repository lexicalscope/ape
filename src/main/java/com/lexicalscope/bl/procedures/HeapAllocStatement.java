package com.lexicalscope.bl.procedures;

import static com.lexicalscope.bl.procedures.VariableName.refVariableName;

import java.util.List;

import com.lexicalscope.bl.compiler.Visitors;
import com.lexicalscope.bl.equiv.Statement;


public class HeapAllocStatement implements Statement, LocalAssignment {
    private final VariableName lhsVar;

    public HeapAllocStatement(final VariableName lhsVar) {
        this.lhsVar = lhsVar;
    }

    public HeapAllocStatement(final String lhsVar) {
        this(refVariableName(lhsVar));
    }

    @Override public List<Statement> accept(final Visitors.StatementVisitor visitor) {
        return visitor.visitHeapAlloc(this);
    }

    @Override public VariableName getLhsVar() {
        return lhsVar;
    }

    @Override public String getType() {
        return "HeapAlloc";
    }

    @Override public boolean isAlloc() {
        return true;
    }

    @Override public int hashCode() {
        final int prime = 31;
        int result = 1;
        result = prime * result + (lhsVar == null ? 0 : lhsVar.hashCode());
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
        final HeapAllocStatement other = (HeapAllocStatement) obj;
        if (lhsVar == null) {
            if (other.lhsVar != null) {
                return false;
            }
        } else if (!lhsVar.equals(other.lhsVar)) {
            return false;
        }
        return true;
    }

    @Override public String toString() {
        return "HeapAllocStatement [lhsVar=" + lhsVar + "]";
    }
}
