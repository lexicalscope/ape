package com.lexicalscope.bl.procedures;

import static com.lexicalscope.bl.procedures.VariableName.refVariableName;

import java.util.List;

import com.lexicalscope.bl.compiler.Visitors;
import com.lexicalscope.bl.equiv.Expression;
import com.lexicalscope.bl.equiv.Statement;

public class LocalUpdateStatement implements Statement, LocalAssignment {
    private final VariableName lhsVar;
    private final Expression expression;

    public LocalUpdateStatement(final VariableName lhsVar, final String rhsVar) {
        this(lhsVar, new LocalReadExpression(rhsVar));
    }

    public LocalUpdateStatement(final String lhsVar, final String rhsVar) {
        this(refVariableName(lhsVar), rhsVar);
    }

    public LocalUpdateStatement(final String lhsVar, final Expression rhsVar) {
        this(refVariableName(lhsVar), rhsVar);
    }

    public LocalUpdateStatement(final VariableName lhsVar, final Expression rhsVar) {
        this.lhsVar = lhsVar;
        this.expression = rhsVar;
    }

    @Override public List<Statement> accept(final Visitors.StatementVisitor visitor) {
        return visitor.visitLocalUpdate(this);
    }

    @Override public VariableName getLhsVar() {
        return lhsVar;
    }

    public Expression getExpression() {
        return expression;
    }

    @Override public String getType() {
        return "LocalUpdate";
    }

    @Override public boolean isAlloc() {
        return false;
    }

    @Override public int hashCode() {
        final int prime = 31;
        int result = 1;
        result = prime * result + (expression == null ? 0 : expression.hashCode());
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
        final LocalUpdateStatement other = (LocalUpdateStatement) obj;
        if (expression == null) {
            if (other.expression != null) {
                return false;
            }
        } else if (!expression.equals(other.expression)) {
            return false;
        }
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
        return "LocalUpdateStatement [lhsVar=" + lhsVar + ", expression=" + expression + "]";
    }
}
