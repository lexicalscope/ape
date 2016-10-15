package com.lexicalscope.bl.procedures;

import com.lexicalscope.bl.compiler.Visitors;
import com.lexicalscope.bl.equiv.Expression;

public class AndExpression  extends AbstractExpression implements Expression {
    private final Expression lhs;
    private final Expression rhs;

    public AndExpression(final Expression lhs, final Expression rhs) {
        this.lhs = lhs;
        this.rhs = rhs;
    }

    public Expression getLhs() {
        return lhs;
    }

    public Expression getRhs() {
        return rhs;
    }

    @Override public String getType() {
        return "And";
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
        final AndExpression other = (AndExpression) obj;
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
        return "AndExpression [lhs=" + lhs + ", rhs=" + rhs + "]";
    }

    @Override public Expression accept(final Visitors.ExpressionVisitor visitor) {
        return visitor.visitAnd(lhs, rhs);
    }
}
