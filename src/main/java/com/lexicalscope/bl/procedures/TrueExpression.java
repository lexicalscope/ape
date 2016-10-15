package com.lexicalscope.bl.procedures;

import com.lexicalscope.bl.compiler.Visitors;
import com.lexicalscope.bl.equiv.Expression;

public final class TrueExpression implements Expression {
    private TrueExpression() { }

    @Override public String getType() {
        return "TrueValue";
    }

    @Override public Expression and(final Expression expression) {
        return expression;
    }

    @Override public int hashCode() {
        final int prime = 31;
        int result = 1;
        result = prime * result + (getClass() == null ? 0 : getClass().hashCode());
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
        final TrueExpression other = (TrueExpression) obj;
        if (getClass() == null) {
            if (other.getClass() != null) {
                return false;
            }
        } else if (!getClass().equals(other.getClass())) {
            return false;
        }
        return true;
    }

    @Override public String toString() {
        return "TrueExpression []";
    }

    @Override public Expression accept(final Visitors.ExpressionVisitor visitor) {
        return visitor.trueValue(this);
    }

    public static Expression trueExpression() {
        return new TrueExpression();
    }
}
