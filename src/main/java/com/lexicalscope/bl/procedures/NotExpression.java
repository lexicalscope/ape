package com.lexicalscope.bl.procedures;

import com.lexicalscope.bl.compiler.Visitors;
import com.lexicalscope.bl.equiv.Expression;

public class NotExpression extends AbstractExpression implements BoolExpression {
    private final Expression expression;

    public NotExpression(final Expression expression) {
        this.expression = expression;
    }

    @Override public String getType() {
        return "Not";
    }

    @Override public int hashCode() {
        final int prime = 31;
        int result = 1;
        result = prime * result + (expression == null ? 0 : expression.hashCode());
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
        final NotExpression other = (NotExpression) obj;
        if (expression == null) {
            if (other.expression != null) {
                return false;
            }
        } else if (!expression.equals(other.expression)) {
            return false;
        }
        return true;
    }

    @Override public String toString() {
        return "NotExpression [expression=" + expression + "]";
    }

    public Expression getExpression() {
        return expression;
    }

    @Override public Expression accept(final Visitors.ExpressionVisitor visitor) {
        return visitor.not(expression);
    }
}
