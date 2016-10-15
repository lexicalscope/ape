package com.lexicalscope.bl.procedures;

import com.lexicalscope.bl.compiler.Visitors;
import com.lexicalscope.bl.equiv.Expression;

public class NullValueExpression extends AbstractExpression implements Expression {
    private NullValueExpression() { }

    @Override public String getType() {
        return "NullValue";
    }

    @Override public Expression and(final Expression expression) {
        throw new IllegalStateException();
    }

    @Override public boolean equals(final Object obj) {
        return obj != null && obj.getClass().equals(getClass());
    }

    @Override public int hashCode() {
        return getClass().hashCode();
    }

    @Override public String toString() {
        return "NullValueExpression []";
    }

    @Override public Expression accept(final Visitors.ExpressionVisitor visitor) {
        return visitor.nullValue(this);
    }

    public static Expression nullValueExpression() {
        return new NullValueExpression();
    }
}
