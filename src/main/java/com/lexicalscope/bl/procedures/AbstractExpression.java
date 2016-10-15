package com.lexicalscope.bl.procedures;

import com.lexicalscope.bl.equiv.Expression;

public abstract class AbstractExpression implements Expression {
    @Override public Expression and(final Expression expression) {
        return new AndExpression(this, expression);
    }
}
