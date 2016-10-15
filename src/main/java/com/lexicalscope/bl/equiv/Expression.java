package com.lexicalscope.bl.equiv;

import com.lexicalscope.bl.compiler.Visitors;

public interface Expression {
    String getType();
    Expression and(Expression expression);
    Expression accept(Visitors.ExpressionVisitor visitor);
    @Override int hashCode();
    @Override boolean equals(Object obj);
}
