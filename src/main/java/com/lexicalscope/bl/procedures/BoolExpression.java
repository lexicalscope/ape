package com.lexicalscope.bl.procedures;

import com.lexicalscope.bl.equiv.Expression;

public interface BoolExpression extends Expression {
    @Override
    String getType();
    @Override int hashCode();
    @Override boolean equals(Object obj);
}
