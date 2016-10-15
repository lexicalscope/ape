package com.lexicalscope.bl.procedures;

import com.lexicalscope.bl.equiv.Expression;

public interface ExpressionVisitor<T> {
    T visitAnd(Expression lhs, Expression rhs);
    T visitEqualTo(Expression lhs, Expression rhs);
    T visitHeapRead(HeapReadExpression heapReadExpression);
    T visitLocalRead(VariableName local);
    T notEqualTo(Expression lhs, Expression rhs);
    T not(Expression expression);
    T nullValue(NullValueExpression nullValueExpression);
    T trueValue(TrueExpression trueExpression);
}
