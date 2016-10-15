package com.lexicalscope.bl.equiv;

import static com.lexicalscope.bl.procedures.NullValueExpression.nullValueExpression;

import com.lexicalscope.bl.parser.BlParser.BexpressionContext;
import com.lexicalscope.bl.parser.BlParser.EqualityContext;
import com.lexicalscope.bl.parser.BlParser.ExpressionContext;
import com.lexicalscope.bl.parser.BlParser.HeapReadContext;
import com.lexicalscope.bl.parser.BlParser.InequalityContext;
import com.lexicalscope.bl.parser.BlParser.LocalReadContext;
import com.lexicalscope.bl.parser.BlParser.NullConstContext;
import com.lexicalscope.bl.procedures.BoolExpression;
import com.lexicalscope.bl.procedures.EqualToExpression;
import com.lexicalscope.bl.procedures.HeapReadExpression;
import com.lexicalscope.bl.procedures.LocalReadExpression;
import com.lexicalscope.bl.procedures.NotEqualToExpression;

public class ExpressionFactory {
    public static Expression expression(final ExpressionContext expr) {
        if (expr instanceof HeapReadContext) {
            return new HeapReadExpression((HeapReadContext) expr);
        } else if (expr instanceof LocalReadContext) {
            return new LocalReadExpression((LocalReadContext) expr);
        } else if (expr instanceof NullConstContext) {
            return nullValueExpression();
        }

        throw new IllegalStateException("unknown expression type " + expr.getClass());
    }

    public static BoolExpression boolExpression(final BexpressionContext bexpr) {
        if(bexpr instanceof EqualityContext) {
            final EqualityContext equalityCtx = (EqualityContext) bexpr;
            return new EqualToExpression(expression(equalityCtx.lhs), expression(equalityCtx.rhs));
        } else if (bexpr instanceof InequalityContext) {
            final InequalityContext inequalityCtx = (InequalityContext) bexpr;
            return new NotEqualToExpression(expression(inequalityCtx.lhs), expression(inequalityCtx.rhs));
        }
        throw new IllegalStateException("unknown expression type " + bexpr);
    }
}
