package com.lexicalscope.bl.procedures;

import com.lexicalscope.bl.compiler.Visitors;
import com.lexicalscope.bl.equiv.Expression;

public class EqualToExpression extends AbstractExpression implements BoolExpression {
    private final Expression lhs;
    private final Expression rhs;

    public EqualToExpression(final String lhsVal, final String rhsVal) {
        this(LocalReadExpression.localOrConst(lhsVal), LocalReadExpression.localOrConst(rhsVal));
    }

    public EqualToExpression(final Expression lhs, final Expression rhs) {
        assert lhs != null;
        assert rhs != null;
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
        return "EqualTo";
    }

    @Override public String toString() {
        return "EqualToExpression [lhsVal=" + lhs + ", rhsVal=" + rhs + "]";
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
        final EqualToExpression other = (EqualToExpression) obj;
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

    @Override public Expression accept(final Visitors.ExpressionVisitor visitor) {
        return visitor.visitEqualTo(lhs, rhs);
    }
}
