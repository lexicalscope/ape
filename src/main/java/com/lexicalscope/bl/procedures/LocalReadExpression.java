package com.lexicalscope.bl.procedures;

import static com.lexicalscope.bl.procedures.NullValueExpression.nullValueExpression;

import com.lexicalscope.bl.compiler.Visitors;
import com.lexicalscope.bl.equiv.Expression;
import com.lexicalscope.bl.parser.BlParser.LocalReadContext;


public final class LocalReadExpression extends AbstractExpression implements Expression {
    private final VariableName local;

    public LocalReadExpression(final VariableName var) {
        this.local = var;
    }

    public LocalReadExpression(final String var) {
        this(VariableName.refVariableName(var));
    }

    public LocalReadExpression(final LocalReadContext expr) {
        this(expr.local.getText());
    }

    public VariableName getVar() {
        return local;
    }

    @Override public String getType() {
        return "LocalRead";
    }

    @Override public int hashCode() {
        final int prime = 31;
        int result = 1;
        result = prime * result + (local == null ? 0 : local.hashCode());
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
        final LocalReadExpression other = (LocalReadExpression) obj;
        if (local == null) {
            if (other.local != null) {
                return false;
            }
        } else if (!local.equals(other.local)) {
            return false;
        }
        return true;
    }

    @Override public String toString() {
        return "LocalReadExpression [local=" + local + "]";
    }

    public static Expression localOrConst(final String val) {
        return val.equals("null") ? nullValueExpression() : new LocalReadExpression(val);
    }

    @Override public Expression accept(final Visitors.ExpressionVisitor visitor) {
        return visitor.visitLocalRead(local);
    }
}
