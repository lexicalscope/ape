package com.lexicalscope.bl.procedures;

import java.util.List;

import com.lexicalscope.bl.compiler.Visitors;
import com.lexicalscope.bl.equiv.Expression;
import com.lexicalscope.bl.equiv.Statement;

public class ConditionalStatement implements Statement {
    private final Expression condition;
    private final Block thenStatements;
    private final Block elseStatements;

    public ConditionalStatement(
            final Expression condition,
            final Block thenStatements,
            final Block elseStatements) {
        this.condition = condition;
        this.thenStatements = thenStatements;
        this.elseStatements = elseStatements;
    }

    public ConditionalStatement(
            final Expression condition,
            final List<Statement> thenStatements,
            final List<Statement> elseStatements) {
        this(condition, new Block(thenStatements), new Block(elseStatements));
    }

    @Override public String getType() {
        return "Conditional";
    }

    public Expression getCondition() {
        return condition;
    }

    public Block getThenStatements() {
        return thenStatements;
    }

    public Block getElseStatements() {
        return elseStatements;
    }

    @Override public boolean isAlloc() {
        return false;
    }

    @Override public int hashCode() {
        final int prime = 31;
        int result = 1;
        result = prime * result + (condition == null ? 0 : condition.hashCode());
        result = prime * result + (elseStatements == null ? 0 : elseStatements.hashCode());
        result = prime * result + (thenStatements == null ? 0 : thenStatements.hashCode());
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
        final ConditionalStatement other = (ConditionalStatement) obj;
        if (condition == null) {
            if (other.condition != null) {
                return false;
            }
        } else if (!condition.equals(other.condition)) {
            return false;
        }
        if (elseStatements == null) {
            if (other.elseStatements != null) {
                return false;
            }
        } else if (!elseStatements.equals(other.elseStatements)) {
            return false;
        }
        if (thenStatements == null) {
            if (other.thenStatements != null) {
                return false;
            }
        } else if (!thenStatements.equals(other.thenStatements)) {
            return false;
        }
        return true;
    }

    @Override public String toString() {
        return "ConditionalStatement [condition=" + condition + ", thenStatements=" + thenStatements
                + ", elseStatements=" + elseStatements + "]";
    }

    @Override public List<Statement> accept(final Visitors.StatementVisitor visitor) {
        return visitor.visitConditional(this);
    }
}
