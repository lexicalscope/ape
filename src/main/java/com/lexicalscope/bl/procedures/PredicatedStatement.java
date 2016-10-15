package com.lexicalscope.bl.procedures;

import java.util.List;

import com.lexicalscope.bl.compiler.Visitors;
import com.lexicalscope.bl.equiv.Expression;
import com.lexicalscope.bl.equiv.Statement;

public class PredicatedStatement implements Statement {
    private final Expression condition;
    private final Block statement;

    public PredicatedStatement(
            final Expression condition,
            final List<Statement> statement) {
        this(condition, new Block(statement));
    }

    public PredicatedStatement(final Expression condition, final Block block) {
        this.condition = condition;
        statement = block;
    }

    @Override public String getType() {
        return "Predicated";
    }

    public Expression getCondition() {
        return condition;
    }

    public Block getPredicatedStatement() {
        return statement;
    }

    @Override public boolean isAlloc() {
        return false;
    }

    @Override public List<Statement> accept(final Visitors.StatementVisitor visitor) {
        return visitor.visitPredicated(this);
    }

    @Override public int hashCode() {
        final int prime = 31;
        int result = 1;
        result = prime * result + (condition == null ? 0 : condition.hashCode());
        result = prime * result + (statement == null ? 0 : statement.hashCode());
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
        final PredicatedStatement other = (PredicatedStatement) obj;
        if (condition == null) {
            if (other.condition != null) {
                return false;
            }
        } else if (!condition.equals(other.condition)) {
            return false;
        }
        if (statement == null) {
            if (other.statement != null) {
                return false;
            }
        } else if (!statement.equals(other.statement)) {
            return false;
        }
        return true;
    }

    @Override public String toString() {
        return "PredicatedStatement [condition=" + condition + ", statement=" + statement + "]";
    }
}
