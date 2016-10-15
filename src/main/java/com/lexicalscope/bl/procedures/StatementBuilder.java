package com.lexicalscope.bl.procedures;

import static com.lexicalscope.bl.procedures.VariableName.refVariableName;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

import com.lexicalscope.bl.equiv.Expression;
import com.lexicalscope.bl.equiv.Statement;

public class StatementBuilder {
    public static class ConditionalStatementBuilder {
        private final Expression condition;
        private final StatementBuilder continuation;

        public ConditionalStatementBuilder(
                final Expression condition,
                final StatementBuilder continuation) {
            this.condition = condition;
            this.continuation = continuation;
        }

        public ConditionalStatementBuilderThen then(final StatementBuilder thenStatements) {
            return then(thenStatements.mk());
        }

        public ConditionalStatementBuilderThen then(final List<Statement> thenStatements) {
            return then(new Block(thenStatements));
        }

        public ConditionalStatementBuilderThen then(final Block thenStatements) {
            return new ConditionalStatementBuilderThen(condition, thenStatements, continuation);
        }

        public ConditionalStatementBuilderThen then() {
            return then(Collections.emptyList());
        }
    }

    public static class ConditionalStatementBuilderThen {
        private final Expression condition;
        private final Block thenStatements;
        private final StatementBuilder continuation;

        public ConditionalStatementBuilderThen(
                final Expression condition,
                final Block thenStatements,
                final StatementBuilder continuation) {
            this.condition = condition;
            this.thenStatements = thenStatements;
            this.continuation = continuation;
        }

        public StatementBuilder elsethen(final StatementBuilder elseStatements) {
            return elsethen(elseStatements.mk());
        }

        public StatementBuilder elsethen(final List<Statement> elseStatements) {
            return elsethen(new Block(elseStatements));
        }

        public StatementBuilder elsethen(final Block elseStatements) {
            continuation.seq(new ConditionalStatement(condition, thenStatements, elseStatements));
            return continuation;
        }

        public StatementBuilder elsethen() {
            return elsethen(Collections.emptyList());
        }
    }

    private final List<Statement> statements = new ArrayList<>();

    public ConditionalStatementBuilder conditional(final Expression condition) {
        return new ConditionalStatementBuilder(condition, this);
    }

    public StatementBuilder predicated(final Expression condition, final List<Statement> statement) {
        seq(new PredicatedStatement(condition, statement));
        return this;
    }

    public StatementBuilder predicated(final Expression condition, final Block statement) {
        seq(new PredicatedStatement(condition, statement));
        return this;
    }

    public StatementBuilder predicated(final Expression condition, final StatementBuilder statements) {
        assert statements.size() == 1;
        seq(new PredicatedStatement(condition, statements.mk()));
        return this;
    }

    private int size() {
        return statements.size();
    }

    public List<Statement> mk() {
        return statements;
    }

    public Statement first() {
        return statements.get(0);
    }

    public StatementBuilder conditionVariable(final String local, final Expression expression) {
        seq(new ConditionVariableStatement(local, expression));
        return this;
    }

    public StatementBuilder conditionVariable(final VariableName local, final Expression expression) {
        seq(new ConditionVariableStatement(local, expression));
        return this;
    }

    public StatementBuilder localUpdate(final VariableName local, final Expression expression) {
        seq(new LocalUpdateStatement(local, expression));
        return this;
    }

    public StatementBuilder localUpdate(final String local, final Expression expression) {
        seq(new LocalUpdateStatement(local, expression));
        return this;
    }

    public StatementBuilder heapUpdate(final String lhs, final String field, final String rhs) {
        seq(new HeapUpdateStatement(refVariableName(lhs), field, rhs));
        return this;
    }

    public StatementBuilder heapUpdate(final String lhs, final String field, final VariableName rhs) {
        seq(new HeapUpdateStatement(refVariableName(lhs), field, rhs));
        return this;
    }

    public StatementBuilder heapAllocationStatement(final String local) {
        seq(new HeapAllocStatement(local));
        return this;
    }

    public StatementBuilder heapAllocationStatement(final VariableName local) {
        seq(new HeapAllocStatement(local));
        return this;
    }

    public StatementBuilder seq(final Statement statement) {
        statements.add(statement);
        return this;
    }

    public static BoolExpression equalToExpression(final String lhsVal, final String rhsVal) {
        return new EqualToExpression(lhsVal, rhsVal);
    }

    public static BoolExpression notExpression(final Expression expression) {
        return new NotExpression(expression);
    }

    public static StatementBuilder statements() {
        return new StatementBuilder();
    }

    public static Expression localRead(final String var) {
        return new LocalReadExpression(var);
    }

    public static Expression localRead(final VariableName var) {
        return new LocalReadExpression(var);
    }

    public static Expression heapRead(final Path path) {
        return new HeapReadExpression(path);
    }

    public static Expression trueExpression() {
        return TrueExpression.trueExpression();
    }

    public static Expression falseExpression() {
        return FalseExpression.falseExpression();
    }
}
