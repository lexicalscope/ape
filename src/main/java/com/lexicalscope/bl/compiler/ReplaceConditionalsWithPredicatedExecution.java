package com.lexicalscope.bl.compiler;

import static com.lexicalscope.bl.compiler.CloneProgram.clonePrograms;
import static com.lexicalscope.bl.compiler.VariableNameGenerator.variableNameGenerator;
import static com.lexicalscope.bl.procedures.StatementBuilder.*;
import static com.lexicalscope.bl.procedures.Type.Bool;

import java.util.ArrayList;
import java.util.Deque;
import java.util.LinkedList;
import java.util.List;

import com.lexicalscope.bl.equiv.Expression;
import com.lexicalscope.bl.equiv.Statement;
import com.lexicalscope.bl.procedures.ConditionalStatement;
import com.lexicalscope.bl.procedures.Multiversion;
import com.lexicalscope.bl.procedures.PredicatedStatement;
import com.lexicalscope.bl.procedures.Procedure;
import com.lexicalscope.bl.procedures.StatementAdaptor;
import com.lexicalscope.bl.procedures.VariableName;

public class ReplaceConditionalsWithPredicatedExecution {
    public static final class FlattenConditionals extends StatementAdaptor {
        private final Deque<Expression> conditions = new LinkedList<>();

        /*
        @Override public List<Statement> visitConditionVariable(final ConditionVariableStatement statement) {
            final ConditionVariableStatement cloneConditionVariableStatement = new ConditionVariableStatement(
                    cloneVariable(statement.getLhsVar()),
                    statement.getExpression().accept(this));

            final ConditionVariableStatement falseConditionVariableStatement = new ConditionVariableStatement(
                    cloneVariable(statement.getLhsVar()),
                    falseExpression());


            Expression condition;
            if(conditions.isEmpty()) {
                condition = trueExpression();
            } else {
                condition = conditions.peek();
            }

            // we must always make sure to set the condition variable, since it may not have been initialised
            return
                    statements().
                    conditional(condition).
                    then(singleton(cloneConditionVariableStatement)).
                    elsethen(singleton(falseConditionVariableStatement)).mk();
        }
        */

        @Override protected List<Statement> decorate(final Statement statement) {
            Expression condition;
            if(conditions.isEmpty()) {
                condition = trueExpression();
            } else {
                condition = conditions.peek();
            }
            return statements().predicated(condition, singleton(statement)).mk();
        }

//        @Override public List<Statement> visitConditionVariable(final ConditionVariableStatement statement) {
//            return singleton(new ConditionVariableStatement(
//                    cloneVariable(statement.getLhsVar()),
//                    statement.getExpression().accept(this)));
//        }

        @Override public List<Statement> visitConditional(final ConditionalStatement statement) {
            conditions.push(statement.getCondition());
            final List<Statement> thenStatements = cloneBlockStatements(statement.getThenStatements());
            conditions.pop();

            conditions.push(notExpression(statement.getCondition()));
            final List<Statement> elseStatements = cloneBlockStatements(statement.getElseStatements());
            conditions.pop();

            final List<Statement> result = new ArrayList<>();
            result.addAll(thenStatements);
            result.addAll(elseStatements);
            return result;
        }

        @Override public List<Statement> visitPredicated(final PredicatedStatement statement) {
            return singleton(new PredicatedStatement(
                    cloneExpression(statement.getCondition()),
                    cloneBlockStatements(statement.getPredicatedStatement())));
        }
    }

    private static final class IntroduceConditionVariables extends StatementAdaptor {
        private VariableNameGenerator nameGenerator;
        final Deque<Expression> variables = new LinkedList<>();

        @Override public void enterProcedure(final Procedure procedure) {
            super.enterProcedure(procedure);
            this.nameGenerator = variableNameGenerator("c", Bool);
        }

        @Override public void exitProcedure() {
            this.nameGenerator = null;
        }

        @Override public List<Statement> visitConditional(final ConditionalStatement statement) {
            final VariableName conditionVariable = nameGenerator.next();
            variables.push(localRead(conditionVariable));
            final List<Statement> thenStatements = cloneBlockStatements(statement.getThenStatements());
            variables.pop();

            variables.push(notExpression(localRead(conditionVariable)));
            final List<Statement> elseStatements = cloneBlockStatements(statement.getElseStatements());
            variables.pop();

            Expression condition;
            if(!variables.isEmpty()) {
                condition = variables.peek().and(cloneExpression(statement.getCondition()));
            } else {
                condition = statement.getCondition();
            }

            return statements().
                    conditionVariable(conditionVariable, condition).
                    conditional(localRead(conditionVariable)).
                    then(thenStatements).
                    elsethen(elseStatements).
                    mk();
        }
    }

    public static Multiversion flattenConditionals(final Multiversion programs) {
        return clonePrograms(
                introduceConditionVariables(programs),
                new FlattenConditionals());
    }

    public static Multiversion introduceConditionVariables(final Multiversion programs) {
        return clonePrograms(programs, new IntroduceConditionVariables());
    }
}
