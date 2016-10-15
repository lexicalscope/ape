package com.lexicalscope.bl.compiler;

import static com.lexicalscope.bl.compiler.ReplaceConditionalsWithPredicatedExecution.flattenConditionals;
import static com.lexicalscope.bl.equiv.ProgramCollector.programs;
import static com.lexicalscope.bl.procedures.Multiversion.procedureNamed;
import static com.lexicalscope.bl.procedures.Procedure.hasStatements;
import static com.lexicalscope.bl.procedures.StatementBuilder.*;
import static com.lexicalscope.bl.procedures.VariableName.boolVariableName;

import java.io.IOException;

import org.junit.Rule;
import org.junit.Test;

import com.lexicalscope.bl.parser.BlAntlrRule;
import com.lexicalscope.bl.parser.UseProgram;
import com.lexicalscope.bl.procedures.Multiversion;

public class TestFlattenConditionals {
    @Rule public BlAntlrRule<Multiversion> p = new BlAntlrRule<Multiversion>() {
        @Override protected Multiversion parseNow() {
            return flattenConditionals(programs(parser().multiversion()));
        }
    };

    @Test @UseProgram("programWithConditionals.bl")
    public void conditionalStatementsAreConvertedToPredicated() throws IOException {
        System.out.println(p.tree().procedure("ConditionalWithTwoStatements"));
        p.assertThat(
                procedureNamed("ConditionalWithTwoStatements",
                hasStatements(
                        statements().
                            predicated(
                                trueExpression(),
                                statements().conditionVariable("$c#0", equalToExpression("x", "y"))).
                            predicated(
                                    localRead(boolVariableName("$c#0")),
                                    statements().heapUpdate("x", "f", "x")).
                            predicated(
                                    localRead(boolVariableName("$c#0")),
                                    statements().heapUpdate("y", "f", "y"))
                        )));
    }

    @Test @UseProgram("programWithConditionals.bl")
    public void conditionalStatementsInElseBranchAreConvertedToPredicated() throws IOException {
        p.assertThat(
                procedureNamed("ConditionalWithStatementsInBothBranches",
                hasStatements(
                        statements().
                            predicated(
                                    trueExpression(),
                                    statements().conditionVariable("$c#0", equalToExpression("x", "y"))).
                            predicated(
                                    localRead(boolVariableName("$c#0")),
                                    statements().heapUpdate("x", "f", "x")).
                            predicated(
                                    localRead(boolVariableName("$c#0")),
                                    statements().heapUpdate("y", "f", "y")).
                            predicated(
                                    notExpression(localRead(boolVariableName("$c#0"))),
                                    statements().heapUpdate("y", "f", "x")).
                            predicated(
                                    notExpression(localRead(boolVariableName("$c#0"))),
                                    statements().heapUpdate("x", "f", "y"))
                        )));
    }

    @Test @UseProgram("programWithConditionals.bl")
    public void conditionalStatementsInNestedBranchAreFlattenedToPredicated() throws IOException {
        p.assertThat(
                procedureNamed("ConditionalStatementsInNestedBranches",
                hasStatements(
                        statements().
                            predicated(
                                    trueExpression(),
                                    statements().conditionVariable("$c#0", equalToExpression("x", "y"))).
                            predicated(
                                    localRead(boolVariableName("$c#0")),
                                    statements().heapUpdate("x", "f", "x")).
                            predicated(
                                    localRead(boolVariableName("$c#0")),
                                    statements().heapUpdate("y", "f", "y")).
                            predicated(
                                    localRead(boolVariableName("$c#0")),
                                    statements().conditionVariable("$c#1", localRead(boolVariableName("$c#0")).and(equalToExpression("x", "x")))).
                            predicated(
                                    localRead(boolVariableName("$c#1")),
                                    statements().heapUpdate("y", "f", "x")).
                            predicated(
                                    localRead(boolVariableName("$c#1")),
                                    statements().heapUpdate("x", "f", "y"))
                        )));
    }
}

