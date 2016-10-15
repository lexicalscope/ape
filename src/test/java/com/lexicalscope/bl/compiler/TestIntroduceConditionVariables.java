package com.lexicalscope.bl.compiler;

import static com.lexicalscope.bl.compiler.ReplaceConditionalsWithPredicatedExecution.introduceConditionVariables;
import static com.lexicalscope.bl.equiv.ProgramCollector.programs;
import static com.lexicalscope.bl.procedures.Multiversion.procedureNamed;
import static com.lexicalscope.bl.procedures.Procedure.declaresVariables;
import static com.lexicalscope.bl.procedures.StatementBuilder.*;
import static com.lexicalscope.bl.procedures.VariableName.boolVariableName;

import java.io.IOException;

import org.junit.Rule;
import org.junit.Test;

import com.lexicalscope.bl.parser.BlAntlrRule;
import com.lexicalscope.bl.parser.UseProgram;
import com.lexicalscope.bl.procedures.Multiversion;
import com.lexicalscope.bl.procedures.Procedure;

public class TestIntroduceConditionVariables {
    @Rule public BlAntlrRule<Multiversion> p = new BlAntlrRule<Multiversion>() {
        @Override protected Multiversion parseNow() {
            return introduceConditionVariables(programs(parser().multiversion()));
        }
    };

    @Test @UseProgram("programWithConditionals.bl")
    public void aConditionalIsIdentifiedIntroducingANewBooleanVariable() throws IOException {
        p.assertThat(procedureNamed("Conditional", declaresVariables(boolVariableName("$c#0"))));
    }

    @Test @UseProgram("programWithConditionals.bl")
    public void multipleConditionalsAreIdentifiedIntroducingNewBooleanVariables() throws IOException {
        p.assertThat(procedureNamed("TwoConditional", declaresVariables(boolVariableName("$c#0"), boolVariableName("$c#1"))));
    }

    @Test @UseProgram("programWithConditionals.bl")
    public void conditionalExpressionIsExtractedIntoVariable() throws IOException {
        p.assertThat(procedureNamed("Conditional",
                Procedure.hasStatements(
                        statements().
                            conditionVariable("$c#0", equalToExpression("x", "y")).
                            conditional(localRead(boolVariableName("$c#0"))).then().elsethen()
                        )));
    }

    @Test @UseProgram("programWithConditionals.bl")
    public void nestedConditionalHasTwoConditionVariables() throws IOException {
        p.assertThat(procedureNamed("NestedConditional",
                Procedure.hasStatements(
                        statements().
                        conditionVariable("$c#0", equalToExpression("x", "y")).
                            conditional(localRead(boolVariableName("$c#0"))).
                                then(statements().
                                    conditionVariable("$c#1",localRead(boolVariableName("$c#0")).and(equalToExpression("x", "x"))).
                                    conditional(localRead(boolVariableName("$c#1"))).then().elsethen()
                                ).elsethen()
                        )));
    }

    @Test @UseProgram("programWithConditionals.bl")
    public void elseNestedConditionalHasTwoConditionVariables() throws IOException {
        p.assertThat(procedureNamed("ElseNestedConditional",
                Procedure.hasStatements(
                        statements().
                        conditionVariable("$c#0", equalToExpression("x", "y")).
                            conditional(localRead(boolVariableName("$c#0"))).
                                then().
                                elsethen(statements().
                                        conditionVariable("$c#1",notExpression(localRead(boolVariableName("$c#0"))).and(equalToExpression("x", "x"))).
                                        conditional(localRead(boolVariableName("$c#1"))).then().elsethen()
                                    )
                        )));
    }
}
