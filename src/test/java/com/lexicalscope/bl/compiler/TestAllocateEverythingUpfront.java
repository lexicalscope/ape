package com.lexicalscope.bl.compiler;

import static com.lexicalscope.bl.compiler.AllocateUpfront.allocateUpfront;
import static com.lexicalscope.bl.equiv.ProgramCollector.programs;
import static com.lexicalscope.bl.procedures.Multiversion.procedureNamed;
import static com.lexicalscope.bl.procedures.Procedure.*;
import static com.lexicalscope.bl.procedures.StatementBuilder.*;
import static org.hamcrest.core.CombinableMatcher.both;

import java.io.IOException;

import org.junit.Rule;
import org.junit.Test;

import com.lexicalscope.bl.parser.BlAntlrRule;
import com.lexicalscope.bl.parser.UseProgram;
import com.lexicalscope.bl.procedures.Multiversion;
import com.lexicalscope.bl.procedures.StatementBuilder;

public class TestAllocateEverythingUpfront {
    @Rule public BlAntlrRule<Multiversion> p = new BlAntlrRule<Multiversion>() {
        @Override protected Multiversion parseNow() {
            return allocateUpfront(programs(parser().multiversion()));
        }
    };

    @Test @UseProgram("programWithAllocations.bl")
    public void allocationsAreMovedToPrefix() throws IOException {
        p.assertThat(
                procedureNamed("OneAllocation",
                both(
                    hasPrefix(statements().
                        heapAllocationStatement("$a#0"))).
                and(
                    hasStatements(statements().
                        heapUpdate("y", "f" ,"x").
                        localUpdate("$t#0", localRead("$a#0")).
                        localUpdate("t", localRead("$t#0"))
                     ))));
    }

    @Test @UseProgram("programWithAllocations.bl")
    public void conditionalAllocationsAreMovedToPrefix() throws IOException {
        p.assertThat(
                procedureNamed("ConditionalAllocation",
                both(
                    hasPrefix(statements().
                        heapAllocationStatement("$a#0"))).
                and(
                    hasStatements(statements().
                        heapUpdate("y", "f", "x").
                        conditional(StatementBuilder.equalToExpression("x", "y")).
                            then(statements().localUpdate("$t#0", localRead("$a#0")).localUpdate("t", localRead("$t#0"))).
                            elsethen()
                     ))));
    }


    @Test @UseProgram("programWithAllocations.bl")
    public void usesMaximumNumberOfAllocationsInProcedurePair() throws IOException {
        p.assertThat(
                procedureNamed("DifferentNumberOfAllocationSites",
                both(
                    hasPrefix(statements().
                        heapAllocationStatement("$a#0").
                        heapAllocationStatement("$a#1").
                        heapAllocationStatement("$a#2"))).
                and(
                    hasStatements(statements().
                        localUpdate("$t#0", localRead("$a#0")).
                        localUpdate("t1", localRead("$t#0")).
                        localUpdate("$t#1", localRead("$a#1")).
                        localUpdate("t2", localRead("$t#1"))
                 ))));
    }
}
