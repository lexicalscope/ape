package com.lexicalscope.bl.compiler;

import static com.lexicalscope.bl.compiler.AllocateUpfront.hasAllocationSiteCount;
import static com.lexicalscope.bl.equiv.ProgramCollector.programs;
import static com.lexicalscope.bl.procedures.Multiversion.procedureNamed;

import java.io.IOException;

import org.junit.Rule;
import org.junit.Test;

import com.lexicalscope.bl.parser.BlAntlrRule;
import com.lexicalscope.bl.parser.UseProgram;
import com.lexicalscope.bl.procedures.Multiversion;

public class TestCountAllocations {
    @Rule public BlAntlrRule<Multiversion> p = new BlAntlrRule<Multiversion>() {
        @Override protected Multiversion parseNow() {
            return programs(parser().multiversion());
        }
    };

    @Test @UseProgram("programWithAllocations.bl")
    public void allocationsAreCounted() throws IOException {
        p.assertThat(procedureNamed("OneAllocation", hasAllocationSiteCount(1)));
    }

    @Test @UseProgram("programWithAllocations.bl")
    public void conditionalAllocationsAreCounted() throws IOException {
        p.assertThat(procedureNamed("ConditionalAllocation", hasAllocationSiteCount(1)));
    }
}
