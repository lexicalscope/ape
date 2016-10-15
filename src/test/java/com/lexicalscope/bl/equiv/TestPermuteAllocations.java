package com.lexicalscope.bl.equiv;

import static com.lexicalscope.MatchersJ8.containsMatching;
import static com.lexicalscope.bl.compiler.AllocateUpfront.allocateUpfront;
import static com.lexicalscope.bl.compiler.VersionVariables.versionVariables;
import static com.lexicalscope.bl.equiv.PermutedAllocations.*;
import static com.lexicalscope.bl.equiv.ProcedurePair.permutedAllocations;
import static com.lexicalscope.bl.equiv.ProgramCollector.programs;
import static org.hamcrest.MatcherAssert.assertThat;
import static org.hamcrest.Matchers.hasItem;

import java.io.IOException;
import java.util.List;

import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.TemporaryFolder;

import com.lexicalscope.bl.parser.BlAntlrRule;
import com.lexicalscope.bl.parser.UseProgram;

public class TestPermuteAllocations {
    @Rule public TemporaryFolder folder = new TemporaryFolder();
    @Rule public BlAntlrRule<List<ProcedurePair>> p = new BlAntlrRule<List<ProcedurePair>>() {
        @Override protected List<ProcedurePair> parseNow() {
            return versionVariables(allocateUpfront(programs(parser().multiversion()))).pairs();
        }
    };

    @Test @UseProgram("SeveralAllocationsToPermute.bl") public void allocationsArePermuted() throws IOException, InterruptedException {
        assertThat(p.tree(),
                hasItem(permutedAllocations(containsMatching(
                            permutation(
                                pair("$a#0_0", "$a#0_1"),
                                pair("$a#1_0", "$a#1_1"),
                                pair("$a#2_0", "$a#2_1")),
                            permutation(
                                pair("$a#1_0", "$a#0_1"),
                                pair("$a#0_0", "$a#1_1"),
                                pair("$a#2_0", "$a#2_1")),
                            permutation(
                                pair("$a#2_0", "$a#0_1"),
                                pair("$a#0_0", "$a#1_1"),
                                pair("$a#1_0", "$a#2_1")),
                            permutation(
                                pair("$a#0_0", "$a#0_1"),
                                pair("$a#2_0", "$a#1_1"),
                                pair("$a#1_0", "$a#2_1")),
                            permutation(
                                pair("$a#1_0", "$a#0_1"),
                                pair("$a#2_0", "$a#1_1"),
                                pair("$a#0_0", "$a#2_1")),
                            permutation(
                                pair("$a#2_0", "$a#0_1"),
                                pair("$a#1_0", "$a#1_1"),
                                pair("$a#0_0", "$a#2_1"))))));
    }
}
