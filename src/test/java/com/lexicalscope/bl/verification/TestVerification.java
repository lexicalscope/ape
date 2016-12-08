package com.lexicalscope.bl.verification;

import static com.lexicalscope.bl.compiler.AllocateUpfront.allocateUpfront;
import static com.lexicalscope.bl.compiler.VersionVariables.versionVariables;
import static com.lexicalscope.bl.equiv.BoogieResult.*;
import static com.lexicalscope.bl.equiv.ProgramCollector.programs;
import static org.hamcrest.MatcherAssert.assertThat;

import java.io.File;
import java.io.IOException;

import org.junit.Ignore;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.TemporaryFolder;

import com.lexicalscope.bl.equiv.BoogieGenerator;
import com.lexicalscope.bl.equiv.BoogieResult;
import com.lexicalscope.bl.equiv.BoogieVerifier;
import com.lexicalscope.bl.parser.BlAntlrRule;
import com.lexicalscope.bl.parser.UseProgram;
import com.lexicalscope.bl.procedures.Multiversion;

public abstract class TestVerification {
    @Rule public TemporaryFolder folder = new TemporaryFolder();
    @Rule public BlAntlrRule<Multiversion> p = new BlAntlrRule<Multiversion>() {
        @Override protected Multiversion parseNow() {
            //return versionVariables(allocateUpfront(flattenConditionals(programs(parser().multiversion()))));
            return versionVariables(allocateUpfront(programs(parser().multiversion())));
        }
    };

    ////////////////////////////////////////////
    // Full Examples
    ///////////////////////////////////////////
    @Test @UseProgram("RecursiveListCopyExample.bl") public void recursiveListCopyVerifies() throws IOException, InterruptedException {
        assertThat(verifyWithBoogie(), verifiedWithNoErrors(3));
    }

    @Ignore
    @Test @UseProgram("ProcedureReturnsValuesViaFramedTemporary.bl") public void outOfOrderProcedureCallsThatOnlyModifyDisjointHeapVerifies() throws IOException, InterruptedException {
        assertThat(verifyWithBoogie(), verifiedWithNoErrors(3));
    }

    ////////////////////////////////////////////
    // Single Feature Tests
    ///////////////////////////////////////////
    @Test @UseProgram("Empty.bl") public void emptyVerifies() throws IOException, InterruptedException {
        assertThat(verifyWithBoogie(), verifiedWithNoErrors(0));
    }

    @Test @UseProgram("SingleAllocation.bl") public void aSingleAllocationVerifies() throws IOException, InterruptedException {
        assertThat(verifyWithBoogie(), verifiedWithNoErrors(3));
    }

    @Test @UseProgram("DoubleAllocationInDifferentOrders.bl") public void aDoubleAllocationVerifies() throws IOException, InterruptedException {
        assertThat(verifyWithBoogie(), verifiedWithNoErrors(3));
    }

    @Test @UseProgram("DifferInSingleGarbageAllocation.bl") public void differenceIsSingleGarbageAllocationVerifies() throws IOException, InterruptedException {
        assertThat(verifyWithBoogie(), verifiedWithNoErrors(3));
    }

    @Test @UseProgram("DifferInShapeOfGarbage.bl") public void differentShapedGarabgeVerifies() throws IOException, InterruptedException {
        final BoogieResult verifyWithBoogie = verifyWithBoogie();
        assertThat(verifyWithBoogie, verifiedWithNoErrors(3));
    }

    @Test @UseProgram("SingleCall.bl") public void singleProcedureCallVerifies() throws IOException, InterruptedException {
        final BoogieResult verifyWithBoogie = verifyWithBoogie();
        assertThat(verifyWithBoogie, verifiedWithNoErrors(6));
    }

    @Test @UseProgram("SingleCallToDifferentProcedures.bl") public void singleCallToDifferentProceduresFails() throws IOException, InterruptedException {
        final BoogieResult verifyWithBoogie = verifyWithBoogie();
        assertThat(verifyWithBoogie, verifiedWith(8,1));
    }

    @Test @UseProgram("AllocationMovesPastCall.bl") public void allocationMovingPastCallVerifies() throws IOException, InterruptedException {
        final BoogieResult verifyWithBoogie = verifyWithBoogie();
        assertThat(verifyWithBoogie, verifiedWithNoErrors(6));
    }

    @Test @UseProgram("RecursivelyWalkList.bl") public void recursiveListWalkVerifies() throws IOException, InterruptedException {
        assertThat(verifyWithBoogie(), verifiedWithNoErrors(3));
    }

    @Test @UseProgram("ReverseAllocationsBeforeCall.bl") public void reversingAllocationsBeforeACallVerifies() throws IOException, InterruptedException {
        assertThat(verifyWithBoogie(), verifiedWithNoErrors(6));
    }

    @Test @UseProgram("FramedNoopProcedure.bl") public void noopCallVerifies() throws IOException, InterruptedException {
        assertThat(verifyWithBoogie(), verifiedWithNoErrors(9));
    }

    @Test @UseProgram("FramedGarbageOnlyProcedure.bl") public void effectivelyNoopCallVerifies() throws IOException, InterruptedException {
        assertThat(verifyWithBoogie(), verifiedWithNoErrors(9));
    }

    @Test @UseProgram("CopyCycle.bl") public void copyingACyclicalStructureWorks() throws IOException, InterruptedException {
        assertThat(verifyWithBoogie(), verifiedWithNoErrors(6));
    }

    @Test @UseProgram("TableInsert.bl") public void tableInsert() throws IOException, InterruptedException {
        assertThat(verifyWithBoogie(), verifiedWithNoErrors(6));
    }

    ////////////////////////////////// VVVV OLD VVVV

    @Test @UseProgram("Swap.bl") public void heapSwapAndStackSwapDifferent() throws IOException, InterruptedException {
        assertThat(verifyWithBoogie(), verifiedWithNoErrors(3));
    }

    @Test @UseProgram("Call001.bl") public void justACall() throws IOException, InterruptedException {
        assertThat(verifyWithBoogie(), verifiedWithNoErrors(6));
    }

    @Test @UseProgram("Call002.bl") public void twoCalls() throws IOException, InterruptedException {
        assertThat(verifyWithBoogie(), verifiedWithNoErrors(6));
    }

    @Test @UseProgram("Frame001.bl") public void allocationMovedPastCall() throws IOException, InterruptedException {
        assertThat(verifyWithBoogie(), verifiedWithNoErrors(6));
    }

    @Test @UseProgram("Frame002.bl") public void allocationsMovedPassedCallThatNeedsFrameInfo() throws IOException, InterruptedException {
        assertThat(verifyWithBoogie(), verifiedWithNoErrors(6));
    }

    @Test @UseProgram("Frame003.bl") public void allocationMovedPassedCallThatIsNotEquivalent() throws IOException, InterruptedException {
        assertThat(verifyWithBoogie(), verifiedWith(5, 1));
    }

    @Test @Ignore("removed the reads frame support") @UseProgram("Frame004.bl") public void methodReadsToMuch() throws IOException, InterruptedException {
        assertThat(verifyWithBoogie(), verifiedWith(1, 2));
    }

    @Test @UseProgram("Frame005.bl") public void methodWritesToMuch() throws IOException, InterruptedException {
        assertThat(verifyWithBoogie(), verifiedWith(1, 2));
    }

    @Test @UseProgram("Frame006.bl") public void unsoundnessFromInconsistentIsomorphisms() throws IOException, InterruptedException {
        assertThat(verifyWithBoogie(), verifiedWith(5, 1));
    }

    @Test @UseProgram("NonEquiv001.bl") public void assignsDifferentLocations() throws IOException, InterruptedException {
        assertThat(verifyWithBoogie(), verifiedWith(2, 1));
    }

    @Test @Ignore("The performance implications of the factorial complexity show up here, we can't actually handle the size of the generated program")
    @UseProgram("NonEquiv002.bl") public void createsDifferentLengthLists() throws IOException, InterruptedException {
        assertThat(verifyWithBoogie(), verifiedWith(2, 1));
    }

    @Test @Ignore("The performance implications of the factorial complexity show up here, it takes a long time to decide if all if the permutations are not equivalent")
    @UseProgram("NonEquiv003.bl") public void aliasedDifferentFromNonAliased() throws IOException, InterruptedException {
        assertThat(verifyWithBoogie(), verifiedWith(2, 1));
    }

    @Test @UseProgram("DifferentParameters.bl") public void differentParameters() throws IOException, InterruptedException {
        assertThat(verifyWithBoogie(), verifiedWith(5, 1));
    }

    @Test @Ignore @UseProgram("Conditional001.bl") public void conditionalReversal() throws IOException, InterruptedException {
        assertThat(verifyWithBoogie(), verifiedWith(9, 0));
    }

    @Test @Ignore @UseProgram("Conditional002.bl") public void nonEquivalentConditionalBodies() throws IOException, InterruptedException {
        assertThat(verifyWithBoogie(), verifiedWith(8, 2));
    }

    @Test @Ignore @UseProgram("PassNew001.bl") public void passNewThenUseItCheckedInAConditional() throws IOException, InterruptedException {
        assertThat(verifyWithBoogie(), verifiedWith(6, 0));
    }

    @Test @Ignore @UseProgram("PassNew002.bl") public void passNewThenUseWronglyInAConditional() throws IOException, InterruptedException {
        assertThat(verifyWithBoogie(), verifiedWith(5, 1));
    }

    @Test @Ignore @UseProgram("PassNew003.bl") public void passNewThenUseItUncheckedInAConditional() throws IOException, InterruptedException {
        assertThat(verifyWithBoogie(), verifiedWith(6, 0));
    }

    @Test @Ignore @UseProgram("PassNew004.bl") public void passNewIndirectlyThenUseItInAConditional() throws IOException, InterruptedException {
        assertThat(verifyWithBoogie(), verifiedWith(6, 0));
    }

    @Test @Ignore @UseProgram("PassNew005.bl") public void passNewIndirectly() throws IOException, InterruptedException {
        assertThat(verifyWithBoogie(), verifiedWith(6, 0));
    }

    @Test @Ignore @UseProgram("PassNew006.bl") public void passNewViaNonParameterVariable() throws IOException, InterruptedException {
        assertThat(verifyWithBoogie(), verifiedWith(6, 0));
    }

    @Test @Ignore @UseProgram("PassNew007.bl") public void passNewViaNonParameterVariableSeveralTimes() throws IOException, InterruptedException {
        assertThat(verifyWithBoogie(), verifiedWith(6, 0));
    }

    @Test @Ignore @UseProgram("Recursion001.bl") public void copyAList() throws IOException, InterruptedException {
        assertThat(verifyWithBoogie(), verifiedWith(3, 0));
    }

    BoogieResult verifyWithBoogie() throws IOException, InterruptedException {
        final File outputDir = outputDirectory();
        outputDir.mkdirs();

        return new BoogieVerifier().execBoogie(new BoogieGenerator(outputDir, verificationStrategy()).writeBoogieForVersions(p));
    }

    abstract File outputDirectory();
    abstract VerificationStrategy verificationStrategy();
}
