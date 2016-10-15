package com.lexicalscope.bl.equiv;

import static com.lexicalscope.bl.equiv.BoogieResult.verifiedWith;
import static com.lexicalscope.bl.equiv.BoogieResult.verifiedWithNoErrors;
import static org.hamcrest.MatcherAssert.assertThat;

import java.io.IOException;

import org.junit.Ignore;
import org.junit.Test;

public class TestUnrolledReachabilityPredicate extends AbstractTestExplicitPermutationPreamble {
    @Test @Ignore public void canFindEdgeInHeap() throws IOException, InterruptedException {
        assertThat(verifyWithBoogie(), verifiedWithNoErrors(1));
    }

    @Test @Ignore public void canDetermineReachability() throws IOException, InterruptedException {
        assertThat(verifyWithBoogie(), verifiedWithNoErrors(1));
    }

    @Test @Ignore public void reachabilityBeyondFuelIsUnknown() throws IOException, InterruptedException {
        assertThat(verifyWithBoogie(), verifiedWith(0, 2));
    }

    @Test @Ignore public void reachabilityWithinFuelIsKnown() throws IOException, InterruptedException {
        assertThat(verifyWithBoogie(), verifiedWithNoErrors(2));
    }
}
