package com.lexicalscope.bl.equiv;

import static com.lexicalscope.bl.equiv.BoogieResult.verifiedWithNoErrors;
import static org.hamcrest.MatcherAssert.assertThat;

import java.io.IOException;

import org.junit.Ignore;
import org.junit.Test;

public class TestUnrolledReachabilityRefRel extends AbstractTestExplicitPermutationPreamble {
    @Test @Ignore public void emptyRefRelHasNoElements() throws IOException, InterruptedException {
        assertThat(verifyWithBoogie(), verifiedWithNoErrors(1));
    }

    @Test @Ignore public void refRelIsARelation() throws IOException, InterruptedException {
        assertThat(verifyWithBoogie(), verifiedWithNoErrors(1));
    }

    @Test @Ignore public void refRelOneToOne() throws IOException, InterruptedException {
        assertThat(verifyWithBoogie(), verifiedWithNoErrors(2));
    }

    @Test @Ignore public void refRelBijection() throws IOException, InterruptedException {
        assertThat(verifyWithBoogie(), verifiedWithNoErrors(4));
    }
}
