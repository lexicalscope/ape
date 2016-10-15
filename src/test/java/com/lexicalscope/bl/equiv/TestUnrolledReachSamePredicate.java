package com.lexicalscope.bl.equiv;

import static com.lexicalscope.bl.equiv.BoogieResult.verifiedWithNoErrors;
import static org.hamcrest.MatcherAssert.assertThat;

import java.io.IOException;

import org.junit.Ignore;
import org.junit.Test;

public class TestUnrolledReachSamePredicate extends AbstractTestExplicitPermutationPreamble {
    @Test @Ignore public void canFindLocationsReachableByTheSamePath() throws IOException, InterruptedException {
        assertThat(verifyWithBoogie(), verifiedWithNoErrors(2));
    }

    @Test @Ignore public void thereIsAnIdentityIsomorphism() throws IOException, InterruptedException {
        assertThat(verifyWithBoogie(), verifiedWithNoErrors(2));
    }
}
