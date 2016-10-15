package com.lexicalscope.bl.boogie;

import static com.lexicalscope.bl.equiv.BoogieResult.verifiedWith;
import static org.hamcrest.MatcherAssert.assertThat;

import org.junit.Ignore;
import org.junit.Rule;
import org.junit.Test;

import com.lexicalscope.bl.parser.BoogieFile;
import com.lexicalscope.bl.parser.BoogieRule;

public class TestBoogieDesign {
    @Rule public final BoogieRule rule = new BoogieRule();

    @Test @Ignore @BoogieFile("trivial.bpl") public void boogieIsAvailable() {
        assertThat(rule.verifyWithBoogie(), verifiedWith(1, 0));
    }

    @Test @Ignore @BoogieFile("reachability.bpl") public void fuelReachability() {
        assertThat(rule.verifyWithBoogie(), verifiedWith(1, 0));
    }

    @Test @Ignore @BoogieFile("isomorphism3.bpl") public void isomorphism() {
        assertThat(rule.verifyWithBoogie(), verifiedWith(7, 0));
    }

    @Test @Ignore @BoogieFile("isomorphism4.bpl") public void isomorphism4() {
        assertThat(rule.verifyWithBoogie(), verifiedWith(7, 0));
    }
}
