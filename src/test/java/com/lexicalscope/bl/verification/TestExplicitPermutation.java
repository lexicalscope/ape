package com.lexicalscope.bl.verification;

import java.io.File;


public class TestExplicitPermutation extends TestVerification {
    @Override
    ExplicitPermutationVerificationStrategy verificationStrategy() {
        return new ExplicitPermutationVerificationStrategy();
    }

    @Override
    File outputDirectory() {
        return new File("generated-testcases/explicitPermutation");
    }
}
