package com.lexicalscope.bl.equiv;

import java.io.File;
import java.io.IOException;

import org.junit.Rule;
import org.junit.rules.TemporaryFolder;
import org.junit.rules.TestName;

import com.lexicalscope.bl.verification.ExplicitPermutationVerificationStrategy;

public class AbstractTestExplicitPermutationPreamble {
    @Rule public TemporaryFolder folder = new TemporaryFolder();
    @Rule public TestName testName = new TestName();

    BoogieResult verifyWithBoogie() throws IOException, InterruptedException {
        final File outputDir = new File("generated-testcases/explicitPermutationPreamble");
        outputDir.mkdirs();

        return new BoogieVerifier().execBoogie(
                new BoogieGenerator(outputDir,
                        new ExplicitPermutationVerificationStrategy())
                            .writeBoogieForTest("test_" + testName.getMethodName()));
    }
}
