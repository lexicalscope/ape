package com.lexicalscope.bl.verification;

import java.io.File;

import com.lexicalscope.bl.equiv.BoogieWriter;
import com.lexicalscope.bl.equiv.StringTemplateBoogieWriter;

public class ExplicitPermutationVerificationStrategy implements VerificationStrategy {
    @Override public BoogieWriter boogieWriter(final File output) {
        return new StringTemplateBoogieWriter(output, "explicitPermutationTemplates/equiv.stg");
    }
}
