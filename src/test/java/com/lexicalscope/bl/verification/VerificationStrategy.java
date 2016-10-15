package com.lexicalscope.bl.verification;

import java.io.File;

import com.lexicalscope.bl.equiv.BoogieWriter;

public interface VerificationStrategy {
    BoogieWriter boogieWriter(File output);
}
