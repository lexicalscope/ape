package com.lexicalscope.bl.equiv;

import static com.lexicalscope.Jc.$;

import java.io.File;
import java.io.IOException;
import java.nio.charset.Charset;
import java.nio.file.Files;

import com.lexicalscope.bl.parser.BlAntlrRule;
import com.lexicalscope.bl.procedures.Multiversion;
import com.lexicalscope.bl.verification.VerificationStrategy;

public class BoogieGenerator {
    private final File outputDir;
    private final VerificationStrategy strategy;

    public BoogieGenerator(final File outputDir, final VerificationStrategy strategy) {
        this.outputDir = outputDir;
        this.strategy = strategy;
    }

    public File writeBoogieForTest(final String testName) throws IOException, InterruptedException {
        final File output = new File(outputDir, testName+ ".bpl");
        try (BoogieWriter toBoogie = strategy.boogieWriter(output))
        {
            toBoogie.writeTest(testName);
        }
        printOut(output);
        return output;
    }

    public File writeBoogieForVersions(final BlAntlrRule<Multiversion> p) throws IOException, InterruptedException {
        final File output = new File(outputDir, p.boogieFile());
        writeBoogieTo(p.tree(), output);
        printOut(output);

        return output;
    }

    private void writeBoogieTo(final Multiversion context, final File output) {
        final ProcedurePairs procedurePairs = new ProcedurePairs(context.pairs());

        try (BoogieWriter toBoogie = strategy.boogieWriter(output))
        {
            toBoogie.writePairs(procedurePairs);
        }
    }

    private void printOut(final File output) throws IOException {
        $(Files.readAllLines(output.toPath(), Charset.forName("UTF-8"))).
            forEachCount((line, lineNumber) -> {
                System.out.println(String.format("%04d:%s", lineNumber + 1, line));
            });
    }
}
