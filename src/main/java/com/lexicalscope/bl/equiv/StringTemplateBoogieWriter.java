package com.lexicalscope.bl.equiv;

import static java.util.Objects.requireNonNull;

import java.io.File;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.OutputStreamWriter;

import org.stringtemplate.v4.AutoIndentWriter;
import org.stringtemplate.v4.ST;
import org.stringtemplate.v4.STGroup;
import org.stringtemplate.v4.STGroupFile;

public class StringTemplateBoogieWriter implements BoogieWriter {
    private final STGroup group;
    private FileOutputStream stream;
    private AutoIndentWriter stWriter;
    private OutputStreamWriter osWriter;

    public StringTemplateBoogieWriter(final File outputfile, final String templateName) {
        group = new STGroupFile(getClass().getResource(templateName), "UTF-8", '%', '%');

        try {
            stream = new FileOutputStream(outputfile);
            osWriter = new OutputStreamWriter(stream);
            stWriter = new AutoIndentWriter(osWriter);
        } catch (final IOException e) {
            try {
                stream.close();
            } catch (final IOException e1) {
                throw new RuntimeException("unable to write to output, and unable to close output", e);
            }
            throw new RuntimeException("unable to write to output", e);
        }
    }

    @Override public void writeTest(final String testName) {
        writePreamble();
        write(group.getInstanceOf(testName));
    }

    @Override
    public void writePairs(final ProcedurePairs procedurePairs) {
        writePreamble();

        for (final ProcedurePair procedurePair : procedurePairs) {
            writePair(procedurePair);
        }
    }

    void writePreamble() {
        final ST preamble = group.getInstanceOf("preamble");
        //preamble.add("reachability", reachability);
        write(preamble);
    }

    private void writePair(final ProcedurePair procedurePair) {
        final ST decl = group.getInstanceOf("mutualVerifyDecl");
        decl.add("name", procedurePair.name());
        decl.add("params", procedurePair.params());
        decl.add("pair", procedurePair);
        decl.add("ver0", new ProcedureVersion("0", procedurePair.procedure0()));
        decl.add("ver1", new ProcedureVersion("1", procedurePair.procedure1()));
        //decl.add("reachability", procedurePair.reachability());
        write(decl);
    }

    private void write(final ST template) {
        requireNonNull(template, "template not found");
        try {
            template.write(stWriter);
        } catch (final IOException e) {
            throw new RuntimeException("unable to write to output", e);
        }
    }

    @Override public void close() {
        try {
            try {
                osWriter.flush();
                stream.flush();
            } finally {
                stream.close();
            }
        } catch (final IOException e) {
            throw new RuntimeException("unable to close output", e);
        }
    }
}
