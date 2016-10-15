package com.lexicalscope.bl.compiler;

import static com.lexicalscope.bl.equiv.ProgramCollector.programs;
import static com.lexicalscope.bl.procedures.Multiversion.procedureNamed;
import static com.lexicalscope.bl.procedures.Path.path;
import static com.lexicalscope.bl.procedures.Procedure.hasStatements;
import static com.lexicalscope.bl.procedures.StatementBuilder.*;

import java.io.IOException;

import org.junit.Rule;
import org.junit.Test;

import com.lexicalscope.bl.parser.BlAntlrRule;
import com.lexicalscope.bl.parser.UseProgram;
import com.lexicalscope.bl.procedures.Multiversion;

public class TestSplitReadFromWrite {
    @Rule public BlAntlrRule<Multiversion> p = new BlAntlrRule<Multiversion>() {
        @Override protected Multiversion parseNow() {
            return programs(parser().multiversion());
        }
    };

    @Test @UseProgram("programWithHeapUpdates.bl")
    public void heapUpdateWithPathOnLhsSplitInTwo() throws IOException {
        p.assertThat(
                procedureNamed("HeapUpdateWithLhsPath",
                hasStatements(statements().
                    localUpdate("$t#0", heapRead(path("x","f"))).
                    heapUpdate("$t#0", "f", "y")
                 )));
    }

    @Test @UseProgram("programWithHeapUpdates.bl")
    public void heapUpdateWithPathOnRhsSplitInTwo() throws IOException {
        p.assertThat(
                procedureNamed("HeapUpdateWithRhsPath",
                hasStatements(statements().
                    localUpdate("$t#0", heapRead(path("y","f"))).
                    heapUpdate("x", "f", "$t#0")
                 )));
    }
}
