package com.lexicalscope.bl.compiler;

import static com.lexicalscope.bl.compiler.VersionVariables.versionVariables;
import static com.lexicalscope.bl.equiv.ProgramCollector.programs;
import static com.lexicalscope.bl.procedures.Multiversion.procedureVersion;
import static com.lexicalscope.bl.procedures.Path.path;
import static com.lexicalscope.bl.procedures.Procedure.hasStatements;
import static com.lexicalscope.bl.procedures.StatementBuilder.*;

import java.io.IOException;

import org.junit.Rule;
import org.junit.Test;

import com.lexicalscope.bl.parser.BlAntlrRule;
import com.lexicalscope.bl.parser.UseProgram;
import com.lexicalscope.bl.procedures.Multiversion;

public class TestRenameVariablesAccordingToVersion {
    @Rule public BlAntlrRule<Multiversion> p = new BlAntlrRule<Multiversion>() {
        @Override protected Multiversion parseNow() {
            return versionVariables(programs(parser().multiversion()));
        }
    };

    @Test @UseProgram("programWithVariablesToRename.bl")
    public void variablesAreRenamed() throws IOException {
        p.assertThat(procedureVersion("OneLocal", 0,
                hasStatements(
                        statements().
                            localUpdate("x_0", localRead("x")).
                            localUpdate("y_0", localRead("y")).
                            localUpdate("$t#0_0", heapRead(path("x_0", "f"))).
                            localUpdate("t_0", localRead("$t#0_0"))
                        )));

        p.assertThat(procedureVersion("OneLocal", 1,
                hasStatements(
                        statements().
                            localUpdate("x_1", localRead("x")).
                            localUpdate("y_1", localRead("y")).
                            localUpdate("$t#0_1", heapRead(path("x_1", "f"))).
                            localUpdate("t_1", localRead("$t#0_1"))
                        )));
    }
}
