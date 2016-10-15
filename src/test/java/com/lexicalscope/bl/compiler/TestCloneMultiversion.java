package com.lexicalscope.bl.compiler;

import static com.lexicalscope.bl.equiv.ProgramCollector.programs;
import static org.hamcrest.MatcherAssert.assertThat;
import static org.hamcrest.Matchers.equalTo;

import java.io.IOException;

import org.junit.Rule;
import org.junit.Test;

import com.lexicalscope.bl.parser.BlAntlrRule;
import com.lexicalscope.bl.parser.UseProgram;
import com.lexicalscope.bl.procedures.Multiversion;

public class TestCloneMultiversion {
    private static final class Result {
        public Result(final Multiversion original, final Multiversion clone) {
            this.original = original;
            this.clone = clone;
        }
        Multiversion original;
        Multiversion clone;
    }

    @Rule public BlAntlrRule<Result> p = new BlAntlrRule<Result>() {
        @Override protected Result parseNow() {
            final Multiversion original = programs(parser().multiversion());
            return new Result(original, CloneProgram.clone(original));
        }
    };

    @Test @UseProgram("programWithStatementsToClone.bl")
    public void programIsCloned() throws IOException {
        assertThat(p.tree().original, equalTo(p.tree().clone));
    }
}
