package com.lexicalscope.bl.parser;

import java.io.IOException;

import org.antlr.v4.runtime.RecognitionException;
import org.junit.Rule;
import org.junit.Test;

import com.lexicalscope.bl.parser.BlParser.ProgramContext;

public class ParserTests {
    @Rule public BlAntlrRule<ProgramContext> p = new BlAntlrRule<ProgramContext>() {
        @Override protected ProgramContext parseNow() {
            return parser().program();
        }
    };

	@Test @UseProgram("program001.bl") public void parseAProgram() throws IOException {
		p.assertThat(p.hasProcedureContextCalled("HeapSwap"));
		p.assertThat(p.hasProcedureContextCalled("HeapSwap", p.withDeclaredParameters("x","y")));
	}

	@Test @UseProgram("program002.bl") public void parseAProcedure() throws RecognitionException, IOException {
		p.assertThat(p.hasProcedureContextCalled("SimpleProcedure"));
	}

	@Test @UseProgram("program003.bl") public void parseAProcedureCall() throws RecognitionException, IOException {
		p.assertThat(p.hasProcedureContextCalled("CallAnother", p.containingCallOf("Another", p.withParameters("x","y","t"))));
	}

	@Test @UseProgram("program004.bl") public void parseListOfProcedures() throws RecognitionException, IOException {
		p.assertThat(p.hasProcedures(
			p.procedureCalled("FirstProcedure"),
			p.procedureCalled("SecondProcedure"),
			p.procedureCalled("ThirdProcedure")));
	}
}
