package com.lexicalscope.bl.parser;

import java.io.IOException;
import java.io.InputStream;

import org.antlr.v4.runtime.ANTLRInputStream;
import org.antlr.v4.runtime.BaseErrorListener;
import org.antlr.v4.runtime.CharStream;
import org.antlr.v4.runtime.CommonTokenStream;
import org.antlr.v4.runtime.InputMismatchException;
import org.antlr.v4.runtime.Lexer;
import org.antlr.v4.runtime.Parser;
import org.antlr.v4.runtime.RecognitionException;
import org.antlr.v4.runtime.Recognizer;
import org.antlr.v4.runtime.TokenStream;
import org.hamcrest.Matcher;
import org.hamcrest.MatcherAssert;
import org.junit.rules.MethodRule;
import org.junit.runners.model.FrameworkMethod;
import org.junit.runners.model.Statement;

abstract class AntlrRule<L extends Lexer, P extends Parser, C> implements MethodRule {
	private P parser;
	private C program;
    private String inputFile;

	@Override
	public Statement apply(final Statement base, final FrameworkMethod method, final Object target) {
		final UseProgram annotation = method.getAnnotation(UseProgram.class);
		if(annotation == null) {
		    return base;
		}

		inputFile = annotation.value();
        try {
			parser = parserFor(inputFile, target.getClass());
			program = parseNow();
			return base;
		} catch (final IllegalStateException|InputMismatchException|IOException e) {
			throw new IllegalStateException("unable to load grammar file " + inputFile, e);
		}
	}

    public String inputFile() {
        return inputFile;
    }

	private P parserFor(final String inputFile, final Class<? extends Object> target) throws IOException {
		final InputStream inputFileStream = target.getResourceAsStream(inputFile);
		if(inputFileStream == null) {
		    throw new IllegalArgumentException("InputFile not found: " + inputFile);
		}

        final L l = makeLexer(new ANTLRInputStream(inputFileStream));
		l.addErrorListener(new BaseErrorListener(){
			@Override
	        public void syntaxError(final Recognizer<?, ?> recognizer, final Object offendingSymbol, final int line, final int charPositionInLine, final String msg, final RecognitionException e) {
	            throw new IllegalStateException("failed to lex at line " + line + " due to " + msg, e);
	        }
		});
	    final CommonTokenStream tokenStream = new CommonTokenStream(l);
		final P p = makeParser(tokenStream);
	    p.addErrorListener(new BaseErrorListener() {
	        @Override
	        public void syntaxError(final Recognizer<?, ?> recognizer, final Object offendingSymbol, final int line, final int charPositionInLine, final String msg, final RecognitionException e) {
	            throw new IllegalStateException("failed to parse at line " + line + " due to " + msg, e);
	        }
	    });
		return p;
	}

	public P parser() {
		return parser;
	}

	public C tree() {
		return program;
	}

	protected abstract P makeParser(final TokenStream tokenStream);

	protected abstract L makeLexer(final CharStream input);

	protected abstract C parseNow();

	public void assertThat(final Matcher<? super C> matcher) {
		MatcherAssert.assertThat(tree(), matcher);
	}
}