package com.lexicalscope.bl.parser;

import java.util.List;

import org.antlr.v4.runtime.Parser;
import org.antlr.v4.runtime.ParserRuleContext;
import org.antlr.v4.runtime.misc.Interval;
import org.antlr.v4.runtime.tree.ParseTree;
import org.antlr.v4.runtime.tree.pattern.ParseTreeMatch;
import org.antlr.v4.runtime.tree.pattern.ParseTreePattern;
import org.hamcrest.Description;
import org.hamcrest.Matcher;
import org.hamcrest.TypeSafeMatcher;

public class AntlrPatternFeatureMatcher extends TypeSafeMatcher<ParserRuleContext>
{
	private final String pattern;
	private final ParseTreePattern compiledPattern;
	private final String xpath;
	private final Matcher<? super List<ParseTreeMatch>> submatcher;

	public AntlrPatternFeatureMatcher(final Parser parser, final String xpath, final String pattern, final int patternRuleIndex, final Matcher<? super List<ParseTreeMatch>> submatcher) {
		this.pattern = pattern;
		this.submatcher = submatcher;
		this.compiledPattern = parser.compileParseTreePattern(pattern, patternRuleIndex);
		this.xpath = xpath;
	}

	@Override
	public void describeTo(final Description description) {
	    description.appendText("find ").appendValue(pattern).appendText(" and match ").appendDescriptionOf(submatcher);
	}

	@Override
	protected void describeMismatchSafely(final ParserRuleContext item, final Description mismatchDescription) {
		final String programText = item.start.getInputStream().getText(new Interval(item.start.getStartIndex(),item.stop.getStopIndex()));
		mismatchDescription.appendText("encountered program text: ").appendValue(programText).appendText(" ");
		submatcher.describeMismatch(featureValueOf(item), mismatchDescription);
	}

	@Override
	protected boolean matchesSafely(final ParserRuleContext actual) {
		return submatcher.matches(featureValueOf(actual));
	}

	private List<ParseTreeMatch> featureValueOf(final ParseTree actual) {
		return compiledPattern.findAll(actual, xpath);
	}
}