package com.lexicalscope.bl.parser;

import static com.lexicalscope.Jc.$;
import static org.hamcrest.core.CombinableMatcher.both;

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;

import org.antlr.v4.runtime.CharStream;
import org.antlr.v4.runtime.ParserRuleContext;
import org.antlr.v4.runtime.TokenStream;
import org.antlr.v4.runtime.tree.ParseTree;
import org.antlr.v4.runtime.tree.pattern.ParseTreeMatch;
import org.hamcrest.Description;
import org.hamcrest.Matcher;
import org.hamcrest.Matchers;
import org.hamcrest.TypeSafeMatcher;

import com.lexicalscope.bl.parser.BlParser.ParamContext;
import com.lexicalscope.bl.parser.BlParser.ParamDeclContext;
import com.lexicalscope.bl.parser.BlParser.ProcedureContext;
import com.lexicalscope.bl.parser.BlParser.ProgramContext;

public abstract class BlAntlrRule<C /*extends ParserRuleContext*/> extends AntlrRule<BlLexer, BlParser, C> {
    @Override
    protected BlLexer makeLexer(final CharStream input) {
        return new BlLexer(input);
    }

    @Override
    protected BlParser makeParser(final TokenStream tokenStream) {
        return new BlParser(tokenStream);
    }

    public String boogieFile() {
        return inputFile().replaceFirst(".bl$", ".bpl");
    }

//    @Override
//    protected C parseNow() {
//        return parser().program();
//    }

    public Matcher<ParserRuleContext> hasProcedureContextCalled(final String procedureName) {
        return hasProcedureContextCalled(procedureName, procedureCalled(procedureName));
    }

    public Matcher<ParserRuleContext> hasProcedureContextCalled(final String procedureName,
            final Matcher<? super ParserRuleContext> procedureMatcher) {
        return hasProcedures(oneProcedureCalled(procedureName, procedureMatcher));
    }

    public Matcher<ParserRuleContext> hasProcedures(
            final Matcher<Collection<? extends ParseTreeMatch>> proceduresMatcher) {
        return new AntlrPatternFeatureMatcher(
                parser(),
                "/program/*",
                "procedure <IDENTIFIER> <paramsDecl> <block>",
                BlParser.RULE_procedure,
                proceduresMatcher);
    }

    @SafeVarargs
    public final Matcher<? super ProgramContext> hasProcedures(final Matcher<? super ParserRuleContext>... procedures) {
        final List<Matcher<? super ParserRuleContext>> matchers = new ArrayList<>();
        for (final Matcher<? super ParserRuleContext> matcher : procedures) {
            matchers.add(matcher);
        }
        return hasProcedures(resultsMatching(Matchers.<ParserRuleContext> contains(matchers)));
    }

    Matcher<Collection<? extends ParseTreeMatch>> oneProcedureCalled(
            final String procedureName,
            final Matcher<? super ParserRuleContext> procedureMatcher) {
        return oneResultMatching(both(procedureCalled(procedureName)).and(procedureMatcher));
    }

    public Matcher<ParserRuleContext> hasParameterDecls(
            final Matcher<? super Collection<? extends ParserRuleContext>> paramMatcher) {
        return new AntlrPatternFeatureMatcher(
                parser(),
                "//*",
                "<paramDecl>",
                BlParser.RULE_paramDecl,
                resultsMatching(paramMatcher));
    }

    public Matcher<ParserRuleContext> hasParameters(
            final Matcher<? super Collection<? extends ParseTreeMatch>> paramMatcher) {
        return new AntlrPatternFeatureMatcher(parser(), "//*", "<param>", BlParser.RULE_param, paramMatcher);
    }

    public Matcher<ParserRuleContext> containingCallOf(
            final String procedureName,
            final Matcher<? super ParserRuleContext> callMatcher) {
        return new AntlrPatternFeatureMatcher(
                parser(),
                "//*",
                String.format("call %s <params>;", procedureName),
                BlParser.RULE_statement,
                oneResultMatching(callMatcher));
    }

    public Matcher<ParserRuleContext> withParameters(final String... parameters) {
        final List<Matcher<? super ParseTreeMatch>> matchers = new ArrayList<>();
        for (final String parameter : parameters) {
            matchers.add(parameter(parameter));
        }
        return hasParameters(Matchers.<ParseTreeMatch> contains(matchers));
    }

    public Matcher<ParserRuleContext> withDeclaredParameters(final String... parameters) {
        final List<Matcher<? super ParserRuleContext>> matchers = new ArrayList<>();
        for (final String parameter : parameters) {
            matchers.add(parameterDecl(parameter));
        }
        return hasParameterDecls(Matchers.<ParserRuleContext> contains(matchers));
    }

    private Matcher<Collection<? extends ParseTreeMatch>> oneResultMatching(
            final Matcher<? super ParserRuleContext> submatcher) {
        return new TypeSafeMatcher<Collection<? extends ParseTreeMatch>>() {
            @Override
            public void describeTo(final Description description) {
                description.appendText("one result matching ").appendDescriptionOf(submatcher);
            }

            @Override
            protected void describeMismatchSafely(
                    final Collection<? extends ParseTreeMatch> item,
                    final Description mismatchDescription) {
                if (item.size() != 1) {
                    mismatchDescription.appendText("expected 1 item but got ").appendValue(item.size());
                } else {
                    submatcher.describeMismatch(tree(item), mismatchDescription);
                }
            }

            @Override
            protected boolean matchesSafely(final Collection<? extends ParseTreeMatch> item) {
                return item.size() == 1 && submatcher.matches(tree(item));
            }

            private ParseTree tree(final Collection<? extends ParseTreeMatch> item) {
                return item.iterator().next().getTree();
            }
        };
    }

    private Matcher<Collection<? extends ParseTreeMatch>> resultsMatching(
            final Matcher<? super Collection<? extends ParserRuleContext>> submatcher) {
        return new TypeSafeMatcher<Collection<? extends ParseTreeMatch>>() {
            @Override
            public void describeTo(final Description description) {
                description.appendText("one result matching ").appendDescriptionOf(submatcher);
            }

            @Override
            protected void describeMismatchSafely(final Collection<? extends ParseTreeMatch> item,
                    final Description mismatchDescription) {
                submatcher.describeMismatch(trees(item), mismatchDescription);
            }

            @Override
            protected boolean matchesSafely(final Collection<? extends ParseTreeMatch> item) {
                return submatcher.matches(trees(item));
            }

            private List<ParseTree> trees(final Collection<? extends ParseTreeMatch> item) {
                return $(item).map(p -> p.getTree())._$();
            }
        };
    }

    public Matcher<? super ParseTreeMatch> parameter(final String parameter) {
        return new TypeSafeMatcher<ParseTreeMatch>() {
            @Override
            protected void describeMismatchSafely(final ParseTreeMatch item, final Description mismatchDescription) {
                mismatchDescription.appendText("parameters ").appendValue(item.getTree().toStringTree(parser()));
            }

            @Override
            public void describeTo(final Description description) {
                description.appendText("parameter ").appendValue(parameter);
            }

            @Override
            protected boolean matchesSafely(final ParseTreeMatch item) {
                if (item.get("param") instanceof ParamContext) {
                    return ((ParamContext) item.get("param")).IDENTIFIER().getText().equals(parameter);
                }
                return false;
            }
        };
    }

    public Matcher<? super ParserRuleContext> parameterDecl(final String parameter) {
        return new TypeSafeMatcher<ParserRuleContext>() {
            @Override
            protected void describeMismatchSafely(final ParserRuleContext item, final Description mismatchDescription) {
                mismatchDescription.appendText("declared parameters ").appendValue(item.toStringTree(parser()));
            }

            @Override
            public void describeTo(final Description description) {
                description.appendText("parameter declaration ").appendValue(parameter);
            }

            @Override
            protected boolean matchesSafely(final ParserRuleContext item) {
                if (item instanceof ParserRuleContext) {
                    // .get("paramDecl")
                    return ((ParamDeclContext) item).IDENTIFIER().getText().equals(parameter);
                }
                return false;
            }
        };
    }

    public Matcher<ParserRuleContext> procedureCalled(final String procedureName) {
        return new TypeSafeMatcher<ParserRuleContext>() {
            @Override
            protected void describeMismatchSafely(final ParserRuleContext item, final Description mismatchDescription) {
                mismatchDescription.appendText("procedure ").appendValue(item.toStringTree(parser()));
            }

            @Override
            public void describeTo(final Description description) {
                description.appendText("procedure called ").appendValue(procedureName);
            }

            @Override
            protected boolean matchesSafely(final ParserRuleContext item) {
                if (item instanceof ProcedureContext) {
                    return ((ProcedureContext) item).IDENTIFIER().getText().equals(procedureName);
                }
                return false;
            }
        };
    }
}