package com.lexicalscope.bl.equiv;

import static com.lexicalscope.MatchersJ8.containsMatching;
import static com.lexicalscope.bl.equiv.ProcedurePair.*;
import static com.lexicalscope.bl.equiv.ProcedurePairsCollector.procedurePairs;
import static com.lexicalscope.bl.procedures.Procedure.*;
import static com.lexicalscope.bl.procedures.StatementBuilder.statements;
import static com.lexicalscope.bl.procedures.VariableName.refVariableName;
import static org.hamcrest.MatcherAssert.assertThat;
import static org.hamcrest.Matchers.equalTo;

import java.io.IOException;

import org.hamcrest.Matcher;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.TemporaryFolder;

import com.lexicalscope.bl.parser.BlAntlrRule;
import com.lexicalscope.bl.parser.UseProgram;
import com.lexicalscope.bl.procedures.AnyModifies;
import com.lexicalscope.bl.procedures.EmptyModifies;
import com.lexicalscope.bl.procedures.EqualToExpression;
import com.lexicalscope.bl.procedures.HeapAllocStatement;
import com.lexicalscope.bl.procedures.HeapReadExpression;
import com.lexicalscope.bl.procedures.HeapUpdateStatement;
import com.lexicalscope.bl.procedures.LocalReadExpression;
import com.lexicalscope.bl.procedures.LocalUpdateStatement;
import com.lexicalscope.bl.procedures.ModifiesSet;
import com.lexicalscope.bl.procedures.Procedure;
import com.lexicalscope.bl.procedures.ProcedureCallStatement;

public class TestProcedurePairing {
    @Rule public TemporaryFolder folder = new TemporaryFolder();
    @Rule public BlAntlrRule<ProcedurePairs> p = new BlAntlrRule<ProcedurePairs>() {
        @Override protected ProcedurePairs parseNow() {
            return procedurePairs(parser().multiversion());
        }
    };

    @Test @UseProgram("ProcedurePairs001.bl") public void proceduresArePaired() throws IOException, InterruptedException {
        assertThat(p.tree(),
                containsMatching(pairCalled("FirstProcedure"), pairCalled("SecondProcedure"), pairCalled("ThirdProcedure")));
    }

    @Test @UseProgram("ProcedurePairs002.bl") public void localsAreFound() throws IOException, InterruptedException {
        assertThat(p.tree(),
                containsMatching(ver0(
                        locals(containsMatching(
                                equalTo(refVariableName("$t#0")),
                                equalTo(refVariableName("s")),
                                equalTo(refVariableName("t")))))));
    }

    @Test @UseProgram("ProcedurePairs003.bl") public void statementsAreFound() throws IOException, InterruptedException {
        assertThat(p.tree(),
                containsMatching(ver0(withStatements(containsMatching(
                        Statement.class,
                        equalTo(new LocalUpdateStatement("t", "x")),
                        equalTo(new HeapUpdateStatement("t", "f", "x")),
                        equalTo(new LocalUpdateStatement("$t#0", new HeapReadExpression("x", "f"))),
                        equalTo(new HeapUpdateStatement("t", "f", "$t#0")),
                        equalTo(new LocalUpdateStatement("$t#1", new HeapReadExpression("x", "f"))),
                        equalTo(new LocalUpdateStatement("t", new LocalReadExpression("$t#1"))),
                        equalTo(new HeapAllocStatement("$t#2")),
                        equalTo(new LocalUpdateStatement("t", new LocalReadExpression("$t#2"))),
                        equalTo(new ProcedureCallStatement("Foo", "t"))
                        )))));
    }

    @Test @UseProgram("ProcedurePairs004.bl") public void modifiesIsFound() throws IOException, InterruptedException {
        assertThat(p.tree(),
                containsMatching(ver0(modifies(containsMatching(
                        Expression.class,
                        equalTo(new LocalReadExpression("x"))
                        )))));
    }

    @Test @UseProgram("ProcedurePairs005.bl") public void readsIsFound() throws IOException, InterruptedException {
        assertThat(p.tree(),
                containsMatching(ver0(reads(containsMatching(
                        Expression.class,
                        equalTo(new LocalReadExpression("x"))
                        )))));
    }

    @Test @UseProgram("ProcedurePairs006.bl") public void newsCanBeCounted() throws IOException, InterruptedException {
//        assertThat(procedurePairs(p.tree()),
//                containsMatching(ver1(newsCount(equalTo(1))), ver1(newsCount(equalTo(4)))));
    }

    @Test @UseProgram("ProcedurePairs007.bl") public void conditionalStatementsAreFound() throws IOException, InterruptedException {
        System.out.println(p.tree());
        assertVer0Matches(withStatements(containsMatching(
                        Statement.class,
                        equalTo(new HeapAllocStatement("$t#0")),
                        equalTo(new LocalUpdateStatement("t", new LocalReadExpression("$t#0"))),
                        equalTo(statements().conditional(new EqualToExpression("x", "null")).
                                    then(statements().heapUpdate("x", "f", "t")).
                                    elsethen(statements().heapUpdate("y", "f", "t")).first())
                        )));
    }

    @Test @UseProgram("ProcedurePairs008.bl") public void emptyModifiesIsFound() throws IOException, InterruptedException {
        assertVer0Matches(modifies(equalTo(new EmptyModifies())));
    }


    @Test @UseProgram("ProcedurePairs009.bl") public void noModifiesIsFound() throws IOException, InterruptedException {
        assertVer0Matches(modifies(equalTo(new AnyModifies())));
    }


    @Test @UseProgram("ProcedurePairs010.bl") public void singletonModifiesIsFound() throws IOException, InterruptedException {
        assertVer0Matches(modifies(equalTo(new ModifiesSet(new LocalReadExpression("x")))));
    }

    @Test @UseProgram("ProcedurePairs011.bl") public void setExpressionIsFound() throws IOException, InterruptedException {
        assertVer0Matches(modifies(equalTo(new ModifiesSet(new LocalReadExpression("x"), new LocalReadExpression("y")))));
    }

    void assertVer0Matches(final Matcher<Procedure> ver0Matcher) {
        assertThat(p.tree(),
                containsMatching(ver0(ver0Matcher)));
    }
}
