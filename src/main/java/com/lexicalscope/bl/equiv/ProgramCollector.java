package com.lexicalscope.bl.equiv;

import static com.lexicalscope.Jc.$;
import static com.lexicalscope.bl.procedures.ProcedureName.procedureName;
import static com.lexicalscope.bl.procedures.Specification.specification;
import static com.lexicalscope.bl.procedures.Type.Ref;
import static com.lexicalscope.bl.procedures.VariableName.variableName;

import java.util.List;
import java.util.NavigableMap;
import java.util.TreeMap;

import org.antlr.v4.runtime.ParserRuleContext;
import org.antlr.v4.runtime.tree.ParseTreeWalker;

import com.lexicalscope.bl.parser.BlBaseListener;
import com.lexicalscope.bl.parser.BlParser.MultiversionContext;
import com.lexicalscope.bl.parser.BlParser.ProcedureContext;
import com.lexicalscope.bl.parser.BlParser.VersionContext;
import com.lexicalscope.bl.procedures.Block;
import com.lexicalscope.bl.procedures.Multiversion;
import com.lexicalscope.bl.procedures.Procedure;
import com.lexicalscope.bl.procedures.ProcedureName;
import com.lexicalscope.bl.procedures.Program;
import com.lexicalscope.bl.procedures.Version;

public class ProgramCollector {
    private interface CollectorState {
        CollectorState enterVersion(VersionContext ctx);

        void procedure(String name, ProcedureContext ctx);

        CollectorState exitVersion(VersionContext ctx);
    }


    private static class ProcedureCollector extends BlBaseListener {
        private final class InitialState implements CollectorState {
            @Override public CollectorState enterVersion(final VersionContext ctx) {
                return new CollectingState(ctx);
            }

            @Override public void procedure(final String name, final ProcedureContext ctx) {
                throw new IllegalStateException("procedure encountered outside version " + formatPosition(ctx));
            }

            @Override public CollectorState exitVersion(final VersionContext ctx) {
                throw new IllegalStateException("exit version before enter version " + formatPosition(ctx));
            }
        }

        private final class CollectingState implements CollectorState {
            private final NavigableMap<ProcedureName, Procedure> procedures = new TreeMap<>();
            private final Version version;

            public CollectingState(final VersionContext ctx) {
                version = new Version(programs.size());
            }

            @Override public CollectorState enterVersion(final VersionContext ctx) {
                throw new IllegalStateException("nested versions unsupported " + formatPosition(ctx));
            }

            @Override public void procedure(final String name, final ProcedureContext ctx) {
                final ProcedureName procedureName = procedureName(name);
                if(procedures.containsKey(procedureName)) {
                    throw new IllegalStateException("too many declarations of " + name + " " + formatPosition(ctx));
                }
                procedures.put(procedureName, mkProcedure(procedureName, ctx));
            }

            @Override public CollectorState exitVersion(final VersionContext ctx) {
                programs.put(version, new Program(procedures));
                return new InitialState();
            }

            private Procedure mkProcedure(final ProcedureName name, final ProcedureContext ctx) {
                return new Procedure(
                        name,
                        $(paramNames(ctx)).map(n -> variableName(n, Ref))._$(),
                        new Block(),
                        specification(ctx.specification()),
                        new StatementCollector().collect(ctx.block()));
            }

            private List<String> paramNames(final ProcedureContext procedure) {
                return $(procedure.paramsDecl().vars).map(p -> p.IDENTIFIER().getText())._$();
            }
        }

        private final NavigableMap<Version, Program> programs = new TreeMap<>();
        private CollectorState state = new InitialState();

        @Override public void enterVersion(final VersionContext ctx) {
            state = state.enterVersion(ctx);
        }

        @Override public void exitVersion(final VersionContext ctx) {
            state = state.exitVersion(ctx);
        }

        @Override public void enterProcedure(final ProcedureContext ctx) {
            state.procedure(ctx.IDENTIFIER().getText(), ctx);
        }

        public NavigableMap<Version, Program> programs() {
            return programs;
        }
    }

    public static Multiversion programs(final MultiversionContext tree) {
        final ProcedureCollector procedureCollector = new ProcedureCollector();
        final ParseTreeWalker walker = new ParseTreeWalker();
        walker.walk(procedureCollector, tree);
        return new Multiversion(procedureCollector.programs());
    }

    static String formatPosition(final ParserRuleContext ctx) {
        return String.format("@%s:%s-%s:%s",
                ctx.getStart().getLine(),
                ctx.getStart().getCharPositionInLine(),
                ctx.getStop().getLine(),
                ctx.getStop().getCharPositionInLine());
    }
}
