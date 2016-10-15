package com.lexicalscope.bl.equiv;

import static com.lexicalscope.bl.equiv.PathFactory.path;
import static com.lexicalscope.bl.procedures.Type.Ref;
import static com.lexicalscope.bl.procedures.VariableName.variableName;

import java.util.ArrayList;
import java.util.List;

import org.antlr.v4.runtime.tree.ParseTreeWalker;

import com.google.common.base.Supplier;
import com.lexicalscope.bl.compiler.VariableNameGenerator;
import com.lexicalscope.bl.parser.BlBaseListener;
import com.lexicalscope.bl.parser.BlBaseVisitor;
import com.lexicalscope.bl.parser.BlParser.AllocRhsContext;
import com.lexicalscope.bl.parser.BlParser.AssignmentContext;
import com.lexicalscope.bl.parser.BlParser.BlockContext;
import com.lexicalscope.bl.parser.BlParser.ConditionalContext;
import com.lexicalscope.bl.parser.BlParser.LocalLhsContext;
import com.lexicalscope.bl.parser.BlParser.LocalRhsContext;
import com.lexicalscope.bl.parser.BlParser.LocalRootedLhsContext;
import com.lexicalscope.bl.parser.BlParser.PathRhsContext;
import com.lexicalscope.bl.parser.BlParser.PathRootedLhsContext;
import com.lexicalscope.bl.parser.BlParser.ProcedureCallContext;
import com.lexicalscope.bl.procedures.Block;
import com.lexicalscope.bl.procedures.ConditionalStatement;
import com.lexicalscope.bl.procedures.HeapAllocStatement;
import com.lexicalscope.bl.procedures.HeapReadExpression;
import com.lexicalscope.bl.procedures.HeapUpdateStatement;
import com.lexicalscope.bl.procedures.LocalReadExpression;
import com.lexicalscope.bl.procedures.LocalUpdateStatement;
import com.lexicalscope.bl.procedures.ProcedureCallStatement;
import com.lexicalscope.bl.procedures.VariableName;

public final class StatementCollector extends BlBaseVisitor<Void> {
    private final List<Statement> result;
    private final StatementCollectionStrategy statementStrategy;
    private final VariableNameGenerator temporaryGenerator;

    public interface StatementCollectionStrategy {
        void conditional(StatementCollector statementCollector, ConditionalContext ctx);
    }

    public static class StatementTreeStrategy implements StatementCollectionStrategy {
        @Override public void conditional(final StatementCollector statementCollector, final ConditionalContext ctx) {
            statementCollector.result.add(new ConditionalStatement(
                    ExpressionFactory.boolExpression(ctx.bexpression()),
                    new StatementCollector().collect(ctx.then),
                    new StatementCollector().collect(ctx.elsethen)));
        }
    }

    public StatementCollector() {
        this(ArrayList::new);
    }

    public StatementCollector(final Supplier<List<Statement>> supplier) {
        this(new StatementTreeStrategy(), supplier);
    }

    public StatementCollector(final StatementCollectionStrategy statementStrategy) {
        this(statementStrategy, ArrayList::new);
    }

    public StatementCollector(final StatementCollectionStrategy statementStrategy, final Supplier<List<Statement>> supplier) {
        this.statementStrategy = statementStrategy;
        result = supplier.get();
        temporaryGenerator = new VariableNameGenerator("t", Ref);
    }

    public List<Statement> getResult() {
        return result;
    }

    @Override public Void visitAssignment(final AssignmentContext ctx) {
        final VariableName[] rhsVar = new VariableName[1];

        new ParseTreeWalker().walk(new BlBaseListener(){
            @Override public void enterPathRhs(final PathRhsContext ctx) {
                final VariableName temp = temporaryGenerator.next();
                result.add(new LocalUpdateStatement(temp, new HeapReadExpression(path(ctx.path()))));
                rhsVar[0] = temp;
                super.enterPathRhs(ctx);
            }

            @Override public void enterLocalRhs(final LocalRhsContext ctx) {
                rhsVar[0] = variableName(ctx.local.getText(), Ref);
                super.enterLocalRhs(ctx);
            }

            @Override public void enterAllocRhs(final AllocRhsContext ctx) {
                final VariableName temp = temporaryGenerator.next();
                result.add(new HeapAllocStatement(temp));
                rhsVar[0] = temp;
                super.enterAllocRhs(ctx);
            }
        }, ctx.rhs);

        new ParseTreeWalker().walk(new BlBaseListener(){
            @Override public void enterPathRootedLhs(final PathRootedLhsContext ctx) {
                final VariableName temp = temporaryGenerator.next();
                result.add(new LocalUpdateStatement(temp, new HeapReadExpression(path(ctx.path()))));
                result.add(new HeapUpdateStatement(temp, ctx.field.getText(), rhsVar[0]));
                super.enterPathRootedLhs(ctx);
            }

            @Override public void enterLocalRootedLhs(final LocalRootedLhsContext ctx) {
                result.add(new HeapUpdateStatement(variableName(ctx.local.getText(), Ref), ctx.field.getText(), rhsVar[0]));
                super.enterLocalRootedLhs(ctx);
            }

            @Override public void enterLocalLhs(final LocalLhsContext ctx) {
                result.add(new LocalUpdateStatement(variableName(ctx.local.getText(), Ref), new LocalReadExpression(rhsVar[0])));
                super.enterLocalLhs(ctx);
            }
        }, ctx.lhs);
        return null;
    }

    @Override public Void visitProcedureCall(final ProcedureCallContext ctx) {
        result.add(new ProcedureCallStatement(ctx));
        return null;
    }

    @Override public Void visitConditional(final ConditionalContext ctx) {
        statementStrategy.conditional(this, ctx);
        return null;
    }

    public Block collect(final BlockContext block) {
        if(block != null) {
            this.visit(block);
        }
        return new Block(getResult());
    }
}