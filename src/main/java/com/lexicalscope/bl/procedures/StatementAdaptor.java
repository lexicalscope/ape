package com.lexicalscope.bl.procedures;

import static com.lexicalscope.Jc.$;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.NavigableMap;

import com.lexicalscope.bl.compiler.Visitors;
import com.lexicalscope.bl.equiv.Expression;
import com.lexicalscope.bl.equiv.Statement;

public class StatementAdaptor implements
    Visitors.StatementVisitor,
    Visitors.ProcedureVisitor,
    Visitors.ProgramVisitor,
    Visitors.ExpressionVisitor {

    protected final List<Statement> singleton(final Statement s) {
        return Collections.singletonList(s);
    }

    protected List<Statement> decorate(final Statement s) {
        return singleton(s);
    }

    protected Expression cloneExpression(final Expression condition) {
        return condition.accept(this);
    }

    protected VariableName cloneVariable(final VariableName var) {
        return var;
    }

    protected Path clonePath(final Path path) {
        return new Path(cloneVariable(path.getLocal()), path.getFields());
    }

    @Override public void enterMultiversion(final Multiversion multiversion) {
        // nothing to do here
    }

    @Override public Multiversion visitMultiversion(final NavigableMap<Version, Program> programs) {
        return new Multiversion(programs);
    }

    @Override public void exitMultiversion() {
        // nothing to do here
    }

    @Override public Program visit(final Version version, final Program program) {
        return new Program(program.accept(this));
    }

    @Override public void enterProcedure(final Procedure procedure) {
        // nothing to do here
    }

    @Override public void exitProcedure() {
        // nothing to do here
    }

    @Override public ProcedureName visitProcedureName(final ProcedureName name) {
        return name;
    }

    @Override public List<VariableName> visitParams(final List<VariableName> params) {
        return params;
    }

    @Override public Block visitPrefix(final Block prefix) {
        return new Block(cloneBlockStatements(prefix));
    }

    @Override public Procedure visitProcedure(
            final ProcedureName name,
            final List<VariableName> params,
            final Block prefix,
            final Specification specification,
            final Block statements) {
        return new Procedure(name, params, prefix, specification, statements);
    }

    @Override public List<Statement> visitBodyStatements(final Block statements) {
        return cloneBlockStatements(statements);
    }

    @Override public List<Statement> visitBlock(final Block block) {
        return decorate(new Block(cloneBlockStatements(block)));
    }

    public List<Statement> cloneBlockStatements(final Block block) {
        final List<Statement> statements = new ArrayList<>();
        for (final Statement statement : block.getStatements()) {
            statements.addAll(statement.accept(this));
        }
        return statements;
    }

    @Override public List<Statement> visitConditional(final ConditionalStatement statement) {
        return decorate(
                new ConditionalStatement(
                    cloneExpression(statement.getCondition()),
                    cloneBlockStatements(statement.getThenStatements()),
                    cloneBlockStatements(statement.getElseStatements())));
    }

    @Override public List<Statement> visitHeapAlloc(final HeapAllocStatement statement) {
        return decorate(new HeapAllocStatement(cloneVariable(statement.getLhsVar())));
    }

    @Override public List<Statement> visitLocalUpdate(final LocalUpdateStatement statement) {
        return decorate(new LocalUpdateStatement(
                cloneVariable(statement.getLhsVar()),
                cloneExpression(statement.getExpression())));
    }

    @Override public List<Statement> visitProcedureCall(final ProcedureCallStatement statement) {
        return decorate(new ProcedureCallStatement(
                statement.getName(),
                $(statement.getParams()).map(v -> cloneVariable(v))._$()));
    }

    @Override public List<Statement> visitHeapUpdate(final HeapUpdateStatement statement) {
        return decorate(new HeapUpdateStatement(
                cloneVariable(statement.getLhs()),
                statement.getField(),
                cloneVariable(statement.getRhs())));
    }

    @Override public List<Statement> visitConditionVariable(final ConditionVariableStatement statement) {
        return decorate(new ConditionVariableStatement(
                cloneVariable(statement.getLhsVar()),
                statement.getExpression().accept(this)));
    }

    @Override public List<Statement> visitPredicated(final PredicatedStatement statement) {
        return decorate(new PredicatedStatement(
                cloneExpression(statement.getCondition()),
                cloneBlockStatements(statement.getPredicatedStatement())));
    }

    @Override public List<Statement> apply(final Statement statement) {
        return statement.accept(this);
    }

    @Override public Expression visitAnd(final Expression lhs, final Expression rhs) {
        return new AndExpression(lhs.accept(this), rhs.accept(this));
    }

    @Override public Expression visitEqualTo(final Expression lhs, final Expression rhs) {
        return new EqualToExpression(lhs.accept(this), rhs.accept(this));
    }

    @Override public Expression visitHeapRead(final HeapReadExpression heapReadExpression) {
        return new HeapReadExpression(clonePath(heapReadExpression.getPath()));
    }

    @Override public Expression visitLocalRead(final VariableName local) {
        return new LocalReadExpression(cloneVariable(local));
    }

    @Override public Expression notEqualTo(final Expression lhs, final Expression rhs) {
        return new NotEqualToExpression(lhs.accept(this), rhs.accept(this));
    }

    @Override public Expression not(final Expression expression) {
        return new NotExpression(expression.accept(this));
    }

    @Override public Expression nullValue(final NullValueExpression nullValueExpression) {
        return nullValueExpression;
    }

    @Override public Expression trueValue(final TrueExpression trueExpression) {
        return trueExpression;
    }

    @Override public Expression falseValue(final FalseExpression falseExpression) {
        return falseExpression;
    }

    @Override public Specification visitSpecification(final Specification specification) {
        return new Specification(specification.getReads(), specification.getModifies());
    }
}
