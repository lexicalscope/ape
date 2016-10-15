package com.lexicalscope.bl.compiler;

import java.util.List;
import java.util.NavigableMap;
import java.util.function.Function;

import com.lexicalscope.bl.equiv.Expression;
import com.lexicalscope.bl.equiv.Statement;
import com.lexicalscope.bl.procedures.Block;
import com.lexicalscope.bl.procedures.ConditionVariableStatement;
import com.lexicalscope.bl.procedures.ConditionalStatement;
import com.lexicalscope.bl.procedures.FalseExpression;
import com.lexicalscope.bl.procedures.HeapAllocStatement;
import com.lexicalscope.bl.procedures.HeapReadExpression;
import com.lexicalscope.bl.procedures.HeapUpdateStatement;
import com.lexicalscope.bl.procedures.LocalUpdateStatement;
import com.lexicalscope.bl.procedures.Multiversion;
import com.lexicalscope.bl.procedures.NullValueExpression;
import com.lexicalscope.bl.procedures.PredicatedStatement;
import com.lexicalscope.bl.procedures.Procedure;
import com.lexicalscope.bl.procedures.ProcedureCallStatement;
import com.lexicalscope.bl.procedures.ProcedureName;
import com.lexicalscope.bl.procedures.Program;
import com.lexicalscope.bl.procedures.Specification;
import com.lexicalscope.bl.procedures.TrueExpression;
import com.lexicalscope.bl.procedures.VariableName;
import com.lexicalscope.bl.procedures.Version;

public class Visitors {
    public interface ProgramVisitor {
        void enterMultiversion(Multiversion multiversion);
        Program visit(Version version, Program program);
        Multiversion visitMultiversion(NavigableMap<Version, Program> programs);
        void exitMultiversion();
    }

    public interface ProcedureVisitor {
        void enterProcedure(Procedure procedure);
        ProcedureName visitProcedureName(ProcedureName name);
        List<VariableName> visitParams(List<VariableName> params);
        Block visitPrefix(Block prefix);
        Specification visitSpecification(Specification specification);
        List<Statement> visitBodyStatements(Block statements);
        Procedure visitProcedure(
                ProcedureName name,
                List<VariableName> params,
                Block prefix,
                Specification specification,
                Block statements);
        void exitProcedure();
    }

    public interface StatementVisitor extends Function<Statement, List<Statement>> {
        List<Statement> visitConditional(ConditionalStatement statement);
        List<Statement> visitHeapAlloc(HeapAllocStatement statement);
        List<Statement> visitLocalUpdate(LocalUpdateStatement statement);
        List<Statement> visitProcedureCall(ProcedureCallStatement statement);
        List<Statement> visitHeapUpdate(HeapUpdateStatement statement);
        List<Statement> visitConditionVariable(ConditionVariableStatement statement);
        List<Statement> visitPredicated(PredicatedStatement statement);
        List<Statement> visitBlock(Block block);
    }

    public interface ExpressionVisitor {
        Expression visitAnd(Expression lhs, Expression rhs);
        Expression visitEqualTo(Expression lhs, Expression rhs);
        Expression visitHeapRead(HeapReadExpression heapReadExpression);
        Expression visitLocalRead(VariableName local);
        Expression notEqualTo(Expression lhs, Expression rhs);
        Expression not(Expression expression);
        Expression nullValue(NullValueExpression nullValueExpression);
        Expression trueValue(TrueExpression trueExpression);
        Expression falseValue(FalseExpression falseExpression);
    }
}
