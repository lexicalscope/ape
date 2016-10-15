package com.lexicalscope.bl.procedures;

import static com.lexicalscope.MatchersJ8.featureMatcher;
import static com.lexicalscope.bl.procedures.VariableName.asVariableNames;
import static org.hamcrest.Matchers.contains;

import java.util.List;
import java.util.NavigableSet;
import java.util.TreeSet;

import org.hamcrest.Matcher;

import com.lexicalscope.MatchersJ8;
import com.lexicalscope.bl.compiler.Visitors;
import com.lexicalscope.bl.compiler.Visitors.ProcedureVisitor;
import com.lexicalscope.bl.equiv.Expression;
import com.lexicalscope.bl.equiv.Modifies;
import com.lexicalscope.bl.equiv.Statement;

public final class Procedure {
    private final ProcedureName name;
    private final List<VariableName> params;
    private final Block prefix;
    private final Specification specification;
    private final Block statements;

    public Procedure(
            final ProcedureName name,
            final List<VariableName> params,
            final Block prefix,
            final Specification specification,
            final Block statements) {
        this.name = name;
        this.params = params;
        this.prefix = prefix;
        this.specification = specification;
        this.statements = statements;
    }

    public List<VariableName> paramNames() {
        return params;
    }

    public ProcedureName getName() {
        return name;
    }

    public Specification getSpecification() {
        return specification;
    }

    public Block getBlock() {
        return statements;
    }

    public NavigableSet<VariableName> getLocals() {
        final TreeSet<VariableName> result = new TreeSet<>();
        final StatementAdaptor localVariableCollector = new StatementAdaptor() {
            @Override public List<Statement> visitConditionVariable(final ConditionVariableStatement statement) {
                result.add(statement.getLhsVar());
                return super.visitConditionVariable(statement);
            }

            @Override public List<Statement> visitHeapAlloc(final HeapAllocStatement statement) {
                result.add(statement.getLhsVar());
                return super.visitHeapAlloc(statement);
            }

            @Override public List<Statement> visitLocalUpdate(final LocalUpdateStatement statement) {
                result.add(statement.getLhsVar());
                return super.visitLocalUpdate(statement);
            }
        };
        prefix.accept(localVariableCollector);
        this.acceptStatementVisitor(localVariableCollector);

        result.removeAll(params);
        return result;
    }

    public Modifies getModifies() {
        return specification.getModifies();
    }

    public List<Expression> getReads() {
        return specification.getReads();
    }

    public List<Statement> acceptStatementVisitor(final Visitors.StatementVisitor visitor) {
        return statements.accept(visitor);
    }

    public Procedure accept(final ProcedureVisitor visitor) {
        visitor.enterProcedure(this);
        final ProcedureName nameClone = visitor.visitProcedureName(name);
        final List<VariableName> paramsClone = visitor.visitParams(params);
        final Block prefixClone = visitor.visitPrefix(prefix);
        final List<Statement> cloneStatements = visitor.visitBodyStatements(statements);
        final Specification specificationClone = visitor.visitSpecification(specification);
        final Procedure procedure = visitor.visitProcedure(nameClone, paramsClone, prefixClone, specificationClone, new Block(cloneStatements));
        visitor.exitProcedure();
        return procedure;
    }

    public List<VariableName> getParams() {
        return params;
    }

    public Block getStatements() {
        return statements;
    }

    public Block getPrefix() {
        return prefix;
    }

    @Override public String toString() {
        return "Procedure [name=" + name + ", params=" + params + ", prefix=" + prefix + ", specification="
                + specification + ", statements=" + statements + "]";
    }

    @Override public int hashCode() {
        final int prime = 31;
        int result = 1;
        result = prime * result + (name == null ? 0 : name.hashCode());
        result = prime * result + (params == null ? 0 : params.hashCode());
        result = prime * result + (prefix == null ? 0 : prefix.hashCode());
        result = prime * result + (specification == null ? 0 : specification.hashCode());
        result = prime * result + (statements == null ? 0 : statements.hashCode());
        return result;
    }

    @Override public boolean equals(final Object obj) {
        if (this == obj) {
            return true;
        }
        if (obj == null) {
            return false;
        }
        if (getClass() != obj.getClass()) {
            return false;
        }
        final Procedure other = (Procedure) obj;
        if (name == null) {
            if (other.name != null) {
                return false;
            }
        } else if (!name.equals(other.name)) {
            return false;
        }
        if (params == null) {
            if (other.params != null) {
                return false;
            }
        } else if (!params.equals(other.params)) {
            return false;
        }
        if (prefix == null) {
            if (other.prefix != null) {
                return false;
            }
        } else if (!prefix.equals(other.prefix)) {
            return false;
        }
        if (specification == null) {
            if (other.specification != null) {
                return false;
            }
        } else if (!specification.equals(other.specification)) {
            return false;
        }
        if (statements == null) {
            if (other.statements != null) {
                return false;
            }
        } else if (!statements.equals(other.statements)) {
            return false;
        }
        return true;
    }

    public static Matcher<Procedure> reads(final Matcher<Iterable<? extends Expression>> expressionsMatcher) {
        return MatchersJ8.featureMatcher(
            "reads",
            body -> body.getReads(),
            expressionsMatcher
        );
    }

    public static Matcher<Procedure> modifies(final Matcher<? super Modifies> expressionsMatcher) {
        return MatchersJ8.featureMatcher(
            "modifies",
            body -> body.getModifies(),
            expressionsMatcher
        );
    }

    public static Matcher<Procedure> withStatements(final Matcher<Iterable<? extends Statement>> statementsMatcher) {
        return MatchersJ8.featureMatcher(
            "statements",
            body -> body.getBlock(),
            statementsMatcher
        );
    }

    public static Matcher<Procedure> hasProcedureName(final Matcher<String> nameMatcher) {
        return featureMatcher("name", (final Procedure p) -> p.getName().toString(), nameMatcher);
    }

    public static Matcher<Procedure> declaresVariables(final String ... names) {
        return declaresVariables(asVariableNames(names));
    }

    public static Matcher<Procedure> declaresVariables(final List<VariableName> variableNames) {
        return declaresVariables(variableNames.toArray(new VariableName[0]));
    }

    public static Matcher<Procedure> declaresVariables(final VariableName ... variableNames) {
        return featureMatcher(
                "variables",
                (final Procedure p) -> p.getLocals(),
                contains(variableNames));
    }

    public static Matcher<Procedure> hasStatements(final List<Statement> statements) {
        return featureMatcher(
                "statements",
                (final Procedure p) -> p.getStatements(),
                contains(statements.toArray(new Statement[0])));
    }

    public static Matcher<Procedure> hasPrefix(final List<Statement> statements) {
        return featureMatcher(
                "prefix",
                (final Procedure p) -> p.getPrefix(),
                contains(statements.toArray(new Statement[0])));
    }

    public static Matcher<Procedure> hasStatements(final StatementBuilder statements) {
        return hasStatements(statements.mk());
    }

    public static Matcher<Procedure> hasPrefix(final StatementBuilder statements) {
        return hasPrefix(statements.mk());
    }

    public static Matcher<Procedure> locals(final Matcher<Iterable<? extends VariableName>> localsMatcher) {
        return MatchersJ8.featureMatcher(
            "locals",
            procedure -> procedure.getLocals(),
            localsMatcher
        );
    }
}
