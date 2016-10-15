package com.lexicalscope.bl.compiler;

import static com.lexicalscope.MatchersJ8.matcher;
import static com.lexicalscope.bl.procedures.Type.Ref;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;

import org.hamcrest.Matcher;

import com.lexicalscope.bl.equiv.Statement;
import com.lexicalscope.bl.procedures.Block;
import com.lexicalscope.bl.procedures.HeapAllocStatement;
import com.lexicalscope.bl.procedures.LocalReadExpression;
import com.lexicalscope.bl.procedures.LocalUpdateStatement;
import com.lexicalscope.bl.procedures.Multiversion;
import com.lexicalscope.bl.procedures.Procedure;
import com.lexicalscope.bl.procedures.ProcedureName;
import com.lexicalscope.bl.procedures.Specification;
import com.lexicalscope.bl.procedures.StatementAdaptor;
import com.lexicalscope.bl.procedures.StatementBuilder;
import com.lexicalscope.bl.procedures.VariableName;

/**
 * Its going to find all the allocations sites, and move the allocations up to the front of the
 * procedure. The original allocation statements are changed to assignment statements.
 */
public class AllocateUpfront {
    public static final class ReplaceAllocationWithAssignment extends StatementAdaptor {
        private Multiversion multiversion;
        private List<VariableName> allocationVariables;
        private Iterator<VariableName> remainingAllocationVariables;

        @Override public void enterMultiversion(final Multiversion multiversion) {
            super.enterMultiversion(multiversion);
            this.multiversion = multiversion;
        }

        @Override public void exitMultiversion() {
            this.multiversion = null;
            super.exitMultiversion();
        }

        @Override public void enterProcedure(final Procedure procedure) {
            super.enterProcedure(procedure);

            int allocationCount = 0;
            for (final Procedure procedureVersion : multiversion.versions(procedure.getName())) {
                allocationCount = Math.max(allocationCount, countAllocationSites(procedureVersion));
            }

            allocationVariables = new VariableNameGenerator("a", Ref).next(allocationCount);
            remainingAllocationVariables = allocationVariables.iterator();
        }

        @Override public void exitProcedure() {
            allocationVariables = null;
            remainingAllocationVariables = null;
            super.exitProcedure();
        }

        @Override public List<Statement> visitHeapAlloc(final HeapAllocStatement statement) {
            return singleton(
                    new LocalUpdateStatement(
                            statement.getLhsVar(),
                            new LocalReadExpression(remainingAllocationVariables.next())));
        }

        @Override public Procedure visitProcedure(
                final ProcedureName name,
                final List<VariableName> params,
                final Block prefix,
                final Specification specification,
                final Block bodyStatements) {

            final StatementBuilder statements = StatementBuilder.statements();
            for (final VariableName allocation : allocationVariables) {
                statements.heapAllocationStatement(allocation);
            }
            final List<Statement> prefixStatements = new ArrayList<>(prefix.getStatements());
            prefixStatements.addAll(statements.mk());

            return super.visitProcedure(name, params, new Block(prefixStatements), specification, bodyStatements);
        }
    }

    public static final class CountAllocationSites extends StatementAdaptor {
        private int count;

        public int count() {
            return count;
        }

        @Override public List<Statement> visitHeapAlloc(final HeapAllocStatement statement) {
            count++;
            return super.visitHeapAlloc(statement);
        }
    }

    public static final class CollectAllocations extends StatementAdaptor {
        private final List<VariableName> allocations = new ArrayList<>();

        public List<VariableName> allocations() {
            return allocations;
        }

        @Override public List<Statement> visitHeapAlloc(final HeapAllocStatement statement) {
            allocations.add(statement.getLhsVar());
            return super.visitHeapAlloc(statement);
        }
    }

    public static Integer countAllocationSites(final Procedure procedure) {
        final CountAllocationSites counter = new CountAllocationSites();
        procedure.accept(counter);
        return counter.count();
    }

    public static List<VariableName> allocations(final Procedure procedure) {
        final CollectAllocations counter = new CollectAllocations();
        procedure.accept(counter);
        return counter.allocations();
    }

    public static Multiversion allocateUpfront(final Multiversion programs) {
        return CloneProgram.clonePrograms(programs, new ReplaceAllocationWithAssignment());
    }


    public static Matcher<Procedure> hasAllocationSiteCount(final int count) {
        return matcher(
                d -> d.appendText("allocation count").appendValue(count),
                (p, d) -> d.appendText("allocation count").appendValue(countAllocationSites(p)),
                p -> countAllocationSites(p) == count);
    }
}
