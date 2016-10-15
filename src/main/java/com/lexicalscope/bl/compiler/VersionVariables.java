package com.lexicalscope.bl.compiler;

import static com.lexicalscope.bl.procedures.StatementBuilder.localRead;
import static com.lexicalscope.bl.procedures.VariableName.variableName;

import java.util.ArrayList;
import java.util.List;

import com.lexicalscope.bl.equiv.Statement;
import com.lexicalscope.bl.procedures.Block;
import com.lexicalscope.bl.procedures.LocalUpdateStatement;
import com.lexicalscope.bl.procedures.Multiversion;
import com.lexicalscope.bl.procedures.Procedure;
import com.lexicalscope.bl.procedures.Program;
import com.lexicalscope.bl.procedures.StatementAdaptor;
import com.lexicalscope.bl.procedures.VariableName;
import com.lexicalscope.bl.procedures.Version;

public class VersionVariables {
    public static Multiversion versionVariables(final Multiversion programs) {
        return CloneProgram.clonePrograms(programs, new StatementAdaptor(){
            private Version version;
            private List<VariableName> procedureParams;

            @Override public Program visit(final Version version, final Program value) {
                this.version = version;
                final Program clone = super.visit(version, value);
                this.version = null;
                return clone;
            }

            @Override public void enterProcedure(final Procedure procedure) {
                super.enterProcedure(procedure);
                this.procedureParams = procedure.getParams();
            }

            @Override public void exitProcedure() {
                super.exitProcedure();
                this.procedureParams = null;
            }

            @Override public List<Statement> visitBodyStatements(final Block statements) {
                final List<Statement> cloneStatements = super.visitBodyStatements(statements);

                final List<Statement> replacementStatements = new ArrayList<>();
                for (final VariableName param : procedureParams) {
                    replacementStatements.add(
                            new LocalUpdateStatement(cloneVariable(param), localRead(param)));
                }
                replacementStatements.addAll(cloneStatements);

                return replacementStatements;
            }

            @Override public VariableName cloneVariable(final VariableName var) {
                return variableName("" + var + version, var.getType());
            }
        });
    }
}
