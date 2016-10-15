package com.lexicalscope.bl.procedures;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;

import com.lexicalscope.bl.compiler.Visitors;
import com.lexicalscope.bl.equiv.Statement;

public class Block implements Statement, Iterable<Statement> {
    private final List<Statement> statements;

    public Block(final List<Statement> statements) {
        this.statements = statements;
    }

    public Block(final Statement statement) {
        this(new ArrayList<Statement>(){{add(statement);}});
    }

    public Block() {
        this(new ArrayList<>());
    }

    @Override public String getType() {
        return "Block";
    }

    @Override public boolean isAlloc() {
        return false;
    }

    @Override public List<Statement> accept(final Visitors.StatementVisitor visitor) {
        return visitor.visitBlock(this);
    }

    @Override public Iterator<Statement> iterator() {
        return statements.iterator();
    }

    public List<Statement> getStatements() {
        return statements;
    }

    @Override public int hashCode() {
        final int prime = 31;
        int result = 1;
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
        final Block other = (Block) obj;
        if (statements == null) {
            if (other.statements != null) {
                return false;
            }
        } else if (!statements.equals(other.statements)) {
            return false;
        }
        return true;
    }

    @Override public String toString() {
        return "Block [statements=" + statements + "]";
    }
}
