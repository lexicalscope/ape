package com.lexicalscope.bl.procedures;

import java.util.Collection;
import java.util.Iterator;
import java.util.Map.Entry;
import java.util.NavigableMap;
import java.util.Set;
import java.util.TreeMap;

import org.stringtemplate.v4.ST;

import com.lexicalscope.bl.compiler.Visitors;

public class Program implements Iterable<Entry<ProcedureName, Procedure>> {
    private final NavigableMap<ProcedureName, Procedure> procedures;

    public Program(final NavigableMap<ProcedureName, Procedure> procedures) {
        this.procedures = procedures;
    }

    public Set<ProcedureName> procedureNames() {
        return procedures.keySet();
    }

    public Procedure procedure(final ProcedureName procedureName) {
        return procedures.get(procedureName);
    }

    public boolean hasProcedure(final ProcedureName name) {
        return procedures.containsKey(name);
    }

    public Collection<Procedure> procedures() {
        return procedures.values();
    }

    @Override public Iterator<Entry<ProcedureName, Procedure>> iterator() {
        return procedures.entrySet().iterator();
    }

    private final ST template = new ST("<procedures:{it|<it>}; separator=\"\\n\">");
    @Override public String toString() {
        template.add("procedures", procedures.values());
        return template.render();
    }

    @Override public int hashCode() {
        final int prime = 31;
        int result = 1;
        result = prime * result + (procedures == null ? 0 : procedures.hashCode());
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
        final Program other = (Program) obj;
        if (procedures == null) {
            if (other.procedures != null) {
                return false;
            }
        } else if (!procedures.equals(other.procedures)) {
            return false;
        }
        return true;
    }

    public NavigableMap<ProcedureName, Procedure> accept(final Visitors.ProcedureVisitor programCloner) {
        final TreeMap<ProcedureName, Procedure> clone = new TreeMap<>();
        for (final Entry<ProcedureName, Procedure> entry : procedures.entrySet()) {
            clone.put(entry.getKey(), entry.getValue().accept(programCloner));
        }
        return clone;
    }
}
