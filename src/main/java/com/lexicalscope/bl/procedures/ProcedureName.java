package com.lexicalscope.bl.procedures;

import java.util.List;

import com.lexicalscope.Jc;

public class ProcedureName implements Comparable<ProcedureName> {
    private final String name;

    private ProcedureName(final String name) {
        this.name = name;
    }

    @Override public String toString() {
        return name;
    }

    @Override public int hashCode() {
        final int prime = 31;
        int result = 1;
        result = prime * result + (name == null ? 0 : name.hashCode());
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
        final ProcedureName other = (ProcedureName) obj;
        if (name == null) {
            if (other.name != null) {
                return false;
            }
        } else if (!name.equals(other.name)) {
            return false;
        }
        return true;
    }

    @Override public int compareTo(final ProcedureName o) {
        return name.compareTo(o.name);
    }

    public static List<ProcedureName> asProcedureNames(final String[] names) {
        return Jc.$(names).map(ProcedureName::procedureName)._$();
    }

    public static ProcedureName procedureName(final String name) {
        return new ProcedureName(name);
    }
}
