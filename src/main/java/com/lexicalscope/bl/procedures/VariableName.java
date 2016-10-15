package com.lexicalscope.bl.procedures;

import static com.lexicalscope.bl.procedures.Type.*;

import java.util.List;

import com.lexicalscope.Jc;

public class VariableName implements Comparable<VariableName> {
    private final String name;
    private final Type type;

    private VariableName(final String name, final Type type) {
        this.name = name;
        this.type = type;
    }

    @Override public String toString() {
        return name;
    }

    @Override public int hashCode() {
        final int prime = 31;
        int result = 1;
        result = prime * result + (name == null ? 0 : name.hashCode());
        result = prime * result + (type == null ? 0 : type.hashCode());
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
        final VariableName other = (VariableName) obj;
        if (name == null) {
            if (other.name != null) {
                return false;
            }
        } else if (!name.equals(other.name)) {
            return false;
        }
        if (type != other.type) {
            return false;
        }
        return true;
    }

    @Override public int compareTo(final VariableName o) {
        final int nameComparison = name.compareTo(o.name);
        if(nameComparison == 0) {
            return type.compareTo(o.type);
        }
        return nameComparison;
    }

    public Type getType() {
        return type;
    }

    public static List<VariableName> asVariableNames(final String[] names) {
        return Jc.$(names).map(n -> variableName(n, Ref))._$();
    }

    public static VariableName refVariableName(final String name) {
        return variableName(name, Ref);
    }

    public static VariableName boolVariableName(final String name) {
        return variableName(name, Bool);
    }

    public static VariableName variableName(final String name, final Type type) {
        return new VariableName(name, type);
    }
}
