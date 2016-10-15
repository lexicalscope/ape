package com.lexicalscope.bl.procedures;

public class Version implements Comparable<Version> {
    private final int id;

    public Version(final int id) {
        this.id = id;
    }

    @Override public int hashCode() {
        final int prime = 31;
        int result = 1;
        result = prime * result + id;
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
        final Version other = (Version) obj;
        if (id != other.id) {
            return false;
        }
        return true;
    }

    @Override public int compareTo(final Version o) {
        return Integer.compare(id, o.id);
    }

    @Override public String toString() {
        return "_" + id;
    }
}
