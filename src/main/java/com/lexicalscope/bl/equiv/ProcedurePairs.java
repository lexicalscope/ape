package com.lexicalscope.bl.equiv;

import java.util.Iterator;
import java.util.List;

import org.stringtemplate.v4.ST;

@Deprecated public class ProcedurePairs implements Iterable<ProcedurePair> {
    private final List<ProcedurePair> pairs;

    public ProcedurePairs(final List<ProcedurePair> pairs) {
        this.pairs = pairs;
    }

    @Override public Iterator<ProcedurePair> iterator() {
        return pairs.iterator();
    }

    @Override public int hashCode() {
        final int prime = 31;
        int result = 1;
        result = prime * result + (pairs == null ? 0 : pairs.hashCode());
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
        final ProcedurePairs other = (ProcedurePairs) obj;
        if (pairs == null) {
            if (other.pairs != null) {
                return false;
            }
        } else if (!pairs.equals(other.pairs)) {
            return false;
        }
        return true;
    }

    private final ST template = new ST("Pairs<\\n><pairs:{it|<it>}; separator=\"\\n\">");
    @Override public String toString() {
        template.add("pairs", pairs);
        return template.render();
    }
}
