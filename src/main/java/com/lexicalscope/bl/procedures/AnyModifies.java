package com.lexicalscope.bl.procedures;

import java.util.Iterator;

import com.lexicalscope.bl.equiv.Expression;
import com.lexicalscope.bl.equiv.Modifies;

public class AnyModifies implements Modifies {
    @Override public Iterator<Expression> iterator() {
        throw new UnsupportedOperationException();
    }

    @Override public String getType() {
        return "AnyModifies";
    }

    @Override public String toString() {
        return "AnyModifies []";
    }

    @Override public int hashCode() {
        return getClass().hashCode();
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
        return true;
    }
}
