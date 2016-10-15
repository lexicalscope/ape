package com.lexicalscope.bl.procedures;

import java.util.Collections;
import java.util.Iterator;

import com.lexicalscope.bl.equiv.Expression;
import com.lexicalscope.bl.equiv.Modifies;

public class EmptyModifies implements Modifies {
    @Override public Iterator<Expression> iterator() {
        return Collections.emptyIterator();
    }

    @Override public String getType() {
        return "EmptyModifies";
    }

    @Override public String toString() {
        return "EmptyModifies []";
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
