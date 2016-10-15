package com.lexicalscope.bl.procedures;

import java.util.Arrays;
import java.util.Iterator;
import java.util.List;

import com.lexicalscope.bl.equiv.Expression;
import com.lexicalscope.bl.equiv.Modifies;

public class ModifiesSet implements Modifies {
    private final List<Expression> expressions;

    public ModifiesSet(final List<Expression> expressions) {
        this.expressions = expressions;
    }

    public ModifiesSet(final Expression ... expressions) {
        this(Arrays.asList(expressions));
    }

    public List<Expression> getExpressions() {
        return expressions;
    }

    @Override public Iterator<Expression> iterator() {
        return expressions.iterator();
    }

    @Override public String getType() {
        return "ModifiesSet";
    }

    @Override public String toString() {
        return "ModifiesSet [expressions=" + expressions + "]";
    }

    @Override public int hashCode() {
        final int prime = 31;
        int result = 1;
        result = prime * result + (expressions == null ? 0 : expressions.hashCode());
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
        final ModifiesSet other = (ModifiesSet) obj;
        if (expressions == null) {
            if (other.expressions != null) {
                return false;
            }
        } else if (!expressions.equals(other.expressions)) {
            return false;
        }
        return true;
    }
}
