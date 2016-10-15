package com.lexicalscope.bl.procedures;


import com.lexicalscope.bl.compiler.Visitors;
import com.lexicalscope.bl.equiv.Expression;
import com.lexicalscope.bl.equiv.PathFactory;
import com.lexicalscope.bl.parser.BlParser.HeapReadContext;

public class HeapReadExpression extends AbstractExpression implements Expression {
    private final Path path;

    public HeapReadExpression(final HeapReadContext expr) {
        this(PathFactory.path(expr.path()));
    }

    @Deprecated // should be one field only
    public HeapReadExpression(final String var, final String ... fields) {
        this(Path.path(var, fields));
    }

    public HeapReadExpression(final Path path) {
        this.path = path;
    }

    @Override public String getType() {
        return "HeapRead";
    }

    public Path getPath() {
        return path;
    }

    @Override public int hashCode() {
        final int prime = 31;
        int result = 1;
        result = prime * result + (path == null ? 0 : path.hashCode());
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
        final HeapReadExpression other = (HeapReadExpression) obj;
        if (path == null) {
            if (other.path != null) {
                return false;
            }
        } else if (!path.equals(other.path)) {
            return false;
        }
        return true;
    }

    @Override public String toString() {
        return "HeapReadExpression [path=" + path + "]";
    }

    @Override public Expression accept(final Visitors.ExpressionVisitor visitor) {
        return visitor.visitHeapRead(this);
    }
}
