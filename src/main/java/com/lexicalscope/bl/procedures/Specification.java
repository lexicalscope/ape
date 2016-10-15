package com.lexicalscope.bl.procedures;

import static com.lexicalscope.bl.equiv.ExpressionFactory.expression;

import java.util.ArrayList;
import java.util.List;

import org.antlr.v4.runtime.tree.ParseTreeWalker;

import com.lexicalscope.bl.equiv.Expression;
import com.lexicalscope.bl.equiv.Modifies;
import com.lexicalscope.bl.parser.BlBaseListener;
import com.lexicalscope.bl.parser.BlParser.HeapReadContext;
import com.lexicalscope.bl.parser.BlParser.LocalReadContext;
import com.lexicalscope.bl.parser.BlParser.ModifiesSpecContext;
import com.lexicalscope.bl.parser.BlParser.SpecificationContext;

public class Specification {
    private final List<Expression> reads;
    private final Modifies modifies;

    private static final class ReadExpressionCollector extends BlBaseListener {
        private final List<Expression> result;

        private ReadExpressionCollector(final List<Expression> result) {
            this.result = result;
        }

        @Override public void enterLocalRead(final LocalReadContext ctx) {
            result.add(expression(ctx));
        }

        @Override public void enterHeapRead(final HeapReadContext ctx) {
            result.add(expression(ctx));
        }
    }

    public Specification(final List<Expression> reads, final Modifies modifies) {
        this.reads = reads;
        this.modifies = modifies;
    }

    public Modifies getModifies() {
        return modifies;
    }

    public List<Expression> getReads() {
        return reads;
    }

    @Override public int hashCode() {
        final int prime = 31;
        int result = 1;
        result = prime * result + (modifies == null ? 0 : modifies.hashCode());
        result = prime * result + (reads == null ? 0 : reads.hashCode());
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
        final Specification other = (Specification) obj;
        if (modifies == null) {
            if (other.modifies != null) {
                return false;
            }
        } else if (!modifies.equals(other.modifies)) {
            return false;
        }
        if (reads == null) {
            if (other.reads != null) {
                return false;
            }
        } else if (!reads.equals(other.reads)) {
            return false;
        }
        return true;
    }

    @Override public String toString() {
        return "Specification [reads=" + reads + ", modifies=" + modifies + "]";
    }

    public static Specification specification(final SpecificationContext context) {
        return new Specification(reads(context), modifies(context));
    }

    private static Modifies modifies(final SpecificationContext context) {
        if(context == null || context.modifiesSpec() == null) {
            return new AnyModifies();
        }
        final ModifiesSpecContext modifiesSpec = context.modifiesSpec();
        if(modifiesSpec.expressionSet().expr.isEmpty()) {
            return new EmptyModifies();
        }
        final List<Expression> result = new ArrayList<Expression>();
        new ParseTreeWalker().walk(new ReadExpressionCollector(result), modifiesSpec);
        return new ModifiesSet(result);
    }

    private static List<Expression> reads(final SpecificationContext context) {
        final List<Expression> result = new ArrayList<Expression>();
        if(context != null && context.readsSpec() != null) {
            new ParseTreeWalker().walk(new ReadExpressionCollector(result), context.readsSpec());
        }
        return result;
    }
}
