package com.lexicalscope.bl.equiv;

import java.util.List;

import com.lexicalscope.bl.compiler.Visitors;

public interface Statement {
    String getType();
    boolean isAlloc();
    List<Statement> accept(Visitors.StatementVisitor visitor);
    @Override int hashCode();
    @Override boolean equals(Object obj);
}
