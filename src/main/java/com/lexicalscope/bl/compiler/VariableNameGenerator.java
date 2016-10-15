package com.lexicalscope.bl.compiler;

import java.util.ArrayList;
import java.util.List;

import com.lexicalscope.bl.procedures.Type;
import com.lexicalscope.bl.procedures.VariableName;

public class VariableNameGenerator {
    private final String root;
    private final Type type;
    private int index;

    public VariableNameGenerator(final String root, final Type type) {
        this.root = root;
        this.type = type;
        this.index = 0;
    }

    public static VariableNameGenerator variableNameGenerator(final String root, final Type type) {
        return new VariableNameGenerator(root, type);
    }

    public VariableName next() {
        return VariableName.variableName("$" + root + "#" + index++, type);
    }

    public List<VariableName> next(final int allocationCount) {
        final List<VariableName> allocationVariables = new ArrayList<>();
        for (int i = 0; i < allocationCount; i++) {
            allocationVariables.add(next());
        }
        return allocationVariables;
    }
}
