package com.lexicalscope.bl.procedures;

public enum Type {
    Ref
    {
        @Override public String getType() {
            return "RefType";
        }
    },
    Bool
    {
        @Override public String toString() {
            return "bool";
        }

        @Override
        public String getType() {
            return "BoolType";
        }
    };

    public abstract String getType();
}
