package com.lexicalscope.bl.equiv;

public interface BoogieWriter extends AutoCloseable {
    void writePairs(ProcedurePairs procedurePairs);
    void writeTest(String testName);

    @Override void close();
}