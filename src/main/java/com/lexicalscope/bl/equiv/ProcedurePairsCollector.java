package com.lexicalscope.bl.equiv;

import com.lexicalscope.bl.parser.BlParser.MultiversionContext;

public class ProcedurePairsCollector {
    public static ProcedurePairs procedurePairs(final MultiversionContext tree) {
        return new ProcedurePairs(ProgramCollector.programs(tree).pairs());
    }
}
