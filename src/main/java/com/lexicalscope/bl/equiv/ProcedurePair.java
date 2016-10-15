package com.lexicalscope.bl.equiv;

import static com.lexicalscope.bl.procedures.ProcedureName.procedureName;

import java.util.Iterator;
import java.util.List;

import org.hamcrest.Matcher;

import com.lexicalscope.MatchersJ8;
import com.lexicalscope.bl.compiler.AllocateUpfront;
import com.lexicalscope.bl.equiv.PermutedAllocations.AllocationPermutation;
import com.lexicalscope.bl.procedures.Procedure;
import com.lexicalscope.bl.procedures.ProcedureName;
import com.lexicalscope.bl.procedures.VariableName;

public class ProcedurePair {
    private final ProcedureName name;
    private final Procedure first;
    private final Procedure second;

    public ProcedurePair(
            final ProcedureName name,
            final Procedure first,
            final Procedure second) {
        assert name.equals(first.getName());
        assert name.equals(second.getName());
        assert first.paramNames().equals(second.paramNames());

        this.name = name;
        this.first = first;
        this.second = second;
    }

    public ProcedureName name() {
        return name;
    }

    public List<VariableName> params() {
        return first.paramNames();
    }

    public Procedure procedure0() {
        return first;
    }

    public Procedure procedure1() {
        return second;
    }

    public int getParamsCount() {
        return first.paramNames().size();
    }

    public PermutedAllocations getPermutedAllocations() {
        final List<VariableName> allocations0 = AllocateUpfront.allocations(procedure0());
        final List<VariableName> allocations1 = AllocateUpfront.allocations(procedure1());
        return new PermutedAllocations(allocations0, allocations1);
    }

    // for string template
    public Iterator<AllocationPermutation> getPermutedAllocationsIterator() {
        return getPermutedAllocations().iterator();
    }

    @Override public int hashCode() {
        final int prime = 31;
        int result = 1;
        result = prime * result + (first == null ? 0 : first.hashCode());
        result = prime * result + (name == null ? 0 : name.hashCode());
        result = prime * result + (second == null ? 0 : second.hashCode());
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
        final ProcedurePair other = (ProcedurePair) obj;
        if (first == null) {
            if (other.first != null) {
                return false;
            }
        } else if (!first.equals(other.first)) {
            return false;
        }
        if (name == null) {
            if (other.name != null) {
                return false;
            }
        } else if (!name.equals(other.name)) {
            return false;
        }
        if (second == null) {
            if (other.second != null) {
                return false;
            }
        } else if (!second.equals(other.second)) {
            return false;
        }
        return true;
    }

    @Override public String toString() {
        return "ProcedurePair [name=" + name + ", first=" + first + ", second=" + second + "]";
    }

    @Deprecated public static Matcher<ProcedurePair> ver1Body(final Matcher<Procedure> bodyMatcher) {
        return MatchersJ8.featureMatcher(
            "ver1",
            pair -> pair.procedure0(),
            bodyMatcher
        );
    }

    public static Matcher<ProcedurePair> ver0(final Matcher<Procedure> matcher) {
        return MatchersJ8.featureMatcher(
            "ver0",
            pair -> pair.procedure0(),
            matcher
        );
    }

    public static Matcher<ProcedurePair> permutedAllocations(final Matcher<? super Iterable<AllocationPermutation>> allocationsMatcher) {
        return MatchersJ8.featureMatcher(
            "permutedAllocations",
            pair -> pair.getPermutedAllocations(),
            allocationsMatcher
        );
    }

    public static Matcher<ProcedurePair> pairCalled(final String procedureName) {
        return MatchersJ8.matcher(
                description -> description.appendText("pair of procedures called ").appendValue(procedureName),
                (item, mismatchDescription) -> mismatchDescription.appendText("pair of procedures called ").appendValue(item.name()),
                item -> item.name().equals(procedureName(procedureName))
        );
    }
}
