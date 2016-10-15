package com.lexicalscope.bl.equiv;

import static com.lexicalscope.bl.procedures.VariableName.refVariableName;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;

import org.hamcrest.Matcher;
import org.hamcrest.Matchers;

import com.lexicalscope.bl.equiv.PermutedAllocations.AllocationPermutation;
import com.lexicalscope.bl.procedures.VariableName;

public class PermutedAllocations implements Iterable<AllocationPermutation> {
    private final List<VariableName> allocations0;
    private final List<VariableName> allocations1;

    public static final class AllocationPermutation implements Iterable<AllocationPair> {
        private final List<AllocationPair> allocationPairs;
        private final int strategyNumber;

        public AllocationPermutation(final List<AllocationPair> allocationPairs, final int strategyNumber) {
            this.allocationPairs = allocationPairs;
            this.strategyNumber = strategyNumber;
        }

        @Override public Iterator<AllocationPair> iterator() {
            return allocationPairs.iterator();
        }

        // for string template
        public Iterator<AllocationPair> getIterator() {
            return iterator();
        }

        public int getStrategyNumber() {
            return strategyNumber;
        }

        @Override public int hashCode() {
            final int prime = 31;
            int result = 1;
            result = prime * result + (allocationPairs == null ? 0 : allocationPairs.hashCode());
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
            final AllocationPermutation other = (AllocationPermutation) obj;
            if (allocationPairs == null) {
                if (other.allocationPairs != null) {
                    return false;
                }
            } else if (!allocationPairs.equals(other.allocationPairs)) {
                return false;
            }
            return true;
        }

        @Override public String toString() {
            return "AllocationPermutation [allocationPairs=" + allocationPairs + "]";
        }
    }

    public static final class AllocationPair {
        private final VariableName var0;
        private final VariableName var1;

        public AllocationPair(final VariableName var0, final VariableName var1) {
            this.var0 = var0;
            this.var1 = var1;
        }

        @Override public int hashCode() {
            final int prime = 31;
            int result = 1;
            result = prime * result + (var0 == null ? 0 : var0.hashCode());
            result = prime * result + (var1 == null ? 0 : var1.hashCode());
            return result;
        }

        public VariableName getVar0() {
            return var0;
        }

        public VariableName getVar1() {
            return var1;
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
            final AllocationPair other = (AllocationPair) obj;
            if (var0 == null) {
                if (other.var0 != null) {
                    return false;
                }
            } else if (!var0.equals(other.var0)) {
                return false;
            }
            if (var1 == null) {
                if (other.var1 != null) {
                    return false;
                }
            } else if (!var1.equals(other.var1)) {
                return false;
            }
            return true;
        }

        @Override public String toString() {
            return "AllocationPair [var0=" + var0 + ", var1=" + var1 + "]";
        }
    }

    public PermutedAllocations(final List<VariableName> allocations0, final List<VariableName> allocations1) {
        assert allocations0.size() == allocations1.size();
        this.allocations0 = allocations0;
        this.allocations1 = allocations1;
    }

    @Override public Iterator<AllocationPermutation> iterator() {
        return new PermutationIterator<VariableName, AllocationPermutation>(allocations0, (permutation, permutationNumber) -> pair(permutation, allocations1, permutationNumber));
    }

    public static AllocationPermutation pair(final List<VariableName> allocations0, final List<VariableName> allocations1, final int strategyNumber) {
        assert allocations0.size() == allocations1.size();
        final List<AllocationPair> result = new ArrayList<>(allocations0.size());

        final Iterator<VariableName> iterator0 = allocations0.iterator();
        final Iterator<VariableName> iterator1 = allocations1.iterator();

        while(iterator0.hasNext() && iterator1.hasNext()) {
            result.add(pair(iterator0.next(), iterator1.next()));
        }
        return new AllocationPermutation(result, strategyNumber);
    }

    @Override public int hashCode() {
        final int prime = 31;
        int result = 1;
        result = prime * result + (allocations0 == null ? 0 : allocations0.hashCode());
        result = prime * result + (allocations1 == null ? 0 : allocations1.hashCode());
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
        final PermutedAllocations other = (PermutedAllocations) obj;
        if (allocations0 == null) {
            if (other.allocations0 != null) {
                return false;
            }
        } else if (!allocations0.equals(other.allocations0)) {
            return false;
        }
        if (allocations1 == null) {
            if (other.allocations1 != null) {
                return false;
            }
        } else if (!allocations1.equals(other.allocations1)) {
            return false;
        }
        return true;
    }

    @Override public String toString() {
        return "PermutedAllocations [allocations0=" + allocations0 + ", allocations1=" + allocations1 + "]";
    }

    public static AllocationPair pair(final String var0, final String var1) {
        return pair(refVariableName(var0), refVariableName(var1));
    }

    public static AllocationPair pair(final VariableName var0, final VariableName var1) {
        return new AllocationPair(var0, var1);
    }

    public static Matcher<? super AllocationPermutation> permutation(final AllocationPair ... allocationPairs ) {
         return Matchers.contains(allocationPairs);
    }
}
