package com.lexicalscope.bl.equiv;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;
import java.util.function.BiFunction;

/**
 * Uses Heap's algorithm to produce all permutations of a given list.
 * We use an iterator to avoid having to use too much memory.
 *
 * @author t.wood
 *
 * @param <T> The type of item being permuted
 * @param <R> The type resulting from decorating the permutation
 */
public final class PermutationIterator<T,R> implements Iterator<R> {
    private final BiFunction<List<T>, Integer, R> defensiveDecorator;
    private final List<T> a;
    private R pending;

    private final int[] skel;
    private int i;

    private int permutationNumber = 0;

    /**
     * An iterator of permutations
     *
     * @param a the list to permute
     * @param decorator a decorator to apply to the permutation, a defensive copy
     *                  of the permutation is taken before it is passed to the decorator
     */
    public PermutationIterator(final List<T> a, final BiFunction<List<T>, Integer, R> decorator) {
        defensiveDecorator = (t, permutationNumber) -> decorator.apply(new ArrayList<>(t), permutationNumber);
        setPending(a);
        this.a = new ArrayList<>(a);
        skel = new int[a.size()];
        i = 0;
    }

    void setPending(final List<T> a) {
        pending = a != null ? defensiveDecorator.apply(a, permutationNumber) : null;
        permutationNumber++;
    }

    @Override public boolean hasNext() {
        return pending != null;
    }

    @Override public R next() {
        if(pending == null) {
            throw new IndexOutOfBoundsException();
        }
        final R result = pending;
        setPending(permute());
        return result;
    }

    private List<T> permute() {
        while(i < a.size()) {
            if (skel[i] < i) {
                if (even(i)) {
                    swap(a, 0, i);
                } else {
                    swap(a, skel[i], i);
                }
                skel[i] += 1;
                i = 0;
                return a;
            } else {
                skel[i] = 0;
                i += 1;
            }
        }
        return null;
    }

    private void swap(final List<T> a, final int i0, final int i1) {
        final T t = a.get(i0);
        a.set(i0, a.get(i1));
        a.set(i1, t);
    }

    private boolean even(final int i) {
        return i % 2 == 0;
    }
}