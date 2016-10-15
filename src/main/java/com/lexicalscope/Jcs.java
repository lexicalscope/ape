package com.lexicalscope;

import java.util.Collection;
import java.util.List;
import java.util.function.BiFunction;
import java.util.function.Function;
import java.util.function.Predicate;
import java.util.function.Supplier;

public interface Jcs<T> extends Iterable<T> {
    @FunctionalInterface
    public interface IntFoldFunction<T> {
        int applyAsInt(T t, int u);
    }

    @FunctionalInterface
    public interface IntForFunction<T> {
        void accept(T t, int count);
    }

    <R> Jcs<R> map(Function<? super T, ? extends R> mapper);

    Jcs<T> filter(Predicate<? super T> predicate);
    <R> Jcs<R> filterByType(Class<R> klass);
    Jcs<T> filterOutMembersOf(Collection<?> collection);

    <A> A foldl(A initial, BiFunction<? super T, A, A> fold);
    int foldlInt(int initial, IntFoldFunction<? super T> fold);
    long count();

    int forEachCount(IntForFunction<? super T> action);

    List<T> _$();
    <C extends Collection<T>> C _$(Supplier<C> collectionFactory);

}
