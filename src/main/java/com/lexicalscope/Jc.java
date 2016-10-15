package com.lexicalscope;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Spliterator;
import java.util.Spliterators;
import java.util.function.BiFunction;
import java.util.function.Function;
import java.util.function.Predicate;
import java.util.function.Supplier;
import java.util.stream.Collectors;
import java.util.stream.Stream;
import java.util.stream.StreamSupport;

public class Jc {
    private static final class StreamJcs<T> implements Jcs<T> {
        private final Stream<T> stream;

        public StreamJcs(final Iterable<T> iterable) {
            this(stream(iterable.spliterator()));
        }

        public StreamJcs(final Stream<T> stream) {
            this.stream = stream;
        }

        @Override public Iterator<T> iterator() {
            return _$().iterator();
        }

        @Override public List<T> _$() {
            return _$(ArrayList::new);
        }

        @Override public <R> Jcs<R> map(final Function<? super T, ? extends R> mapper) {
            return new StreamJcs<>(stream.map(mapper));
        }

        @Override public Jcs<T> filter(final Predicate<? super T> predicate) {
            return new StreamJcs<>(stream.filter(predicate));
        }

        @Override public <C extends Collection<T>> C _$(final Supplier<C> collectionFactory) {
            return stream.collect(Collectors.toCollection(collectionFactory));
        }

        @Override public <R> Jcs<R> filterByType(final Class<R> klass) {
            return filter(s -> klass.isInstance(s)).map(s -> klass.cast(s));
        }

        @Override public Jcs<T> filterOutMembersOf(final Collection<?> collection) {
            return filter(s -> !collection.contains(s));
        }

        @Override public <A> A foldl(final A initial, final BiFunction<? super T, A, A> fold) {
            final Cell<A> cell = new Cell<>(initial);
            stream.forEachOrdered(p -> cell.val = fold.apply(p, cell.val));
            return cell.val;
        }

        @Override public int foldlInt(final int initial, final IntFoldFunction<? super T> fold) {
            final CellInt cell = new CellInt(initial);
            stream.forEachOrdered(p -> cell.val = fold.applyAsInt(p, cell.val));
            return cell.val;
        }

        @Override public int forEachCount(final com.lexicalscope.Jcs.IntForFunction<? super T> action) {
            return foldlInt(0, (item, count) -> {action.accept(item, count); return count+1;});
        }

        @Override public long count() {
            return stream.count();
        }
    }

    private static final class StreamJcm<K, V> implements Jcm<K, V> {
        private final Map<K,V> map;

        public StreamJcm(final Map<K,V> map) {
            this.map = map;
        }

        @Override public Jcs<V> values() {
            return $(map.values());
        }
    }

    public static <T> Jcs<T> $(final Iterable<T> iterable) {
        return new StreamJcs<>(iterable);
    }

    static <T> Stream<T> stream(final Iterator<T> iterator) {
        final Spliterator<T> spliterator = Spliterators.spliteratorUnknownSize(iterator, 0);
        return stream(spliterator);
    }

    static <T> Stream<T> stream(final Spliterator<T> spliterator) {
        return StreamSupport.stream(spliterator, false);
    }

    public static <K, V> Jcm<K, V> $(final Map<K, V> map) {
        return new StreamJcm<>(map);
    }

    public static <T> Jcs<T> $(final T[] values) {
        return $(Arrays.asList(values));
    }
}
