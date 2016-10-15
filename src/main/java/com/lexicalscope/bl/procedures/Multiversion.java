package com.lexicalscope.bl.procedures;

import static com.lexicalscope.Jc.$;
import static com.lexicalscope.MatchersJ8.featureMatcher;
import static com.lexicalscope.bl.procedures.Procedure.hasProcedureName;
import static com.lexicalscope.bl.procedures.ProcedureName.procedureName;
import static org.hamcrest.Matchers.equalTo;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.NavigableMap;
import java.util.TreeMap;
import java.util.function.Consumer;

import org.hamcrest.Matcher;
import org.stringtemplate.v4.ST;

import com.lexicalscope.bl.compiler.Visitors;
import com.lexicalscope.bl.equiv.ProcedurePair;

public class Multiversion implements Iterable<Entry<Version, Program>>{
    private final NavigableMap<Version, Program> programs;

    public Multiversion(final NavigableMap<Version, Program> programs) {
        assert !programs.isEmpty();
        this.programs = programs;
    }

    public List<ProcedurePair> pairs() {
        if(programs.size() != 2) {
            throw new IllegalStateException("wrong number of programs, should be 2 but was " + programs.size());
        }
        final Program program1 = programs.get(new Version(0));
        final Program program2 = programs.get(new Version(1));

        if(!program1.procedureNames().equals(program2.procedureNames())) {
            throw new IllegalStateException("wrong number of programs, should be 2 but was " + programs.size());
        }

        final Map<ProcedureName, ProcedurePair> pairs = new LinkedHashMap<>();
        for (final ProcedureName procedureName : program1.procedureNames()) {
            pairs.put(procedureName,
                    new ProcedurePair(procedureName,
                            program1.procedure(procedureName),
                            program2.procedure(procedureName)));
        }

        return $(pairs).values()._$();
    }

    /**
     * @return The first procedure called name
     */
    public Procedure procedure(final ProcedureName name) {
        assert firstProgram().hasProcedure(name) : firstProgram().procedures();
        return firstProgram().procedure(name);
    }

    public Procedure procedure(final String name) {
        return procedure(procedureName(name));
    }

    public Procedure procedure(final ProcedureName name, final Version ver) {
        return programs.get(ver).procedure(name);
    }

    private Program firstProgram() {
        assert !programs.isEmpty();
        return programs.firstEntry().getValue();
    }

    public static Matcher<? super Multiversion> hasProcedureCalled(final String string) {
        return procedureNamed(string, hasProcedureName(equalTo(string)));
    }

    public static Matcher<Multiversion> procedureNamed(final String procedureName, final Matcher<Procedure> procedureMatcher) {
        return featureMatcher("procedure " + procedureName, m -> m.procedure(ProcedureName.procedureName(procedureName)), procedureMatcher);
    }

    public static Matcher<? super Multiversion> procedureVersion(final String procedureName, final int ver, final Matcher<Procedure> procedureMatcher) {
        return featureMatcher(
                "procedure " + procedureName + " version " + ver,
                m -> m.procedure(procedureName(procedureName), new Version(ver)),
                procedureMatcher);
    }

    public void foreachProcedure(final Consumer<Procedure> consumer) {
        programs.forEach(
                (v,program) -> program.procedures().forEach(
                        procedure -> consumer.accept(procedure)));
    }

    public void foreachProcedurePair(final Consumer<ProcedurePair> consumer) {
        pairs().forEach(consumer);
    }

    @Override public Iterator<Entry<Version, Program>> iterator() {
        return programs.entrySet().iterator();
    }

    private final ST template = new ST("VERSION<\\n><programs:{it|<it>}; separator=\"\\n\">");
    @Override public String toString() {
        template.add("programs", programs.values());
        return template.render();
    }

    @Override public int hashCode() {
        final int prime = 31;
        int result = 1;
        result = prime * result + (programs == null ? 0 : programs.hashCode());
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
        final Multiversion other = (Multiversion) obj;
        if (programs == null) {
            if (other.programs != null) {
                return false;
            }
        } else if (!programs.equals(other.programs)) {
            return false;
        }
        return true;
    }

    public Multiversion accept(final Visitors.ProgramVisitor programCloner) {
        programCloner.enterMultiversion(this);
        final TreeMap<Version, Program> clone = new TreeMap<>();
        for (final Entry<Version, Program> entry : programs.entrySet()) {
            clone.put(entry.getKey(), programCloner.visit(entry.getKey(), entry.getValue()));
        }
        final Multiversion result = programCloner.visitMultiversion(clone);
        programCloner.exitMultiversion();
        return result;
    }

    public List<Procedure> versions(final ProcedureName name) {
        final List<Procedure> result = new ArrayList<>();
        for (final Entry<Version, Program> entry : programs.entrySet()) {
            result.add(entry.getValue().procedure(name));
        }
        return result;
    }
}
