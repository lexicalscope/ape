package com.lexicalscope.bl.procedures;

import static com.lexicalscope.bl.procedures.VariableName.refVariableName;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

public class Path {
    private final VariableName local;
    private final List<String> fields;

    public Path(final VariableName local, final List<String> fields) {
        assert !fields.isEmpty();
        this.local = local;
        this.fields = fields;
    }

    public String getType() {
        return "Path";
    }

    public VariableName getLocal() {
        return local;
    }

    public List<String> getFields() {
        return fields;
    }

    public String lastField() {
        return fields.get(fields.size() - 1);
    }

    public Path prefix() {
        return new Path(local, new ArrayList<>(fields.subList(0, fields.size() - 1)));
    }

    public int fieldCount() {
        return fields.size();
    }

    @Override public int hashCode() {
        final int prime = 31;
        int result = 1;
        result = prime * result + (fields == null ? 0 : fields.hashCode());
        result = prime * result + (local == null ? 0 : local.hashCode());
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
        final Path other = (Path) obj;
        if (fields == null) {
            if (other.fields != null) {
                return false;
            }
        } else if (!fields.equals(other.fields)) {
            return false;
        }
        if (local == null) {
            if (other.local != null) {
                return false;
            }
        } else if (!local.equals(other.local)) {
            return false;
        }
        return true;
    }

    @Override public String toString() {
        return "Path [local=" + local + ", fields=" + fields + "]";
    }

    public static Path path(final String local, final List<String> fields) {
        return new Path(refVariableName(local), fields);
    }

    public static Path path(final String local, final String ... fields) {
        return path(local, Arrays.asList(fields));
    }
}
