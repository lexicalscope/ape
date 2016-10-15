package com.lexicalscope.bl.equiv;

import static com.lexicalscope.Jc.$;

import java.util.List;

import org.antlr.v4.runtime.Token;

import com.lexicalscope.bl.parser.BlParser.PathContext;
import com.lexicalscope.bl.procedures.Path;

public class PathFactory {
    public static Path path(final PathContext path) {
        return path(path.local, path.fields);
    }

    private static Path path(final Token local, final List<Token> fields) {
        return Path.path(local.getText(), $(fields).map(t -> t.getText())._$());
    }

}
