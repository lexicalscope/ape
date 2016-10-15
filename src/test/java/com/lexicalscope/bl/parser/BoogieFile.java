package com.lexicalscope.bl.parser;

import static java.lang.annotation.RetentionPolicy.RUNTIME;

import java.lang.annotation.Retention;

@Retention(RUNTIME) public @interface BoogieFile {
    String value();
}
