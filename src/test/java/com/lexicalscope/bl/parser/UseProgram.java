package com.lexicalscope.bl.parser;

import java.lang.annotation.ElementType;
import java.lang.annotation.Retention;
import java.lang.annotation.RetentionPolicy;
import java.lang.annotation.Target;

public @Retention(RetentionPolicy.RUNTIME) @Target(ElementType.METHOD) @interface UseProgram {
	String value();
}
