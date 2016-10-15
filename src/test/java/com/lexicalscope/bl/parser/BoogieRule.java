package com.lexicalscope.bl.parser;

import java.io.File;
import java.io.IOException;
import java.net.URISyntaxException;
import java.net.URL;

import org.junit.rules.MethodRule;
import org.junit.runners.model.FrameworkMethod;
import org.junit.runners.model.Statement;

import com.lexicalscope.bl.equiv.BoogieResult;
import com.lexicalscope.bl.equiv.BoogieVerifier;

public class BoogieRule implements MethodRule {
    private String inputFile;
    private Object target;

    @Override public Statement apply(final Statement base, final FrameworkMethod method, final Object target) {
        return new Statement() {
            @Override public void evaluate() throws Throwable {
                final BoogieFile annotation = method.getAnnotation(BoogieFile.class);
                if(annotation == null) {
                    base.evaluate();
                }

                BoogieRule.this.target = target;
                inputFile = annotation.value();
                base.evaluate();
            }
        };
    }

    public BoogieResult verifyWithBoogie()  {
        try {
            final Class<? extends Object> testKlass = target.getClass();
            final URL inputResource = testKlass.getResource(inputFile);
            return new BoogieVerifier().execBoogie(new File(inputResource.toURI()));
        } catch (IOException | InterruptedException | URISyntaxException e) {
            throw new RuntimeException(e);
        }
    }
}
