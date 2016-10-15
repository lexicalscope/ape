package com.lexicalscope.bl.equiv;

import com.lexicalscope.MatchersJ8;

public class BoogieResult {
    private final int exitValue;
    private final int verified;
    private final int errors;
    private final String output;

    public BoogieResult(final int exitValue) {
        this(exitValue, 0, 0, "");
        assert exitValue != 0;
    }

    public BoogieResult(final int verified, final int errors, final String output) {
        this(0, verified, errors, output);
    }

    private BoogieResult(final int exitValue, final int verified, final int errors, final String output) {
        this.exitValue = exitValue;
        this.verified = verified;
        this.errors = errors;
        this.output = output;
    }

    public int exitValue() {
        return exitValue;
    }

    public int verified() {
        checkExit();
        return verified;
    }

    public int errors() {
        checkExit();
        return errors;
    }

    public String output() {
        return output;
    }

    private void checkExit() {
        if(exitValue != 0) {
            throw new IllegalStateException("boogie exit value was " + exitValue);
        }
    }

    public static org.hamcrest.Matcher<BoogieResult> verifiedWithNoErrors(final int verifiedCount) {
        return verifiedWith(verifiedCount, 0);
    }

    public static org.hamcrest.Matcher<BoogieResult> verifiedWith(final int verifiedCount, final int errorsCount) {
        return MatchersJ8.matcher(
                describeTo -> describeTo.
                    appendText("verified ").appendValue(verifiedCount).
                    appendText(" errors ").appendValue(errorsCount),
                (actual, describeMismatch) -> {
                    if(actual.exitValue() != 0) {
                        describeMismatch.
                            appendText("boogie exited with ").appendValue(actual.exitValue()).
                            appendText(" output :" + System.lineSeparator()).appendText(actual.output());
                    } else {
                        describeMismatch.
                            appendText("verified ").appendValue(actual.verified()).
                            appendText(" errors ").appendValue(actual.errors()).
                            appendText(" output :" + System.lineSeparator()).appendText(actual.output());
                    }
                },
                actual -> actual.exitValue() == 0 && actual.verified() == verifiedCount && actual.errors() == errorsCount);
    }

    @Override public String toString() {
        return "BoogieResult [exitValue=" + exitValue + ", verified=" + verified + ", errors=" + errors + ", output="
                + output + "]";
    }
}
