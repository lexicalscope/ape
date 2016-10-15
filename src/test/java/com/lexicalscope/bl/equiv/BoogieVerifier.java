package com.lexicalscope.bl.equiv;

import static java.lang.Integer.parseInt;
import static java.lang.System.lineSeparator;
import static java.nio.charset.StandardCharsets.UTF_8;

import java.io.ByteArrayOutputStream;
import java.io.File;
import java.io.IOException;
import java.util.HashMap;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import org.apache.commons.exec.CommandLine;
import org.apache.commons.exec.DefaultExecuteResultHandler;
import org.apache.commons.exec.DefaultExecutor;
import org.apache.commons.exec.ExecuteWatchdog;
import org.apache.commons.exec.Executor;
import org.apache.commons.exec.PumpStreamHandler;

public class BoogieVerifier {
    public BoogieResult execBoogie(final File output) throws IOException, InterruptedException {
        final CommandLine cmdLine = new CommandLine("C:\\Users\\flami_000\\Documents\\boogie\\Binaries\\boogie.exe");
        //cmdLine.addArgument("/smoke");
        //cmdLine.addArgument("/vcsMaxKeepGoingSplits:2");
        cmdLine.addArgument("${file}");
        //cmdLine.addArgument("/z3opt:TRACE=true");
        //cmdLine.addArgument("/timeLimit:5400");
        //cmdLine.addArgument("/z3opt:TRACE_FILE_NAME=\"z3.trace\"");
        final HashMap<String, Object> map = new HashMap<>();
        map.put("file", output);
        cmdLine.setSubstitutionMap(map);

        final DefaultExecuteResultHandler resultHandler = new DefaultExecuteResultHandler();

        final ExecuteWatchdog watchdog = new ExecuteWatchdog(1080000 * 1000);
        final Executor executor = new DefaultExecutor();
        executor.setExitValue(1);
        //executor.setWatchdog(watchdog);
        final ByteArrayOutputStream out = new ByteArrayOutputStream();
        final ByteArrayOutputStream err = new ByteArrayOutputStream();
        executor.setStreamHandler(new PumpStreamHandler(out, err));
        executor.execute(cmdLine, resultHandler);

        resultHandler.waitFor();

        final String result = out.toString(UTF_8.name());
        final String errors = err.toString(UTF_8.name());

        if(resultHandler.getExitValue() != 0)
        {
            System.out.println(result);
            System.out.println(errors);
            return new BoogieResult(resultHandler.getExitValue());
        }

        if(Pattern.compile("found unreachable code:").matcher(result).find()) {
            throw new IllegalStateException("found unreachable code " + lineSeparator() + result);
        }

        final Matcher verifiedMatcher = Pattern.compile("Boogie program verifier finished with (\\d+) verified, (\\d+) errors?$").matcher(result);
        if(!verifiedMatcher.find()) {
            throw new IllegalStateException("couldn't match in boogie output " + lineSeparator() + result);
        }

        return new BoogieResult(parseInt(verifiedMatcher.group(1)), parseInt(verifiedMatcher.group(2)), result);
    }
}