package CVC5SmtSolver;

import java.io.*;
import java.util.concurrent.TimeUnit;

public class CVC5SmtProcess implements Smt.SmtProcess {
    private static final boolean DEBUG = false;
    private Process process;
    private PrintWriter input;
    private BufferedReader output;
    private boolean isDisposed;

    public void log(String s) {
        if (DEBUG) {
            System.out.println(s);
        }
    }

    public CVC5SmtProcess() {
        try {
            ProcessBuilder pb = new ProcessBuilder("CVC5", "--incremental");
            pb.redirectErrorStream(true);
            process = pb.start();

            input = new PrintWriter(process.getOutputStream(), true);
            output = new BufferedReader(new InputStreamReader(process.getInputStream()));

            SendCmd("(set-option :produce-models true)");
            SendCmd("(set-logic ALL)");
            
            isDisposed = false;
        } catch (Exception ex) {
            System.out.println("Error initializing CVC5: " + ex.getMessage());
            isDisposed = true;
        }
    }

    @Override
    public boolean Disposed() {
        return isDisposed;
    }

    @Override
    public dafny.DafnySequence<? extends dafny.CodePoint> SendCmd(dafny.DafnySequence<? extends dafny.CodePoint> cmdDafny) {
        String cmd = cmdDafny.verbatimString();
        String response = SendCmd(cmd);
        return dafny.DafnySequence.asUnicodeString(response);
    }

    public String SendCmd(String cmd) {
        try {
            if (isDisposed || input == null || output == null) {
                return "error: CVC5 not initialized or disposed";
            }
            
            if ("(exit)".equals(cmd)) {
                isDisposed = true;
            }
            
            input.println(cmd);
            input.flush();
            log("CVC5 << " + cmd);
            
            String response = readResponse(cmd);
            log("CVC5 >> " + response);
            return response;
        } catch (Exception ex) {
            System.out.println("Error communicating with CVC5: " + ex.getMessage());
            return "error: " + ex.getMessage();
        }
    }
    
    private String readResponse(String cmd) throws IOException {
        if ("(push)".equals(cmd) || "(pop)".equals(cmd) || cmd.startsWith("(assert ") || 
            cmd.startsWith("(set-option ") || cmd.startsWith("(set-logic ") ||
            "(exit)".equals(cmd) ||
            cmd.startsWith("(declare-fun") || cmd.startsWith("(declare-const") || cmd.startsWith("(declare-sort")) {
            return "success";
        }
        
        if ("(check-sat)".equals(cmd)) {
            return output.readLine();
        }
        
        if ("(get-model)".equals(cmd)) {
            StringBuilder response = new StringBuilder();
            String line;
            int parenCount = 0;
            boolean started = false;
            
            while ((line = output.readLine()) != null) {
                response.append(line).append("\n");
                
                for (char c : line.toCharArray()) {
                    if (c == '(') {
                        started = true;
                        parenCount++;
                    } else if (c == ')') {
                        parenCount--;
                    }
                }
                
                if (started && parenCount <= 0) {
                    break;
                }
            }
            
            return response.toString();
        }
        
        return output.readLine();
    }
}
