using System;
using System.Diagnostics;
using System.IO;
using Smt;

namespace CVC5SmtSolver {
  
  public class CVC5SmtProcess : SmtProcess {
    const bool DEBUG = false;
    private Process process;
    private StreamWriter input;
    private StreamReader output;
    private bool isDisposed;

    public void Log(string s) {
      if (DEBUG) {
        Console.WriteLine(s);
      }
    }

    public CVC5SmtProcess() {
      try {
        // Start CVC5 process in interactive mode
        var startInfo = new ProcessStartInfo("cvc5", "--incremental");
        startInfo.RedirectStandardInput = true;
        startInfo.RedirectStandardOutput = true;
        startInfo.RedirectStandardError = true;
        startInfo.UseShellExecute = false;
        startInfo.CreateNoWindow = true;

        process = Process.Start(startInfo);
        if (process != null) {
          input = process.StandardInput;
          output = process.StandardOutput;

          // Initialize CVC5 with SMT-LIB2 commands
          SendCmd("(set-option :produce-models true)");
          SendCmd("(set-logic ALL)");
        }
        else {
          Console.WriteLine("Failed to start CVC5 process");
        }
        
        isDisposed = false;
      }
      catch (Exception ex) {
        Console.WriteLine($"Error initializing CVC5: {ex.Message}");
        isDisposed = true;
      }
    }

    public bool Disposed() {
      return isDisposed;
    }

    public Dafny.ISequence<Dafny.Rune> SendCmd(Dafny.ISequence<Dafny.Rune> cmdDafny) {
      var cmd = cmdDafny.ToVerbatimString(false);
      var response = SendCmd(cmd);
      var dafnyResponse = Dafny.Sequence<Dafny.Rune>.UnicodeFromString(response);
      return dafnyResponse;
    }

    public string SendCmd(string cmd) {
      try {
        if (isDisposed || input == null || output == null) {
          return "error: CVC5 not initialized or disposed";
        }
        
        // Special case for exit command - mark as disposed
        if (cmd == "(exit)") {
          isDisposed = true;
        }
        
        // Send command
        input.WriteLine(cmd);
        input.Flush();
        Log($"CVC5 << {cmd}");
        
        // Read response
        string response = ReadResponse(cmd);
        Log($"CVC5 >> {response}");
        return response;
      } catch (Exception ex) {
        Console.WriteLine($"Error communicating with CVC5: {ex.Message}");
        return $"error: {ex.Message}";
      }
    }
    
    private string ReadResponse(string cmd) {
      // For simple commands like (push), (pop), just return "success"
      if (cmd == "(push)" || cmd == "(pop)" || cmd.StartsWith("(assert ") || 
          cmd.StartsWith("(set-option ") || cmd.StartsWith("(set-logic ") ||
          cmd == "(exit)" ||
          cmd.StartsWith("(declare-fun") || cmd.StartsWith("(declare-const") || cmd.StartsWith("(declare-sort"))
      {
        return "success";
      }
      
      // For check-sat, read a single line
      if (cmd == "(check-sat)") {
        return output.ReadLine();
      }
      
      // For get-model, read until we get a balanced set of parentheses
      if (cmd == "(get-model)") {
        var response = new System.Text.StringBuilder();
        string line;
        int parenCount = 0;
        bool started = false;
        
        while ((line = output.ReadLine()) != null) {
          response.AppendLine(line);
          
          // Count parentheses to determine when the response is complete
          foreach (char c in line) {
            if (c == '(') {
              started = true;
              parenCount++;
            } else if (c == ')') {
              parenCount--;
            }
          }
          
          // If we've started receiving a response and all parentheses are balanced, we're done
          if (started && parenCount <= 0) {
            break;
          }
        }
        
        return response.ToString();
      }
      
      // Default case
      return output.ReadLine();
    }
  }
  public static partial class __default {
    public static SmtProcess CreateCVC5Process() {
      return new CVC5SmtProcess();
    }
  }
}