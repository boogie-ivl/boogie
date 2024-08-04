using System;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.IO;

namespace Microsoft.Boogie
{
  public class OnlyBoogie
  {
    public static int Main(string[] args)
    {
      Contract.Requires(Cce.NonNullElements(args));

      var options = new CommandLineOptions(Console.Out, new ConsolePrinter())
      {
        RunningBoogieFromCommandLine = true
      };

      if (!options.Parse(args))
      {
        return 1;
      }
      using var executionEngine = ExecutionEngine.CreateWithoutSharedCache(options);
      
      if (options.ProcessInfoFlags())
      {
        return 0;
      }

      if (options.Files.Count == 0)
      {
        options.Printer.ErrorWriteLine(Console.Out, "*** Error: No input files were specified.");
        return 1;
      }

      List<string> fileList = GetFileList(options);
      if (fileList == null)
      {
        return 1;
      }

      if (options.XmlSink != null)
      {
        string errMsg = options.XmlSink.Open();
        if (errMsg != null)
        {
          options.Printer.ErrorWriteLine(Console.Out, "*** Error: " + errMsg);
          return 1;
        }
      }

      if (options.ShowEnv == ExecutionEngineOptions.ShowEnvironment.Always)
      {
        Console.WriteLine("---Command arguments");
        foreach (string arg in args)
        {
          Contract.Assert(arg != null);
          Console.WriteLine(arg);
        }

        Console.WriteLine("--------------------");
      }

      Helpers.ExtraTraceInformation(options, "Becoming sentient");

      var success = executionEngine.ProcessFiles(Console.Out, fileList).Result;

      if (options.XmlSink != null)
      {
        options.XmlSink.Close();
      }

      if (options.Wait)
      {
        Console.WriteLine("Press Enter to exit.");
        Console.ReadLine();
      }

      return success ? 0 : 1;
    }

    private static List<string> GetFileList(CommandLineOptions options)
    {
      List<string> fileList = new List<string>();
      foreach (string file in options.Files)
      {
        string extension = Path.GetExtension(file);
        if (extension != null)
        {
          extension = extension.ToLower();
        }

        if (extension == ".txt")
        {
          StreamReader stream = new StreamReader(file);
          string s = stream.ReadToEnd();
          fileList.AddRange(s.Split(new char[3] { ' ', '\n', '\r' }, StringSplitOptions.RemoveEmptyEntries));
        }
        else
        {
          fileList.Add(file);
        }
      }

      foreach (string file in fileList)
      {
        Contract.Assert(file != null);
        string extension = Path.GetExtension(file);
        if (extension != null)
        {
          extension = extension.ToLower();
        }

        if (extension != ".bpl")
        {
          options.Printer.ErrorWriteLine(
            Console.Out,
            "*** Error: '{0}': Filename extension '{1}' is not supported. Input files must be BoogiePL programs (.bpl).",
            file,
            extension == null ? string.Empty : extension);
          return null;
        }
      }

      return fileList;
    }
  }
}
