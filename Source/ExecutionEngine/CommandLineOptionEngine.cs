using System;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.IO;

namespace Microsoft.Boogie;

public class CommandLineOptionEngine
{
  public TextWriter OutputWriter { get; set; }
  public string ToolName { get; set; }
  public string DescriptiveToolName { get; set; }

  [ContractInvariantMethod]
  void ObjectInvariant()
  {
    Contract.Invariant(ToolName != null);
    Contract.Invariant(DescriptiveToolName != null);
    Contract.Invariant(this._environment != null);
    Contract.Invariant(Cce.NonNullElements(this._files));
    Contract.Invariant(this._fileTimestamp != null);
  }

  private string /*!*/ _environment = "";

  public string Environment
  {
    get
    {
      Contract.Ensures(Contract.Result<string>() != null);
      return this._environment;
    }
    set
    {
      Contract.Requires(value != null);
      this._environment = value;
    }
  }

  private readonly List<string /*!*/> /*!*/ _files = new List<string /*!*/>();

  public IList<string /*!*/> /*!*/ Files
  {
    get
    {
      Contract.Ensures(Cce.NonNullElements(Contract.Result<IList<string>>()));
      Contract.Ensures(Contract.Result<IList<string>>().IsReadOnly);
      return this._files.AsReadOnly();
    }
  }

  public bool VersionRequested = false;
  public bool HelpRequested = false;
  public bool AttributeHelpRequested = false;

  public CommandLineOptionEngine(string toolName, string descriptiveName, TextWriter outputWriter)
  {
    Contract.Requires(toolName != null);
    Contract.Requires(descriptiveName != null);
    ToolName = toolName;
    DescriptiveToolName = descriptiveName;
    OutputWriter = outputWriter;
  }

  public virtual string /*!*/ VersionNumber
  {
    get
    {
      Contract.Ensures(Contract.Result<string>() != null);
      return Cce.NonNull(Cce
        .NonNull(System.Diagnostics.FileVersionInfo.GetVersionInfo(System.Reflection.Assembly.GetExecutingAssembly()
          .Location)).FileVersion);
    }
  }

  public virtual string /*!*/ VersionSuffix
  {
    get
    {
      Contract.Ensures(Contract.Result<string>() != null);
      return " version " + VersionNumber + ", Copyright (c) 2003-2014, Microsoft.";
    }
  }

  public virtual string /*!*/ Version
  {
    get
    {
      Contract.Ensures(Contract.Result<string>() != null);
      return DescriptiveToolName + VersionSuffix;
    }
  }

  private string /*!*/
    _fileTimestamp = Cce.NonNull(DateTime.Now.ToString("o")).Replace(':', '.');

  public string FileTimestamp
  {
    get
    {
      Contract.Ensures(Contract.Result<string>() != null);
      return this._fileTimestamp;
    }
    set
    {
      Contract.Requires(value != null);
      this._fileTimestamp = value;
    }
  }

  public void ExpandFilename(string pattern, Action<string> setPattern, string logPrefix, string fileTimestamp)
  {
    if (pattern != null)
    {
      pattern = pattern.Replace("@PREFIX@", logPrefix).Replace("@TIME@", fileTimestamp);
      string fn = Files.Count == 0 ? "" : Files[Files.Count - 1];
      fn = Util.EscapeFilename(fn);
      setPattern(pattern.Replace("@FILE@", fn));
    }
  }

  /// <summary>
  /// Process the option and modify "ps" accordingly.
  /// Return true if the option is one that is recognized.
  /// </summary>
  protected virtual bool ParseOption(string name, CommandLineParseState ps)
  {
    Contract.Requires(name != null);
    Contract.Requires(ps != null);

    if (ps.CheckBooleanFlag("version", ref VersionRequested) ||
        ps.CheckBooleanFlag("help", ref HelpRequested) ||
        ps.CheckBooleanFlag("?", ref HelpRequested) ||
        ps.CheckBooleanFlag("attrHelp", ref AttributeHelpRequested))
    {
      return true;
    }

    return false; // unrecognized option
  }

  protected virtual string HelpHeader =>
    $"Usage: {ToolName} [ option ... ] [ filename ... ]" + @"

  ---- General options -------------------------------------------------------

  /version      print the " + ToolName + @" version number
  /help         print this message
  /attrHelp     print a message about supported declaration attributes";

  protected virtual string HelpBody => "";

  public virtual string Help =>
    HelpHeader + HelpBody;

  public virtual string AttributeHelp => "";

  /// <summary>
  /// This method is called after all parsing is done, if no parse errors were encountered.
  /// </summary>
  public virtual void ApplyDefaultOptions()
  {
  }

  public virtual bool ProcessInfoFlags()
  {
    if (VersionRequested)
    {
      OutputWriter.WriteLine(Version);
      return true;
    }
    if (HelpRequested)
    {
      OutputWriter.WriteLine(Help);
      return true;
    }
    if (AttributeHelpRequested)
    {
      OutputWriter.WriteLine(AttributeHelp);
      return true;
    }
    return false;
  }

  /// <summary>
  /// Parses the command-line arguments "args" into the global flag variables.  Returns true
  /// if there were no errors.
  /// </summary>
  public virtual bool Parse(string[] /*!*/ args)
  {
    Contract.Requires(Cce.NonNullElements(args));

    // save the command line options for the log files
    Environment += "Command Line Options: " + string.Join(" ", args);
    args = Cce.NonNull((string[]) args.Clone()); // the operations performed may mutate the array, so make a copy
    var ps = InitializeCommandLineParseState(args);

    while (ps.i < args.Length)
    {
      Cce.LoopInvariant(ps.args == args);
      string arg = args[ps.i];
      Contract.Assert(arg != null);
      ps.s = arg.Trim();

      bool isOption = ps.s.StartsWith("-") || ps.s.StartsWith("/");
      int colonIndex = ps.s.IndexOf(':');
      if (0 <= colonIndex && isOption)
      {
        ps.hasColonArgument = true;
        args[ps.i] = ps.s.Substring(colonIndex + 1);
        ps.s = ps.s.Substring(0, colonIndex);
      }
      else
      {
        ps.i++;
        ps.hasColonArgument = false;
      }

      ps.nextIndex = ps.i;

      if (isOption)
      {
        if (!ParseOption(ps.s.Substring(1), ps))
        {
          if (Path.DirectorySeparatorChar == '/' && ps.s.StartsWith("/"))
          {
            AddFile(arg, ps);
          }
          else
          {
            UnknownSwitch(ps);
          }
        }
      }
      else
      {
        AddFile(arg, ps);
      }

      ps.i = ps.nextIndex;
    }

    if (ps.EncounteredErrors)
    {
      Console.Error.WriteLine("Use /help for available options");
      return false;
    }
    else
    {
      this.ApplyDefaultOptions();
      return true;
    }
  }

  protected virtual void UnknownSwitch(CommandLineParseState ps) {
    ps.Error("unknown switch: {0}", ps.s);
  }

  protected virtual void AddFile(string file, CommandLineParseState ps) {
    this._files.Add(file);
  }

  protected virtual CommandLineParseState InitializeCommandLineParseState(string[] args) {
    return new CommandLineParseState(args, ToolName);
  }
}