using System;
using System.IO;
using System.Collections.Generic;
using System.Reflection;
using System.Text;
using System.Diagnostics.Contracts;

namespace Microsoft.Boogie
{
  public class ProverOptions
  {
    public SMTLibOptions LibOptions { get; }
    public string /*?*/ LogFilename = null;

    public bool AppendLogFile = false;

    public bool SeparateLogFiles = false;

    // Say (DBG_WAS_VALID) or (DBG_WAS_INVALID) after query
    public bool ForceLogStatus = false;
    public uint TimeLimit = 0;
    public uint ResourceLimit = 0;
    public int RandomSeed;
    public int MemoryLimit = 0;
    public int Verbosity = 0;
    public string ProverName;
    public string ProverPath;
    private string confirmedProverPath;
    public bool BatchMode;

    public List<Type> UsedTypes = new List<Type>()
      // Default to all the base types
      { Type.Int, Type.Real, Type.Bool, Type.RMode, Type.String, Type.RegEx };


    private string /*!*/
      stringRepr = "";

    public ProverOptions(SMTLibOptions libOptions)
    {
      this.LibOptions = libOptions;
    }

    [ContractInvariantMethod]
    void ObjectInvariant()
    {
      Contract.Invariant(stringRepr != null);
    }


    [Pure]
    public override string ToString()
    {
      Contract.Ensures(Contract.Result<string>() != null);
      return stringRepr;
    }

    // The usual thing to override.
    protected virtual bool Parse(string opt)
    {
      Contract.Requires(opt != null);
      return ParseString(opt, "PROVER_PATH", ref ProverPath) ||
             ParseString(opt, "PROVER_NAME", ref ProverName) ||
             ParseString(opt, "LOG_FILE", ref LogFilename) ||
             ParseBool(opt, "APPEND_LOG_FILE", ref AppendLogFile) ||
             ParseBool(opt, "FORCE_LOG_STATUS", ref ForceLogStatus) ||
             ParseInt(opt, "MEMORY_LIMIT", ref MemoryLimit) ||
             ParseInt(opt, "VERBOSITY", ref Verbosity) ||
             ParseUInt(opt, "TIME_LIMIT", ref TimeLimit) ||
             ParseBool(opt, "BATCH_MODE", ref BatchMode);
    }

    public virtual string Help
    {
      get
      {
        return
          @"
Generic prover options :
~~~~~~~~~~~~~~~~~~~~~~~
PROVER_PATH=<string>      Path to the prover to use.
PROVER_NAME=<string>      Name of the prover executable.
LOG_FILE=<string>         Log input for the theorem prover. The string @PROC@
                          in the filename causes there to be one prover log
                          file per verification condition, and is expanded to
                          the name of the procedure that the verification
                          condition is for.
APPEND_LOG_FILE=<bool>    Append, rather than overwrite the log file.
MEMORY_LIMIT=<int>        Memory limit of the prover in megabytes.
VERBOSITY=<int>           The higher, the more verbose.
TIME_LIMIT=<uint>         Time limit per verification condition in
                          milliseconds.
BATCH_MODE=<bool>         If true, send all solver input in one batch,
                          rather than incrementally.

The generic options may or may not be used by the prover plugin.
";
      }
    }

    public virtual void Parse(IEnumerable<string /*!*/> /*!*/ opts)
    {
      Contract.Requires(Cce.NonNullElements(opts));
      StringBuilder sb = new StringBuilder(stringRepr);
      Contract.Assert(sb != null);
      foreach (string /*!*/ opt in opts)
      {
        Contract.Assert(opt != null);
        if (!Parse(opt))
        {
          ReportError("Unrecognised prover option: " + opt);
        }

        sb.Append(opt).Append(" ");
      }

      stringRepr = sb.ToString();
      PostParse();
    }

    public virtual void PostParse()
    {
      if (LogFilename != null && LogFilename.Contains("@PROC@"))
      {
        SeparateLogFiles = true;
      }
    }

    static string CodebaseString()
    {
      Contract.Ensures(Contract.Result<string>() != null);
      return Path.GetDirectoryName(Cce.NonNull(System.Reflection.Assembly.GetExecutingAssembly().Location));
    }

    public string ExecutablePath()
    {
      Contract.Ensures(confirmedProverPath != null);

      if (confirmedProverPath != null)
      {
        return confirmedProverPath;
      }

      // Explicitly set path always has priority
      if (ProverPath != null)
      {
        if (!File.Exists(ProverPath))
        {
          throw new ProverException("Cannot find specified prover: " + ProverPath);
        }

        return ConfirmProverPath(ProverPath);
      }

      return ConfirmProverPath(ProverName);
    }

    private string ConfirmProverPath(string proverPath)
    {
      Contract.Requires(proverPath != null);
      Contract.Ensures(confirmedProverPath != null);
      confirmedProverPath = proverPath;
      if (LibOptions.Trace)
      {
        LibOptions.OutputWriter.WriteLine("[TRACE] Using prover: " + confirmedProverPath);
        if (BatchMode) {
          LibOptions.OutputWriter.WriteLine("[TRACE] Running in batch mode.");
        }
      }

      return confirmedProverPath;
    }

    protected void ReportError(string msg)
    {
      Contract.Requires(msg != null);
      throw new ProverOptionException(msg);
    }

    protected virtual bool ParseString(string opt, string name, ref string field)
    {
      Contract.Requires(name != null);
      Contract.Requires(opt != null);
      if (opt.Length >= name.Length && opt.StartsWith(name))
      {
        if (opt.Length == name.Length)
        {
          field = "";
          return true;
        }
        else if (opt[name.Length] == '=' || opt[name.Length] == ':')
        {
          field = opt.Substring(name.Length + 1);
          return true;
        }
      }

      return false;
    }

    protected virtual bool ParseBool(string opt, string name, ref bool field)
    {
      Contract.Requires(name != null);
      Contract.Requires(opt != null);
      string tmp = null;
      if (ParseString(opt, name, ref tmp))
      {
        switch (Cce.NonNull(tmp).ToLower())
        {
          case "1":
          case "true":
          case "":
            field = true;
            return true;
          case "0":
          case "false":
            field = false;
            return true;
          default:
            ReportError("Invalid Boolean option \"" + opt + "\"");
            return false;
        }
      }

      return false;
    }

    protected virtual bool ParseInt(string opt, string name, ref int field)
    {
      Contract.Requires(name != null);
      Contract.Requires(opt != null);
      string tmp = null;
      if (ParseString(opt, name, ref tmp))
      {
        if (int.TryParse(Cce.NonNull(tmp), out var t2))
        {
          field = t2;
          return true;
        }
        else
        {
          ReportError("Invalid integer option \"" + opt + "\"");
        }
      }

      return false;
    }

    protected virtual bool ParseUInt(string opt, string name, ref uint field)
    {
      Contract.Requires(name != null);
      Contract.Requires(opt != null);
      string tmp = null;
      if (ParseString(opt, name, ref tmp))
      {
        if (uint.TryParse(Cce.NonNull(tmp), out var t2))
        {
          field = t2;
          return true;
        }
        else
        {
          ReportError("Invalid unsigned integer option \"" + opt + "\"");
        }
      }

      return false;
    }

    public virtual TextWriter OpenLog(string /*?*/ descName)
    {
      if (LogFilename != null)
      {
        string filename = LogFilename;
        Contract.Assert(filename != null);
        if (descName != null)
        {
          filename = Helpers.GetLogFilename(descName, filename, true).fileName;
        }

        return new StreamWriter(filename, AppendLogFile);
      }
      else
      {
        return null;
      }
    }
  }

  [ContractClass(typeof(ProverFactoryContracts))]
  public abstract class ProverFactory
  {
    // Really returns ProverInterface.
    //public abstract object! SpawnProver(ProverOptions! options, object! ctxt);
    public abstract ProverInterface SpawnProver(SMTLibOptions libOptions, ProverOptions options, object ctxt);

    // Really returns ProverContext
    public abstract ProverContext /*!*/ NewProverContext(ProverOptions /*!*/ options);

    public virtual ProverOptions BlankProverOptions(SMTLibOptions libOptions)
    {
      Contract.Ensures(Contract.Result<ProverOptions>() != null);
      return new ProverOptions(libOptions);
    }

    // return true if the prover supports DAG AST as opposed to LET AST
    public virtual bool SupportsDags
    {
      get { return false; }
    }

    public virtual void Close()
    {
    }

    public static ProverFactory Load(string proverName)
    {
      Contract.Requires(proverName != null);
      Contract.Ensures(Contract.Result<ProverFactory>() != null);
      Contract.Ensures(Cce.IsNew(Contract.Result<ProverFactory>()) && Cce.Owner.New(Contract.Result<ProverFactory>()));
      string /*!*/
        path;
      if (proverName.IndexOf("/") >= 0 || proverName.IndexOf("\\") >= 0)
      {
        path = proverName;
      }
      else
      {
        string codebase = Cce.NonNull(System.IO.Path.GetDirectoryName(
          Cce.NonNull(System.Reflection.Assembly.GetExecutingAssembly().Location)));
        path = System.IO.Path.Combine(codebase, "Boogie.Provers." + proverName + ".dll");
      }

      Assembly asm = Cce.NonNull(Assembly.LoadFrom(path));
      string name = Cce.NonNull(asm.GetName().Name);
      System.Type factoryType =
        Cce.NonNull(asm.GetType("Microsoft.Boogie." + name.Replace("Boogie.Provers.", "") + ".Factory"));
      return Cce.NonNull((ProverFactory /*!*/) Activator.CreateInstance(factoryType));
    }
  }

  [ContractClassFor(typeof(ProverFactory))]
  public abstract class ProverFactoryContracts : ProverFactory
  {
    public override ProverContext NewProverContext(ProverOptions options)
    {
      Contract.Requires(options != null);
      Contract.Ensures(Contract.Result<object>() != null);

      throw new NotImplementedException();
    }
  }

  public class ProverException : Exception
  {
    public ProverException(string s)
      : base(s)
    {
    }
  }

  public class ProverOptionException : ProverException
  {
    public ProverOptionException(string msg)
      : base(msg)
    {
      Contract.Requires(msg != null);
    }
  }
}
