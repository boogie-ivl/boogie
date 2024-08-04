using System.Collections.Generic;
using System.IO;
using System.Diagnostics.Contracts;

namespace Boogie.Util
{
  public class TeeWriter : TextWriter
  {
    readonly TextWriter /*!*/
      a;

    readonly TextWriter /*!*/
      b;

    [ContractInvariantMethod]
    void ObjectInvariant()
    {
      Contract.Invariant(a != null);
      Contract.Invariant(b != null);
    }


    public TeeWriter(TextWriter a, TextWriter b)
    {
      Contract.Requires(b != null);
      Contract.Requires(a != null);
      this.a = a;
      this.b = b;
    }

    public override System.Text.Encoding Encoding
    {
      get { return a.Encoding; }
    }

    public override void Close()
    {
      a.Close();
      b.Close();
    }

    public override void Flush()
    {
      a.Flush();
      b.Flush();
    }

    [Pure]
    public override string ToString()
    {
      Contract.Ensures(Contract.Result<string>() != null);
      return "<TeeWriter: " + a.ToString() + ", " + b.ToString() + ">";
    }

    public override void Write(char ch)
    {
      a.Write(ch);
      b.Write(ch);
    }

    public override void Write(string s)
    {
      a.Write(s);
      b.Write(s);
    }
  }

  /// <summary>
  /// A LineReader is a class that allows further subclasses to just override the ReadLine() method.
  /// It simply reads from the given "reader".
  /// </summary>
  public class LineReader : TextReader
  {
    [Rep] readonly TextReader /*!*/ reader;

    [ContractInvariantMethod]
    void ObjectInvariant()
    {
      Contract.Invariant(reader != null);
      Contract.Invariant(readAhead == null || (0 <= readAheadConsumed && readAheadConsumed < readAhead.Length));
    }

    string readAhead;
    int readAheadConsumed;


    public LineReader([Captured] TextReader reader)
    {
      Contract.Requires(reader != null);
      this.reader = reader;
    }

    public override void Close()
    {
      Cce.BeginExpose(this);
      {
        reader.Close();
      }
      Cce.EndExpose();
    }

    public override int Read()
    {
      Cce.BeginExpose(this);
      try
      {
        while (readAhead == null)
        {
          readAhead = reader.ReadLine();
          if (readAhead == null)
          {
            // we're at EOF
            return -1;
          }
          else if (readAhead.Length > 0)
          {
            readAheadConsumed = 0;
            break;
          }
        }

        int res = readAhead[readAheadConsumed++];
        if (readAheadConsumed == readAhead.Length)
        {
          readAhead = null;
        }

        return res;
      }
      finally
      {
        Cce.EndExpose();
      }
    }

    public override int Read(char[] buffer, int index, int count)
    {
      int n = 0;
      for (; n < count; n++)
      {
        int ch = Read();
        if (ch == -1)
        {
          break;
        }

        buffer[index + n] = (char) ch;
      }

      return n;
    }

    public override string ReadLine()
    {
      string res;
      if (readAhead != null)
      {
        Cce.BeginExpose(this);
        {
          res = readAhead.Substring(readAheadConsumed);
          readAhead = null;
        }
        Cce.EndExpose();
      }
      else
      {
        res = reader.ReadLine();
      }

      return res;
    }
  }

  public class IfdefReader : LineReader
  {
    [Rep] readonly List<string /*!*/> /*!*/ defines;
    [Rep] readonly List<bool> /*!*/ readState = new List<bool>();
    int ignoreCutoff = 0; // 0 means we're not ignoring

    [ContractInvariantMethod]
    void ObjectInvariant()
    {
      Contract.Invariant(readState != null);
      Contract.Invariant(Cce.NonNullElements(defines));
      Contract.Invariant(0 <= ignoreCutoff && ignoreCutoff <= readState.Count);
    }


    public IfdefReader([Captured] TextReader reader, [Captured] List<string /*!*/> /*!*/ defines)
      : base(reader)
    {
      Contract.Requires(reader != null);
      Contract.Requires(Cce.NonNullElements(defines));
      this.defines = defines;
    }

    public override string ReadLine()
    {
      while (true)
      {
        string s = base.ReadLine();
        if (s == null)
        {
          return s;
        }

        string t = s.Trim();
        if (t.StartsWith("#if"))
        {
          string arg = t.Substring(3).TrimStart();
          bool sense = true;
          while (t.StartsWith("!"))
          {
            sense = !sense;
            t = t.Substring(1).TrimStart();
          }

          // push "true", since we're in a "then" branch
          readState.Add(true);
          if (ignoreCutoff == 0 && defines.Contains(arg) != sense)
          {
            ignoreCutoff = readState.Count; // start ignoring
          }
        }
        else if (t == "#else")
        {
          if (readState.Count == 0 || !readState[readState.Count - 1])
          {
            return s; // malformed input; return the read line as if it were not special
          }

          // change the "true" to a "false" on top of the state, since we're now going into the "else" branch
          readState[readState.Count - 1] = false;
          if (ignoreCutoff == 0)
          {
            // the "then" branch had been included, so we'll ignore the "else" branch
            ignoreCutoff = readState.Count;
          }
          else if (ignoreCutoff == readState.Count)
          {
            // we had ignored the "then" branch, so we'll include the "else" branch
            ignoreCutoff = 0;
          }
        }
        else if (t == "#endif")
        {
          if (readState.Count == 0)
          {
            return s; // malformed input; return the read line as if it were not special
          }

          if (ignoreCutoff == readState.Count)
          {
            // we had ignored the branch that ends here; so, now we start including again
            ignoreCutoff = 0;
          }

          // pop
          readState.RemoveAt(readState.Count - 1);
        }
        else if (ignoreCutoff == 0)
        {
          return s;
        }
      }
    }
  }
}