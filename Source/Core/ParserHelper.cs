using System.Text;
using System.Collections.Generic;
using System.IO;
using System.Diagnostics.Contracts;

namespace Microsoft.Boogie
{
  public static class ParserHelper
  {
    struct ReadState
    {
      public bool hasSeenElse;
      public bool mayStillIncludeAnotherAlternative;

      public ReadState(bool hasSeenElse, bool mayStillIncludeAnotherAlternative)
      {
        this.hasSeenElse = hasSeenElse;
        this.mayStillIncludeAnotherAlternative = mayStillIncludeAnotherAlternative;
      }
    }

    // "arg" is assumed to be trimmed
    private static bool IfdefConditionSaysToInclude(string arg, List<string /*!*/> /*!*/ defines)
    {
      Contract.Requires(arg != null);
      Contract.Requires(Cce.NonNullElements(defines));
      bool sense = true;
      while (arg.StartsWith("!"))
      {
        sense = !sense;
        arg = arg.Substring(1).TrimStart();
      }

      return defines.Contains(arg) == sense;
    }

    public static string Fill(Stream stream, List<string /*!*/> /*!*/ defines)
    {
      Contract.Requires(stream != null);
      Contract.Requires(Cce.NonNullElements(defines));
      Contract.Ensures(Contract.Result<string>() != null);
      StreamReader /*!*/
        reader = new StreamReader(stream);
      return Fill(reader, defines);
    }

    public static string Fill(TextReader reader, List<string /*!*/> /*!*/ defines)
    {
      Contract.Requires(reader != null);
      Contract.Requires(Cce.NonNullElements(defines));
      Contract.Ensures(Contract.Result<string>() != null);
      StringBuilder sb = new StringBuilder();
      List<ReadState> /*!*/
        readState = new List<ReadState>(); // readState.Count is the current nesting level of #if's
      int ignoreCutoff =
        -1; // -1 means we're not ignoring; for 0<=n, n means we're ignoring because of something at nesting level n
      while (true)
        //invariant -1 <= ignoreCutoff && ignoreCutoff < readState.Count;
      {
        string s = reader.ReadLine();
        if (s == null)
        {
          if (readState.Count != 0)
          {
            sb.AppendLine("#MalformedInput: missing #endif");
          }

          break;
        }

        string t = s.Trim();
        if (t.StartsWith("#if"))
        {
          ReadState rs = new ReadState(false, false);
          if (ignoreCutoff != -1)
          {
            // we're already in a state of ignoring, so continue to ignore
          }
          else if (IfdefConditionSaysToInclude(t.Substring(3).TrimStart(), defines))
          {
            // include this branch
          }
          else
          {
            ignoreCutoff = readState.Count; // start ignoring
            rs.mayStillIncludeAnotherAlternative = true; // allow some later "elsif" or "else" branch to be included
          }

          readState.Add(rs);
          sb.AppendLine(); // ignore the #if line
        }
        else if (t.StartsWith("#elsif"))
        {
          ReadState rs;
          if (readState.Count == 0 || (rs = readState[readState.Count - 1]).hasSeenElse)
          {
            sb.AppendLine("#MalformedInput: misplaced #elsif"); // malformed input
            break;
          }

          if (ignoreCutoff == -1)
          {
            // we had included the previous branch
            //Contract.Assert(!rs.mayStillIncludeAnotherAlternative);
            ignoreCutoff = readState.Count - 1; // start ignoring
          }
          else if (rs.mayStillIncludeAnotherAlternative &&
                   IfdefConditionSaysToInclude(t.Substring(6).TrimStart(), defines))
          {
            // include this branch, but no subsequent branch at this level
            ignoreCutoff = -1;
            rs.mayStillIncludeAnotherAlternative = false;
            readState[readState.Count - 1] = rs;
          }

          sb.AppendLine(); // ignore the #elsif line
        }
        else if (t == "#else")
        {
          ReadState rs;
          if (readState.Count == 0 || (rs = readState[readState.Count - 1]).hasSeenElse)
          {
            sb.AppendLine("#MalformedInput: misplaced #else"); // malformed input
            break;
          }

          rs.hasSeenElse = true;
          if (ignoreCutoff == -1)
          {
            // we had included the previous branch
            //Contract.Assert(!rs.mayStillIncludeAnotherAlternative);
            ignoreCutoff = readState.Count - 1; // start ignoring
          }
          else if (rs.mayStillIncludeAnotherAlternative)
          {
            // include this branch
            ignoreCutoff = -1;
            rs.mayStillIncludeAnotherAlternative = false;
          }

          readState[readState.Count - 1] = rs;
          sb.AppendLine(); // ignore the #else line
        }
        else if (t == "#endif")
        {
          if (readState.Count == 0)
          {
            sb.AppendLine("#MalformedInput: misplaced #endif"); // malformed input
            break;
          }

          readState.RemoveAt(readState.Count - 1); // pop
          if (ignoreCutoff == readState.Count)
          {
            // we had ignored the branch that ends here; so, now we start including again
            ignoreCutoff = -1;
          }

          sb.AppendLine(); // ignore the #endif line
        }
        else if (ignoreCutoff == -1)
        {
          sb.AppendLine(s); // included line
        }
        else
        {
          sb.AppendLine(); // ignore the line
        }
      }

      return sb.ToString();
    }
  }
}