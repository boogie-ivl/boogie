using System;
using System.Collections.Concurrent;
using System.Collections.Generic;
using System.Diagnostics.Contracts;

namespace Microsoft.Boogie
{
  public class Helpers
  {
    public static string BeautifyBplString(string s)
    {
      Contract.Requires(s != null);
      Contract.Ensures(Contract.Result<string>() != null);
      // strip "^" if it is the first character, change "$result" to "result"
      if (s.StartsWith("^") || s == "$result")
      {
        s = s.Substring(1);
      }
      else if (s.StartsWith("call"))
      {
        s = s.Substring(s.IndexOf('@') + 1);
        if (s.StartsWith("formal@"))
        {
          s = "(value of formal parameter: " + s.Substring(7) + ")";
        }
      }

      // strip "$in" from the end of identifier names
      if (s.EndsWith("$in"))
      {
        return "(initial value of: " + s.Substring(0, s.Length - 3) + ")";
      }
      else
      {
        return s;
      }
    }

    public static string PrettyPrintBplExpr(Expr e)
    {
      Contract.Requires(e != null);
      Contract.Ensures(Contract.Result<string>() != null);
      // anything that is unknown will just be printed via ToString
      // OldExpr and QuantifierExpr, BvExtractExpr, BvConcatExpr are ignored for now
      // LiteralExpr is printed as itself by ToString
      if (e is IdentifierExpr)
      {
        string s = e.ToString();
        return Helpers.BeautifyBplString(s);
      }
      else if (e is NAryExpr)
      {
        NAryExpr ne = (NAryExpr) e;
        IAppliable fun = ne.Fun;
        var eSeq = ne.Args;
        if (fun != null)
        {
          if ((fun.FunctionName == "$Length" || fun.FunctionName == "$StringLength") && eSeq.Count == 1)
          {
            Expr e0 = eSeq[0];
            if (e0 != null)
            {
              string s0 = PrettyPrintBplExpr(e0);
              return s0 + ".Length";
            }

            //unexpected, just fall outside to the default
          }
          else if (fun.FunctionName == "$typeof" && eSeq.Count == 1)
          {
            Expr e0 = eSeq[0];
            if (e0 != null)
            {
              string s0 = PrettyPrintBplExpr(e0);
              return "(the dynamic type of: " + s0 + ")";
            }

            //unexpected, just fall outside to the default
          }
          else if (fun.FunctionName == "IntArrayGet" && eSeq.Count == 2)
          {
            Expr e0 = eSeq[0];
            Expr e1 = eSeq[1];
            if (e0 != null && e1 != null)
            {
              string s0 = PrettyPrintBplExpr(e0);
              string s1 = PrettyPrintBplExpr(e1);
              return s0 + "[" + s1 + "]";
            }

            //unexpected, just fall outside to the default
          }
          else if (fun.FunctionName == "$Is" && eSeq.Count == 2)
          {
            Expr e0 = eSeq[0];
            Expr e1 = eSeq[1];
            if (e0 != null && e1 != null)
            {
              string s0 = PrettyPrintBplExpr(e0);
              string s1 = PrettyPrintBplExpr(e1);
              return "(" + s0 + " == null || (" + s0 + " is " + s1 + "))";
            }

            //unexpected, just fall outside to the default
          }
          else if (fun.FunctionName == "$IsNotNull" && eSeq.Count == 2)
          {
            Expr e0 = eSeq[0];
            Expr e1 = eSeq[1];
            if (e0 != null && e1 != null)
            {
              string s0 = PrettyPrintBplExpr(e0);
              string s1 = PrettyPrintBplExpr(e1);
              return "(" + s0 + " is " + s1 + ")";
            }

            //unexpected, just fall outside to the default
          }
          else if (fun is MapSelect && eSeq.Count <= 3)
          {
            // only maps with up to two arguments are supported right now (here)
            if (Cce.NonNull(eSeq[0]).ToString() == "$Heap")
            {
              //print Index0.Index1, unless Index1 is "$elements", then just print Index0
              string s0 = PrettyPrintBplExpr(Cce.NonNull(eSeq[1]));
              if (eSeq.Count > 2)
              {
                string s1 = PrettyPrintBplExpr(Cce.NonNull(eSeq[2]));
                if (s1 == "$elements")
                {
                  return s0;
                }
                else
                {
                  if (eSeq[2] is IdentifierExpr)
                  {
                    // strip the class name out of a fieldname
                    s1 = s1.Substring(s1.LastIndexOf('.') + 1);
                  }

                  return s0 + "." + s1;
                }
              }
            }

            //unexpected, just fall outside to the default
          }
          else if (fun is Microsoft.Boogie.BinaryOperator && eSeq.Count == 2)
          {
            Microsoft.Boogie.BinaryOperator f = (Microsoft.Boogie.BinaryOperator) fun;
            Expr e0 = eSeq[0];
            Expr e1 = eSeq[1];
            if (e0 != null && e1 != null)
            {
              string s0 = PrettyPrintBplExpr(e0);
              string s1 = PrettyPrintBplExpr(e1);
              string op = "";
              switch (f.Op)
              {
                case Microsoft.Boogie.BinaryOperator.Opcode.Add:
                  op = " + ";
                  break;
                case Microsoft.Boogie.BinaryOperator.Opcode.And:
                  op = " && ";
                  break;
                case Microsoft.Boogie.BinaryOperator.Opcode.Div:
                  op = " div ";
                  break;
                case Microsoft.Boogie.BinaryOperator.Opcode.Eq:
                  op = " == ";
                  break;
                case Microsoft.Boogie.BinaryOperator.Opcode.Ge:
                  op = " >= ";
                  break;
                case Microsoft.Boogie.BinaryOperator.Opcode.Gt:
                  op = " > ";
                  break;
                case Microsoft.Boogie.BinaryOperator.Opcode.Iff:
                  op = " <==> ";
                  break;
                case Microsoft.Boogie.BinaryOperator.Opcode.Imp:
                  op = " ==> ";
                  break;
                case Microsoft.Boogie.BinaryOperator.Opcode.Le:
                  op = " <= ";
                  break;
                case Microsoft.Boogie.BinaryOperator.Opcode.Lt:
                  op = " < ";
                  break;
                case Microsoft.Boogie.BinaryOperator.Opcode.Mod:
                  op = " mod ";
                  break;
                case Microsoft.Boogie.BinaryOperator.Opcode.Mul:
                  op = " * ";
                  break;
                case Microsoft.Boogie.BinaryOperator.Opcode.Neq:
                  op = " != ";
                  break;
                case Microsoft.Boogie.BinaryOperator.Opcode.Or:
                  op = " || ";
                  break;
                case Microsoft.Boogie.BinaryOperator.Opcode.Pow:
                  op = " ** ";
                  break;
                case Microsoft.Boogie.BinaryOperator.Opcode.RealDiv:
                  op = " / ";
                  break;
                case Microsoft.Boogie.BinaryOperator.Opcode.Sub:
                  op = " - ";
                  break;
                default:
                  op = " ";
                  break;
              }

              return "(" + s0 + op + s1 + ")";
            }

            //unexpected, just fall outside to the default
          }
          else
          {
            string s = fun.FunctionName + "(";
            for (int i = 0; i < eSeq.Count; i++)
            {
              Expr ex = eSeq[i];
              Contract.Assume(ex != null);
              if (i > 0)
              {
                s += ", ";
              }

              string t = PrettyPrintBplExpr(ex);
              if (t.StartsWith("(") && t.EndsWith(")"))
              {
                t = t.Substring(1, t.Length - 2);
              }

              s += t;
            }

            s += ")";
            return s;
            //unexpected, just fall outside to the default
          }
        }
      }

      return e.ToString();
    }

    private static readonly DateTime StartUp = DateTime.UtcNow;

    public static void ExtraTraceInformation(CoreOptions options, string point)
    {
      Contract.Requires(point != null);
      if (options.TraceTimes)
      {
        DateTime now = DateTime.UtcNow;
        TimeSpan timeSinceStartUp = now - StartUp;
        options.OutputWriter.WriteLine(">>> {0}   [{1} s]", point, timeSinceStartUp.TotalSeconds);
      }
    }

    private static readonly ConcurrentDictionary<string, int> UsedLogNames = new();
    public static (string fileName, bool reused) GetLogFilename(string descriptiveName, string filename, bool allowReuse)
    {
      filename = SubstituteAtPROC(descriptiveName, Cce.NonNull(filename));

      var reused = false;
      var index = UsedLogNames.AddOrUpdate(filename, 0, (_, i) => {
        reused = allowReuse;
        return allowReuse ? i : i + 1;
      });
      var filenameWithIndex = index > 0 ? filename + "." + index : filename;

      return (filenameWithIndex, reused);
    }

    private static string SubstituteAtPROC(string descriptiveName, string filename)
    {
      Contract.Requires(filename != null);
      Contract.Requires(descriptiveName != null);
      Contract.Ensures(Contract.Result<string>() != null);
      var /*!*/ sb = new System.Text.StringBuilder(descriptiveName.Length);
      // quote the name, characters like ^ cause trouble in CMD
      // while $ could cause trouble in SH
      foreach (char c in descriptiveName)
      {
        if (Char.IsLetterOrDigit(c) || c == '.')
        {
          sb.Append(c);
        }
        else
        {
          sb.Append('_');
        }
      }

      string pn = sb.ToString();
      // We attempt to avoid filenames that are too long, but we only
      // do it by truncating the @PROC@ replacement, which leaves unchanged
      // any filename extension specified by the user.  We base our
      // calculations on that there is at most one occurrence of @PROC@.
      if (180 <= filename.Length - 6 + pn.Length)
      {
        pn = pn.Substring(0, Math.Max(180 - (filename.Length - 6), 0)) + "-n" +
             System.Threading.Interlocked.Increment(ref sequenceId);
      }

      return filename.Replace("@PROC@", pn);
    }

    private static int sequenceId = -1;
  }
}