using System;
using System.Text;
using System.Diagnostics.Contracts;
using BIM = System.Numerics.BigInteger;

namespace Microsoft.BaseTypes
{
  /// <summary>
  /// A thin wrapper around System.Numerics.BigInteger
  /// (to be able to define equality, etc. properly)
  /// </summary>
  public struct BigNum
  {
    // the internal representation
    [Rep] internal readonly System.Numerics.BigInteger val;
    public static readonly BigNum ZERO = new BigNum(BIM.Zero);
    public static readonly BigNum ONE = new BigNum(BIM.One);
    public static readonly BigNum MINUS_ONE = new BigNum(-BIM.One);

    [Pure]
    public static BigNum FromInt(int v)
    {
      return new BigNum(new BIM(v));
    }

    [Pure]
    public static BigNum FromUInt(uint v)
    {
      return new BigNum(new BIM((long) v));
    }

    [Pure]
    public static BigNum FromLong(long v)
    {
      return new BigNum(new BIM(v));
    }

    [Pure]
    public static BigNum FromBigInt(System.Numerics.BigInteger v)
    {
      return new BigNum(v);
    }

    [Pure]
    public static BigNum FromULong(ulong v)
    {
      return FromString("" + v);
    }

    [Pure]
    public static BigNum FromString(string v)
    {
      try
      {
        return new BigNum(BIM.Parse(v));
      }
      catch (System.ArgumentException)
      {
        throw new FormatException();
      }
    }

    public static bool TryParse(string v, out BigNum res)
    {
      try
      {
        res = BigNum.FromString(v);
        return true;
      }
      catch (FormatException)
      {
        res = ZERO;
        return false;
      }
    }

    // Convert to int, without checking whether overflows occur
    public int ToInt
    {
      get { return (int) val; }
    }

    public BIM ToBigInteger
    {
      get { return val; }
    }

    // Convert to int; assert that no overflows occur
    public int ToIntSafe
    {
      get
      {
        Contract.Assert(this.InInt32);
        return this.ToInt;
      }
    }

    public Rational ToRational
    {
      get { return Rational.FromBignum(this); }
    }

    public byte[] ToByteArray()
    {
      return this.val.ToByteArray();
    }

    internal BigNum(System.Numerics.BigInteger val)
    {
      this.val = val;
    }

    public static bool operator ==(BigNum x, BigNum y)
    {
      return (x.val == y.val);
    }

    public static bool operator !=(BigNum x, BigNum y)
    {
      return !(x.val == y.val);
    }

    [Pure]
    [Reads(ReadsAttribute.Reads.Nothing)]
    public override bool Equals(object obj)
    {
      if (obj == null)
      {
        return false;
      }

      if (!(obj is BigNum))
      {
        return false;
      }

      BigNum other = (BigNum) obj;
      return (this.val == other.val);
    }

    [Pure]
    public override int GetHashCode()
    {
      return this.val.GetHashCode();
    }

    [Pure]
    public override string /*!*/ ToString()
    {
      Contract.Ensures(Contract.Result<string>() != null);
      return Cce.NonNull(val.ToString());
    }

    //////////////////////////////////////////////////////////////////////////////
    // Very limited support for format strings
    // Note: Negative integers are linearised with a minus "-" in hexadecimal,
    // not in 2-complement notation (in contrast to what the method
    // int32.ToString(format) does) 

    [Pure]
    public string /*!*/ ToString(string /*!*/ format)
    {
      Contract.Requires(format != null);
      Contract.Ensures(Contract.Result<string>() != null);
      if (format.StartsWith("d") || format.StartsWith("D"))
      {
        string res = this.Abs.ToString();
        Contract.Assert(res != null);
        return addMinus(this.Signum,
          prefixWithZeros(extractPrecision(format), res));
      }
      else if (format.StartsWith("x") || format.StartsWith("X"))
      {
        string res = this.toHex(format.Substring(0, 1));
        Contract.Assert(res != null);
        return addMinus(this.Signum,
          prefixWithZeros(extractPrecision(format), res));
      }
      else
      {
        throw new FormatException("Format " + format + " is not supported");
      }
    }

    private static readonly System.Numerics.BigInteger BI_2_TO_24 = new BIM(0x1000000);

    [Pure]
    private string /*!*/ toHex(string /*!*/ format)
    {
      Contract.Requires(format != null);
      Contract.Ensures(Contract.Result<string>() != null);
      string res = "";
      System.Numerics.BigInteger rem = this.Abs.val;

      while (rem > BIM.Zero)
      {
        res = ((int) (rem % BI_2_TO_24)).ToString(format) + res;
        rem = rem / BI_2_TO_24;
      }

      return res;
    }

    [Pure]
    private int extractPrecision(string /*!*/ format)
    {
      Contract.Requires(format != null);
      if (format.Length > 1)
      {
        // will throw a FormatException if the precision is invalid;
        // that is ok
        return Int32.Parse(format.Substring(1));
      }
      // always output at least one digit
      return 1;
    }

    [Pure]
    private string /*!*/ addMinus(int signum, string /*!*/ suffix)
    {
      Contract.Requires(suffix != null);
      Contract.Ensures(Contract.Result<string>() != null);
      if (signum < 0)
      {
        return "-" + suffix;
      }

      return suffix;
    }

    [Pure]
    private string /*!*/ prefixWithZeros(int minLength, string /*!*/ suffix)
    {
      Contract.Requires(suffix != null);
      Contract.Ensures(Contract.Result<string>() != null);
      StringBuilder res = new StringBuilder();
      while (res.Length + suffix.Length < minLength)
      {
        res.Append("0");
      }

      res.Append(suffix);
      return res.ToString();
    }

    ////////////////////////////////////////////////////////////////////////////
    // Basic arithmetic operations

    public BigNum Abs
    {
      get { return new BigNum(BIM.Abs(this.val)); }
    }

    public BigNum Neg
    {
      get { return new BigNum(-this.val); }
    }

    [Pure]
    public static BigNum operator -(BigNum x)
    {
      return x.Neg;
    }

    [Pure]
    public static BigNum operator +(BigNum x, BigNum y)
    {
      return new BigNum(x.val + y.val);
    }

    [Pure]
    public static BigNum operator -(BigNum x, BigNum y)
    {
      return new BigNum(x.val - y.val);
    }

    [Pure]
    public static BigNum operator *(BigNum x, BigNum y)
    {
      return new BigNum(x.val * y.val);
    }

    // TODO: check that this has a proper semantics (which? :-))
    [Pure]
    public static BigNum operator /(BigNum x, BigNum y)
    {
      return new BigNum(x.val / y.val);
    }

    // TODO: check that this has a proper semantics (which? :-))
    [Pure]
    public static BigNum operator %(BigNum x, BigNum y)
    {
      return new BigNum(x.val - ((x.val / y.val) * y.val));
    }

    [Pure]
    public BigNum Min(BigNum that)
    {
      return new BigNum(this.val <= that.val ? this.val : that.val);
    }

    [Pure]
    public BigNum Max(BigNum that)
    {
      return new BigNum(this.val >= that.val ? this.val : that.val);
    }

    /// <summary>
    /// Returns the greatest common divisor of this and _y.
    /// </summary>
    /// <param name="_y"></param>
    /// <returns></returns>
    public BigNum Gcd(BigNum _y)
    {
      Contract.Ensures(!Contract.Result<BigNum>().IsNegative);
      BigNum x = this.Abs;
      BigNum y = _y.Abs;

      while (true)
      {
        if (x < y)
        {
          y = y % x;
          if (y.IsZero)
          {
            return x;
          }
        }
        else
        {
          x = x % y;
          if (x.IsZero)
          {
            return y;
          }
        }
      }
    }

    ////////////////////////////////////////////////////////////////////////////
    // Some basic comparison operations

    public int Signum
    {
      get { return this.val.Sign; }
    }

    public bool IsPositive
    {
      get { return (this.val > BIM.Zero); }
    }

    public bool IsNegative
    {
      get { return (this.val < BIM.Zero); }
    }

    public bool IsZero
    {
      get { return this.val.IsZero; }
    }

    [Pure]
    public int CompareTo(BigNum that)
    {
      if (this.val == that.val)
      {
        return 0;
      }

      if (this.val < that.val)
      {
        return -1;
      }

      return 1;
    }

    [Pure]
    public static bool operator <(BigNum x, BigNum y)
    {
      return (x.val < y.val);
    }

    [Pure]
    public static bool operator >(BigNum x, BigNum y)
    {
      return (x.val > y.val);
    }

    [Pure]
    public static bool operator <=(BigNum x, BigNum y)
    {
      return (x.val <= y.val);
    }

    [Pure]
    public static bool operator >=(BigNum x, BigNum y)
    {
      return (x.val >= y.val);
    }


    private static readonly System.Numerics.BigInteger MaxInt32 =
      new BIM(Int32.MaxValue);

    private static readonly System.Numerics.BigInteger MinInt32 =
      new BIM(Int32.MinValue);

    public bool InInt32
    {
      get { return (val >= MinInt32) && (val <= MaxInt32); }
    }
  }
}