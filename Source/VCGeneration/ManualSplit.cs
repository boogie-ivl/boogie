using System;
using System.Collections.Generic;
using Microsoft.Boogie;

namespace VC;

public class ManualSplit : Split
{

  public IToken Token { get; }


  public ManualSplit(VCGenOptions options, 
    List<Block> blocks, 
    Dictionary<TransferCmd, ReturnCmd> gotoCmdOrigins, 
    VerificationConditionGenerator par, 
    ImplementationRun run, 
    IToken token, int? randomSeed = null) 
    : base(options, blocks, gotoCmdOrigins, par, run, randomSeed)
  {
    Token = token;
  }
}