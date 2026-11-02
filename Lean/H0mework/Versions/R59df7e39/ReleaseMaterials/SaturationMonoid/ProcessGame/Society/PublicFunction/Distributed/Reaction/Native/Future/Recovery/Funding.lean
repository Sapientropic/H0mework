import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Future.Recovery.Runtime

set_option autoImplicit false
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Future.Recovery.Funding
open Institutions.Capitalism.Universal.Source.Program

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (old : Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)) (oldDepth : Nat) (word : List (Action old))

/-- The actual failed source cut is retained, rather than replaced by a missing report. -/
inductive Failure where
  | unsupported (cursor : Cursor old oldDepth word) (fee : List (Action old))
      (outside : fee ∉ words cursor.source.val.code.actions cursor.source.val.code.actionLimit)
  | unpaid (cursor : Cursor old oldDepth word) (fee : List (Action old))
      (supported : fee ∈ words cursor.source.val.code.actions cursor.source.val.code.actionLimit)
      (refused : (cursor.feePath fee).succeeded = false)

  | workload (cursor : Cursor old oldDepth word) (position : Nat)
      (made : Metering.Stage cursor position)
      (failed : made.result.FundingFailed)

  | quoted (cursor : Cursor old oldDepth word) (position : Metering.Quoted.Fees (Action old))
      (made : Metering.Quoted.Stage cursor position)
      (failed : made.result.FundingFailed)

variable {old oldDepth word}

def ofWalk : {cursor : Cursor old oldDepth word} → Walk cursor → Option (Failure old oldDepth word)
  | _,.finished .. | _,.blocked .. => none
  | _,.unsupported cursor fee outside => some (.unsupported cursor fee outside)
  | _,.unpaid cursor fee supported refused => some (.unpaid cursor fee supported refused)
  | _,.billed _ _ _ _ later | _,.advanced _ _ _ _ _ later => ofWalk later
  | _,.workloadAdvanced _ _ _ _ later => ofWalk later
  | _,.workloadStopped cursor position made _ =>
      if failed : made.result.FundingFailed then some (.workload cursor position made failed) else none
  | _,.quotedAdvanced _ _ _ _ later => ofWalk later
  | _,.quotedStopped cursor position made _ =>
      if failed : made.result.FundingFailed then some (.quoted cursor position made failed) else none

end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Future.Recovery.Funding
