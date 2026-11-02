import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Normalization.Source
import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Challenge

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Normalization.RawAuthority

open Distributed Distributed.Reaction Distributed.Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Institutions.Capitalism.Universal.Source.ProgrammeFace

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (bound : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (input : Input bound.source.code) (cut : Nat)

def candidate (rival : Opponent bound.source.code) (term : List (Option bound.source.code.Policy)) :
    Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
      (Technology := Technology) (Instrument := Instrument) :=
  {bound with source := Future.target bound.source input cut rival term}

abbrev terminalDepth := Cut.finish bound.source input cut - 2

abbrev arrivalDepth := bound.source.history.length + cut

variable (rival : Opponent bound.source.code) (term : List (Option bound.source.code.Policy))
  (active : bound.source.feedback? = some input)

include active in
theorem prefix_current (ordinal : Nat) (inside : ordinal ≤ Cut.start bound.source cut) :
    (ProgrammeHistory.visitAt (candidate bound input cut rival term).source.input ordinal).current =
      (ProgrammeHistory.visitAt bound.source.input ordinal).current :=
  Machine.actual_prefix_from_events bound.source.input (candidate bound input cut rival term).source.input rfl rfl
    (Cut.start bound.source cut) (Future.prior_raw_event bound.source input cut rival term active) ordinal inside

include active in
theorem prefix_word (ordinal : Nat) (inside : ordinal < Cut.start bound.source cut) :
    ProgrammeSource.rawEvent (candidate bound input cut rival term).source.input
        (ProgrammeHistory.visitAt (candidate bound input cut rival term).source.input ordinal).current =
      ProgrammeSource.rawEvent bound.source.input (ProgrammeHistory.visitAt bound.source.input ordinal).current :=
  (congrArg (ProgrammeSource.rawEvent (candidate bound input cut rival term).source.input)
    (prefix_current bound input cut rival term active ordinal (by omega))).trans
      (Future.prior_raw_event bound.source input cut rival term active ordinal inside)

include active in
theorem prefix_items (ordinal : Nat) (inside : ordinal < Cut.start bound.source cut) :
    Registered.traceItems ((Native.Authority.programme bound).inputAt
        (Native.Authority.sourceIndex (candidate bound input cut rival term)))
        (ProgrammeHistory.visitAt (candidate bound input cut rival term).source.input ordinal).current =
      Registered.traceItems bound.source.input (ProgrammeHistory.visitAt bound.source.input ordinal).current := by
  exact congrArg₂ bound.source.code.law.rawItems
    (congrArg (ProgrammeSource.rawCurrent bound.source.input)
      (prefix_current bound input cut rival term active ordinal (by omega)))
    (prefix_word bound input cut rival term active ordinal inside)

include active in
theorem prefix_grant_current (depth : Nat) (inside : depth ≤ arrivalDepth bound cut) :
    Native.Authority.currentAt (candidate bound input cut rival term) depth = Native.Authority.currentAt bound depth := by
  exact congrArg (ProgrammeSource.rawCurrent bound.source.input)
    (prefix_current bound input cut rival term active (depth + 1) (by dsimp only [arrivalDepth, Cut.start] at *; omega))

include active in
theorem prefix_grant_word (depth : Nat) (inside : depth ≤ arrivalDepth bound cut) :
    Native.Authority.wordAt (candidate bound input cut rival term) depth = Native.Authority.wordAt bound depth :=
  prefix_word bound input cut rival term active (depth + 1) (by dsimp only [arrivalDepth, Cut.start] at *; omega)

end SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Normalization.RawAuthority
