import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Evolving.Native.Whole

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Evolving.History

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion Source.Program
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root Abolition.Root.Registered Abolition.Root.Registered.Macro Evolution

noncomputable section
variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (source : NativeCurrent (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))


/-- Finite observations of the source's recursive query chain. The network,
source vocabulary and living root may change at every actual native birth. -/
def currentAt : Nat → NativeCurrent (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)
  | 0 => source
  | n + 1 => (currentAt n).advance

def claimAt : (n : Nat) → source.frame.N.Claim → (currentAt source n).frame.N.Claim
  | 0 => id
  | n + 1 => fun claim => (currentAt source n).advanceClaim (claimAt n claim)

def rowAt (row : OpenResponsibilityAt source.frame.N (source.frame.sourceSupport source.visit.current)) :
    (n : Nat) → OpenResponsibilityAt (currentAt source n).frame.N
      ((currentAt source n).frame.sourceSupport (currentAt source n).visit.current)
  | 0 => row
  | n + 1 => (currentAt source n).advanceRow (rowAt row n)

theorem every_step_is_the_actual_root_query (n : Nat) :
    type_of% (NativeCurrent.advance_is_the_actual_source_successor (currentAt source n)) :=
  NativeCurrent.advance_is_the_actual_source_successor _

theorem every_actual_claim_map_is_injective (n : Nat) : Function.Injective (claimAt source n) := by
  induction n with
  | zero => exact fun _ _ same => same
  | succ n ih => exact (NativeCurrent.advanceClaim_does_not_merge_original_claims _).comp ih

theorem every_original_row_keeps_its_claim
    (row : OpenResponsibilityAt source.frame.N (source.frame.sourceSupport source.visit.current)) (n : Nat) :
    (rowAt source row n).claim = claimAt source n row.claim := by
  induction n with
  | zero => rfl
  | succ n ih =>
    exact (NativeCurrent.advanceRow_keeps_the_original_claim _ _).trans
      (congrArg (NativeCurrent.advanceClaim (currentAt source n)) ih)

theorem no_original_responsibility_can_be_refilled
    (row : OpenResponsibilityAt source.frame.N (source.frame.sourceSupport source.visit.current)) (n : Nat) :
    (rowAt source row n).progressBudget ≤ row.progressBudget := by
  induction n with
  | zero => exact le_rfl
  | succ n ih => exact (NativeCurrent.advanceRow_never_refills_an_old_responsibility _ _).trans ih

theorem every_original_paid_responsibility_remains_paid
    (row : OpenResponsibilityAt source.frame.N (source.frame.sourceSupport source.visit.current))
    (paid : row.progressBudget = 0) (n : Nat) : (rowAt source row n).progressBudget = 0 :=
  Nat.eq_zero_of_le_zero (paid ▸ no_original_responsibility_can_be_refilled source row n)

theorem the_productive_row_is_the_carried_original (n : Nat) :
    rowAt source source.rows.productive n = (currentAt source n).rows.productive := by
  induction n with
  | zero => rfl
  | succ n ih =>
      exact (congrArg (NativeCurrent.advanceRow (currentAt source n)) ih).trans
        (NativeCurrent.advanceRow_is_the_same_productive_history _)

theorem the_gross_row_is_the_carried_original (n : Nat) :
    rowAt source source.rows.gross n = (currentAt source n).rows.gross := by
  induction n with
  | zero => rfl
  | succ n ih =>
      exact (congrArg (NativeCurrent.advanceRow (currentAt source n)) ih).trans
        (NativeCurrent.advanceRow_is_the_same_gross_history _)

theorem each_actual_handler_excludes_every_capital_relation (n : Nat) :
    Global.NoCapital (currentAt source n).handlerLaw :=
  NativeCurrent.the_actual_public_handler_excludes_every_capital_relation _

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Evolving.History
