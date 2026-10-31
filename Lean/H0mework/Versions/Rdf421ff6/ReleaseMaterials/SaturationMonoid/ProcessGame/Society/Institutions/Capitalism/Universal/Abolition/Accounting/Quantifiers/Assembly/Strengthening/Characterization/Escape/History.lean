import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Characterization.Escape.Rows

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Characterization.Escape

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion Source.Program
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root Abolition.Root.Registered Abolition.Root.Registered.Macro Evolution
noncomputable section
variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (source : Evolving.Epoch.Current (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))

def claimAlong : (n : Nat) → source.native.frame.N.Claim → (Evolving.Epoch.History.currentAt source n).native.frame.N.Claim
  | 0 => id
  | n+1 => fun claim => nextClaim (Evolving.Epoch.History.currentAt source n) (claimAlong n claim)

def rowAlong (original : OpenResponsibilityAt source.native.frame.N
    (source.native.frame.sourceSupport source.native.visit.current)) :
    (n : Nat) → OpenResponsibilityAt (Evolving.Epoch.History.currentAt source n).native.frame.N
      ((Evolving.Epoch.History.currentAt source n).native.frame.sourceSupport
        (Evolving.Epoch.History.currentAt source n).native.visit.current)
  | 0 => original
  | n+1 => nextRow (Evolving.Epoch.History.currentAt source n) (rowAlong original n)

theorem all_actual_detours_keep_original_claims_distinct (n : Nat) : Function.Injective (claimAlong source n) := by
  induction n with
  | zero => exact fun _ _ same => same
  | succ n previous => exact (nextClaim_does_not_merge_original_claims _).comp previous

theorem every_actual_detour_carries_the_exact_original_claim
    (original : OpenResponsibilityAt source.native.frame.N
      (source.native.frame.sourceSupport source.native.visit.current)) (n : Nat) :
    (rowAlong source original n).claim = claimAlong source n original.claim := by
  induction n with
  | zero => rfl
  | succ n previous =>
      exact (nextRow_keeps_the_same_source_claim _ _).trans
        (congrArg (nextClaim (Evolving.Epoch.History.currentAt source n)) previous)

theorem no_actual_detour_refills_an_original_responsibility
    (original : OpenResponsibilityAt source.native.frame.N
      (source.native.frame.sourceSupport source.native.visit.current)) (n : Nat) :
    (rowAlong source original n).progressBudget ≤ original.progressBudget := by
  induction n with
  | zero => exact le_rfl
  | succ n previous => exact (nextRow_never_refills_an_original_residual _ _).trans previous

theorem every_paid_original_stays_paid_through_all_actual_detours
    (original : OpenResponsibilityAt source.native.frame.N
      (source.native.frame.sourceSupport source.native.visit.current))
    (paid : original.progressBudget = 0) (n : Nat) : (rowAlong source original n).progressBudget = 0 :=
  Nat.eq_zero_of_le_zero (paid ▸ no_actual_detour_refills_an_original_responsibility source original n)

theorem all_actual_detours_are_the_original_answer_and_whole_ledger (n : Nat) :
    Evolving.Epoch.Current.ClosedAt (Evolving.Epoch.History.currentAt source n) :=
  Evolving.Epoch.History.every_actual_epoch_reads_its_live_control_and_closes_its_whole_ledger source n

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Characterization.Escape
