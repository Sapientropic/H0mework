import H0mework.Physics.SourceFamily.Acceptance

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherFamilyOccurrence

open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open Stage9C.Revision StageNineEnrichedProofFreeSource SourceFamily

noncomputable section

abbrev MotherRoot := SpinPair.livingRoot.toAuthoritativeRoot.toLedgerRoot
abbrev MotherVisit := SourceNativeTemporalVisitAt MotherRoot

private theorem no_postCofinal {current : SpinPair.V.Current} :
    SourceNativePostCofinalReachableAt MotherRoot current → False
  | .cofinal visit => nomatch visit.event
  | .step prior _ => no_postCofinal prior

/-- A lossless finite view of the original discrete mother's actual history. -/
def finiteHistory {current : SpinPair.V.Current} :
    SourceNativeTemporalReachableAt MotherRoot current → MotherRoot.toRoot.ReachableAt current
  | .finite history => history
  | .postCofinal history => False.elim (no_postCofinal history)

def finiteVisit (visit : MotherVisit) : RootVisit MotherRoot.toRoot :=
  ⟨visit.current, finiteHistory visit.history⟩

theorem finite_readback (visit : MotherVisit) :
    SourceNativeTemporalVisitAt.finite (finiteVisit visit) = visit := by
  rcases visit with ⟨current, history⟩
  cases history with
  | finite history => rfl
  | postCofinal history => exact False.elim (no_postCofinal history)

theorem finite_next (visit : MotherVisit) :
    finiteVisit (visit.next rfl) = (finiteVisit visit).next rfl := by
  rcases visit with ⟨current, history⟩
  cases history with
  | finite history => rfl
  | postCofinal history => exact False.elim (no_postCofinal history)

theorem finite_depth (visit : MotherVisit) :
    ProductiveFiniteRootHistoryAt.causalDepth (finiteVisit visit).history =
      temporalDepth visit.history := by
  rcases visit with ⟨current, history⟩
  cases history with
  | finite history => rfl
  | postCofinal history => exact False.elim (no_postCofinal history)

def originDepth : ℕ := ProductiveFiniteRootHistoryAt.causalDepth (finiteVisit Runtime.visit).history

/-- This fold consumes the actual predecessor and native successor edge.
The existing Stage-10 origin fixes the prefix; each later event applies the
already generated source-material operation. No future field enters the seed. -/
def sourceFold {current : SpinPair.V.Current} :
    MotherRoot.toRoot.ReachableAt current → SmoothUnifiedSource
  | .initial => Runtime.source
  | .step prior _ =>
      if ProductiveFiniteRootHistoryAt.causalDepth prior < originDepth then sourceFold prior
      else advanceSource (sourceFold prior)

theorem sourceFold_normal {current : SpinPair.V.Current}
    (history : MotherRoot.toRoot.ReachableAt current) :
    sourceFold history = sourceAt (ProductiveFiniteRootHistoryAt.causalDepth history - originDepth) := by
  induction history with
  | initial =>
      simp only [sourceFold, ProductiveFiniteRootHistoryAt.causalDepth, Nat.zero_sub, sourceAt]
      rfl
  | @step current target prior transition induction =>
      simp only [sourceFold, ProductiveFiniteRootHistoryAt.causalDepth]
      split_ifs with before
      · rw [induction]
        congr 1
        omega
      · rw [induction]
        rw [show ProductiveFiniteRootHistoryAt.causalDepth prior + 1 - originDepth =
          (ProductiveFiniteRootHistoryAt.causalDepth prior - originDepth) + 1 by omega]
        rfl

def formedSource (visit : MotherVisit) : SmoothUnifiedSource := sourceFold (finiteVisit visit).history

theorem formed_normal (visit : MotherVisit) :
    formedSource visit = sourceAt (temporalDepth visit.history - originDepth) := by
  exact (sourceFold_normal (finiteVisit visit).history).trans
    (congrArg (fun depth => sourceAt (depth - originDepth)) (finite_depth visit))

theorem formed_next (visit : MotherVisit) (afterOrigin : originDepth ≤ temporalDepth visit.history) :
    formedSource (visit.next rfl) = advanceSource (formedSource visit) := by
  unfold formedSource
  rw [finite_next]
  change (if ProductiveFiniteRootHistoryAt.causalDepth (finiteVisit visit).history < originDepth
    then sourceFold (finiteVisit visit).history else advanceSource (sourceFold (finiteVisit visit).history)) = _
  rw [finite_depth, if_neg (not_lt_of_ge afterOrigin)]

theorem visit_depth (step : ℕ) : temporalDepth (SpinPair.visit step).history = step := by
  induction step with
  | zero => rfl
  | succ step induction =>
      exact (temporalDepth_next (SpinPair.visit step).history _).trans (congrArg (· + 1) induction)

theorem origin_depth : originDepth = 10 := by
  rw [originDepth, finite_depth]
  exact visit_depth 10

theorem formed_at (step : ℕ) : formedSource (SpinPair.visit (10 + step)) = sourceAt step := by
  rw [formed_normal, visit_depth, origin_depth]
  congr 1
  omega

theorem origin_source : formedSource Runtime.visit = Runtime.source := formed_at 0

theorem seed_next (visit : MotherVisit) (afterOrigin : originDepth ≤ temporalDepth visit.history) :
    (formedSource (visit.next rfl)).stageEight.sigmaSeed =
      (formedSource visit).stageEight.sigmaSeed + 1 := by
  rw [formed_next visit afterOrigin]
  rfl

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherFamilyOccurrence
