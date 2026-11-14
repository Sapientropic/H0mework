import H0mework.Versions.Red5c4028.ReleaseMaterials.SaturationMonoid.GenericFoundation.Scalar.Feature.FiniteGram.Projection.DualColumn.Insert
import H0mework.Versions.Red5c4028.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.OutsideFeedbackHistory.PhysicalSource

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKFiniteOrderRelease.PositionGapCayley.OutsideLogRank.SelfOrbit.FeedbackHistory

open BurnolPhysicalState SourceGeneratedFiniteGram.Projection
open scoped InnerProductSpace

private abbrev lagColumns (c : BurnolCompletedMellinCoordinate) (n : Nat) : Fin (n+1) → BurnolL2 :=
  fun j => column c j.val

private theorem outside_columns_snoc (c : BurnolCompletedMellinCoordinate) (n : Nat) :
    Fin.snoc (lagColumns c n) (column c (n+1)) = lagColumns c (n+1) := by
  funext j
  refine Fin.lastCases ?_ (fun i => ?_) j
  · rw [Fin.snoc_last]
    change column c (n+1) = column c (Fin.last (n+1)).val
    rw [Fin.val_last]
  · rw [Fin.snoc_castSucc]
    change column c i.val = column c i.castSucc.val
    rw [Fin.val_castSucc]

private theorem actual_columns_independent (c : BurnolCompletedMellinCoordinate) (n : Nat) :
    LinearIndependent ℂ (lagColumns c n) :=
  (column_linearIndependent c).comp (Fin.val : Fin (n+1) → Nat) Fin.val_injective

private theorem appended_columns_independent (c : BurnolCompletedMellinCoordinate) (n : Nat) :
    LinearIndependent ℂ (Fin.snoc (lagColumns c n) (column c (n+1))) := by
  rw [outside_columns_snoc]
  exact actual_columns_independent c (n+1)

theorem original_outside_innovation_ne_zero (c : BurnolCompletedMellinCoordinate) (n : Nat) :
    innovationCLM (lagColumns c n) (column c (n+1)) ≠ 0 :=
  snoc_innovation_ne_zero _ _ (appended_columns_independent c n)

private theorem dualColumn_congr {n : Nat} {left right : Fin n → BurnolL2} (same : left = right)
    (leftIndependent : LinearIndependent ℂ left) (rightIndependent : LinearIndependent ℂ right) (i : Fin n) :
    dualColumn left leftIndependent i = dualColumn right rightIndependent i := by
  subst right
  rfl

private theorem outside_cotest_append (c : BurnolCompletedMellinCoordinate) (n : Nat) (j : Fin (n+2)) :
    outsideLagCotest c (n+1) j =
      dualColumn (Fin.snoc (lagColumns c n) (column c (n+1))) (appended_columns_independent c n) j :=
  (dualColumn_congr (outside_columns_snoc c n) _ (actual_columns_independent c (n+1)) j).symm

/-- The new original outside column supplies the next oldest cotest by its innovation alone. -/
theorem original_outside_last_cotest (c : BurnolCompletedMellinCoordinate) (n : Nat) :
    outsideLagCotest c (n+1) (Fin.last (n+1)) =
      insertedDualColumn (lagColumns c n) (column c (n+1)) :=
  (outside_cotest_append c n _).trans (dualColumn_snoc_last _ _ (appended_columns_independent c n))

/-- Each existing original cotest makes exactly the one new-column correction. -/
theorem original_outside_prior_cotest (c : BurnolCompletedMellinCoordinate) (n : Nat) (lag : Fin (n+1)) :
    outsideLagCotest c (n+1) lag.castSucc =
      outsideLagCotest c n lag-star (inner ℂ (outsideLagCotest c n lag) (column c (n+1))) •
        insertedDualColumn (lagColumns c n) (column c (n+1)) :=
  (outside_cotest_append c n _).trans (dualColumn_snoc_castSucc _ _ (appended_columns_independent c n) lag)

/-- One new innovation and the original old outside solver read all lags of the extended field. -/
theorem original_outside_lag_insertion (c : BurnolCompletedMellinCoordinate) (n : Nat) (field : BurnolL2) :
    let charge := insertedCoefficient (lagColumns c n) (column c (n+1)) field
    decodedLag c (n+1) field (Fin.last (n+1)) = -charge/2 ∧
      ∀ lag : Fin (n+1),
        decodedLag c (n+1) field lag.castSucc = decodedLag c n (field-charge • column c (n+1)) lag := by
  have read := coefficients_snoc_read (lagColumns c n) (column c (n+1)) (appended_columns_independent c n) field
  dsimp only at read ⊢
  rw [outside_columns_snoc] at read
  constructor
  · unfold decodedLag
    rw [read.1]
  · intro lag
    unfold decodedLag
    rw [read.2 lag]

end OriginalKFiniteOrderRelease.PositionGapCayley.OutsideLogRank.SelfOrbit.FeedbackHistory
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
