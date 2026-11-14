import H0mework.Versions.Red5c4028.ReleaseMaterials.SaturationMonoid.GenericFoundation.Scalar.Feature.FiniteGram.Projection.DualColumn
import H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Observed.Operator.Impulse
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.OutsideFeedbackHistory

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKFiniteOrderRelease.PositionGapCayley.OutsideLogRank.SelfOrbit.FeedbackHistory

open BurnolPhysicalState Finset
open OriginalKCrossParameterRAdjointSource.PhysicalOutsideSource
open scoped BigOperators InnerProductSpace

open private state_convolution from H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Observed.Operator.Impulse
open private full_outside_write coefficients_exact from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.OutsideFeedbackHistory

local notation "R" => burnolDirectRightResolventCLM
local notation "O" => OriginalKCombPhysicalAction.physicalRemainder
local notation "V" => physicalOutsideColumn
local notation "K" => burnolCompletedMellinRieszVector
local notation "price" => fun (c : BurnolCompletedMellinCoordinate) (value : BurnolL2) =>
  inner ℂ (fourierL2 (K c : BurnolL2)) value

/-- The actual outside recurrence carries each payment in the original self-action column. -/
theorem physical_source_outside_history (c : BurnolCompletedMellinCoordinate)
    (source : BurnolPaAmbientCarrier) (n : Nat) :
    O (((R c)^(n+1)) (source : BurnolL2)) =
      ∑ j ∈ range (n+1), (-2*price c (((R c)^(n-j)) (source : BurnolL2))) • column c j := by
  let action : Module.End ℂ BurnolL2 := (selfAction c).toLinearMap
  let field (j : Nat) := O (((R c)^j) (source : BurnolL2))
  let amount (j : Nat) := -2*price c (((R c)^j) (source : BurnolL2))
  have initial : field 0 = 0 := by
    dsimp only [field]
    rw [pow_zero,one_apply_eq_self]
    exact Submodule.starProjection_orthogonal_apply_eq_zero source.property
  have written (j : Nat) : field (j+1) = action (field j) + amount j • V c := by
    dsimp only [field,amount]
    rw [pow_succ',mul_apply_eq_comp]
    exact full_outside_write c (((R c)^j) (source : BurnolL2))
  have columns (j : Nat) : (action^j) (V c) = column c j := by
    induction j with
    | zero => simp only [pow_zero,Module.End.one_apply,column,one_apply_eq_self]
    | succ j previous =>
      rw [pow_succ',Module.End.mul_apply,previous]
      change selfAction c (column c j) = column c (j+1)
      change selfAction c (((selfAction c)^j) (V c)) = ((selfAction c)^(j+1)) (V c)
      rw [pow_succ',mul_apply_eq_comp]
  have whole := state_convolution action (V c) initial written n
  change field (n+1) = ∑ j ∈ range (n+1), amount (n-j) • column c j
  rw [whole]
  simp only [columns]
  conv_lhs => rw [← Finset.sum_range_reflect (fun j => amount j • column c (n-j)) (n+1)]
  simp only [Nat.add_sub_cancel]
  apply Finset.sum_congr rfl
  intro j live
  rw [Nat.sub_sub_self (by have h := Finset.mem_range.mp live; omega)]

/-- The same exterior field determines every chronological input price. -/
theorem physical_source_decoded_history (c : BurnolCompletedMellinCoordinate) (source : BurnolPaAmbientCarrier)
    (n : Nat) (lag : Fin (n+1)) :
    decodedLag c n (O (((R c)^(n+1)) (source : BurnolL2))) lag =
      price c (((R c)^(n-lag.val)) (source : BurnolL2)) := by
  let a : Gram.Coordinates (Fin (n+1)) :=
    WithLp.toLp 2 fun i => -2*price c (((R c)^(n-i.val)) (source : BurnolL2))
  have word : O (((R c)^(n+1)) (source : BurnolL2)) =
      Gram.synthesis (fun j : Fin (n+1) => column c j.val) a := by
    change O (((R c)^(n+1)) (source : BurnolL2)) =
      ∑ j : Fin (n+1), (-2*price c (((R c)^(n-j.val)) (source : BurnolL2))) • column c j.val
    exact (physical_source_outside_history c source n).trans
      (Fin.sum_univ_eq_sum_range (fun j : Nat => (-2*price c (((R c)^(n-j)) (source : BurnolL2))) • column c j) (n+1)).symm
  unfold decodedLag
  rw [word,coefficients_exact]
  change -(-2*price c (((R c)^(n-lag.val)) (source : BurnolL2)))/2 = _
  ring

/-- The same original outside columns generate a fixed cotest for each lag. -/
def outsideLagCotest (c : BurnolCompletedMellinCoordinate) (n : Nat) (lag : Fin (n+1)) : BurnolL2 :=
  SourceGeneratedFiniteGram.Projection.dualColumn (fun j : Fin (n+1) => column c j.val)
    ((column_linearIndependent c).comp (Fin.val : Fin (n+1) → Nat) Fin.val_injective) lag

theorem decoded_lag_eq_cotest (c : BurnolCompletedMellinCoordinate) (n : Nat) (lag : Fin (n+1))
    (field : BurnolL2) :
    decodedLag c n field lag = -inner ℂ (outsideLagCotest c n lag) field / 2 := by
  rw [outsideLagCotest,SourceGeneratedFiniteGram.Projection.inner_dualColumn_eq_coefficients]
  rfl

end OriginalKFiniteOrderRelease.PositionGapCayley.OutsideLogRank.SelfOrbit.FeedbackHistory
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
