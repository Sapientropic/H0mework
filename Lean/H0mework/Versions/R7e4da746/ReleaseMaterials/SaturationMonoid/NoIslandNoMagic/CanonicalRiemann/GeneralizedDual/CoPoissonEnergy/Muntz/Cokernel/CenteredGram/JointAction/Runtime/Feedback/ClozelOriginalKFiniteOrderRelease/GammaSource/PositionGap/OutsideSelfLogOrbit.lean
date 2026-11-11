import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.OutsideLogRank

set_option autoImplicit false
noncomputable section

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKFiniteOrderRelease.PositionGapCayley.OutsideLogRank.SelfOrbit

open BurnolPhysicalState Finset
open OriginalKCrossParameterRAdjointSource.PhysicalOutsideSource
open OriginalKDirectRCofinalOutsideVolterraSource
open OriginalKFiniteOrderRelease.OutsideQuarterAction
open UnitPowerJordanSource UnitPowerJordanAction GenericSourceStepBAction
open scoped BigOperators InnerProductSpace

open private fourier_R from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.PairedCayleyAction
open private position_read fourier_read position_gap_zero actual_position_step source_even from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GenericSourceStepBAction
open private embedding_even embedding_fourier from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.OutsideQuarterAction
open private actual_R_reflect from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.CofinalCanonicalSourceMaterial
open private log_inventory_succ from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.OutsideLogWrite

local notation "R" => burnolDirectRightResolventCLM
local notation "O" => OriginalKCombPhysicalAction.physicalRemainder
local notation "barC" => OriginalPrimitiveRankBalance.conjugateCoordinate
local notation "V" => physicalOutsideColumn
local notation "F" => fourierL2
local notation "Z" => OriginalRieszSource.Constructor.zeroMean
local notation "Rq" => burnolQuarterRestriction
local notation "M" => BurnolQuarterMeanZeroCarrier

/-- The original outside block with only its own current field as input. -/
def selfAction (c : BurnolCompletedMellinCoordinate) : BurnolL2 →L[ℂ] BurnolL2 :=
  (O).comp (R c)

def column (c : BurnolCompletedMellinCoordinate) (n : Nat) : BurnolL2 :=
  ((selfAction c)^n) (V c)

private def centerRead : BurnolL2 →ₗ[ℂ] M :=
  ((Z).comp ((Rq).comp fourierL2.toContinuousLinearEquiv.toContinuousLinearMap)).toLinearMap

private theorem center_physical (x : BurnolPaAmbientCarrier) : centerRead (x:BurnolL2) = 0 := by
  have inside := fourierL2_mem_evenBurnolClosedFace x.property
  have even := mem_evenL2ClosedFace_iff.mp inside.2
  have gap : F (x:BurnolL2) ∈ locallyConstantFace (1/4:ℝ) := inside.1.1
  have paid := position_gap_zero _ even gap
  rw [position_read _ even] at paid
  exact paid

private theorem center_outside (x : BurnolL2) : centerRead (O x) = centerRead x := by
  rw [show O x = x - (burnolEvenAmbientProjection x:BurnolL2) from Submodule.starProjection_orthogonal_val x,
    map_sub, center_physical, sub_zero]

private theorem outside_even (x : BurnolL2) (even : reflectL2 x=x) : reflectL2 (O x)=O x := by
  have physical := mem_evenL2ClosedFace_iff.mp (burnolEvenAmbientProjection x).property.2
  rw [show O x = x - (burnolEvenAmbientProjection x:BurnolL2) from Submodule.starProjection_orthogonal_val x,
    map_sub, even, physical]

private theorem V_even (c : BurnolCompletedMellinCoordinate) : reflectL2 (V c)=V c := by
  rw [physicalOutsideColumn_embedding]
  exact embedding_even _ (log_B_even (barC c) 0)

private theorem V_center (c : BurnolCompletedMellinCoordinate) :
    centerRead (V c) = centeredLogColumn (barC c) 0 := by
  let h := hPowerBColumn (barC c)
  have even : sourceMeanZeroReflection h=h := log_B_even (barC c) 0
  have read := embedding_fourier h even
  rw [fourier_read _ (embedding_even h even)] at read
  change centerRead (outsideEmbedding h) = h - burnolMeanZeroTruncatedFourier (burnolMeanZeroTruncatedFourier h) at read
  rw [physicalOutsideColumn_embedding, read]
  change burnolMeanZeroOneMinusSquare (burnolMeanZeroBlockInverse (centeredLogColumn (barC c) 0)) = _
  exact congrArg (fun map : M →L[ℂ] M => map (centeredLogColumn (barC c) 0))
    burnolMeanZeroBlockInverse_right

private theorem column_even (c : BurnolCompletedMellinCoordinate) (n : Nat) :
    reflectL2 (column c n) = column c n := by
  induction n with
  | zero => simpa only [column, pow_zero, one_apply_eq_self] using V_even c
  | succ n prior =>
    have step : column c (n+1) = selfAction c (column c n) := by
      simp only [column, pow_succ', mul_apply_eq_comp]
    rw [step]
    change reflectL2 (O (R c (column c n))) = O (R c (column c n))
    apply outside_even
    change reflectL2 (burnolDirectRightResolvent (c.value/2) (column c n)) =
      burnolDirectRightResolvent (c.value/2) (column c n)
    rw [actual_R_reflect, prior]

private theorem center_step (c : BurnolCompletedMellinCoordinate) (x : BurnolL2)
    (even : reflectL2 x=x) :
    centerRead (selfAction c x) =
      centeredQuarterStep (barC c) (centerRead x) +
        currentAmplitude (barC c) (F x) • centeredLogColumn (barC c) 0 := by
  have FourierEven : reflectL2 (F x)=F x := by rw [← fourierL2_reflectL2_commute, even]
  have paid := actual_position_step (barC c) (F x) FourierEven
  rw [position_read _ (source_even (barC c) _ FourierEven), position_read _ FourierEven] at paid
  change centerRead (O (R c x)) = _
  rw [center_outside]
  change Z (Rq (F (R c x))) = _
  rw [fourier_R]
  exact paid

private def stock (c : BurnolCompletedMellinCoordinate) : Nat → LogStock :=
  Nat.rec (Finsupp.single 0 1) fun n old =>
    logInventoryStep (barC c) old +
      Finsupp.single 0 (currentAmplitude (barC c) (F (column c n)))

private theorem stock_succ (c : BurnolCompletedMellinCoordinate) (n : Nat) :
    stock c (n+1) = logInventoryStep (barC c) (stock c n) +
      Finsupp.single 0 (currentAmplitude (barC c) (F (column c n))) := rfl

private theorem column_center (c : BurnolCompletedMellinCoordinate) (n : Nat) :
    centerRead (column c n) = logSynthesis (barC c) (stock c n) := by
  induction n with
  | zero =>
    simp only [column, pow_zero, one_apply_eq_self, V_center]
    change _ = Finsupp.linearCombination ℂ (centeredLogColumn (barC c)) (Finsupp.single 0 (1:ℂ))
    rw [Finsupp.linearCombination_single, one_smul]
  | succ n prior =>
    rw [stock_succ, map_add, log_inventory_synthesis]
    change centerRead (((selfAction c)^(n+1)) (V c)) = _
    rw [pow_succ', mul_apply_eq_comp]
    change centerRead (selfAction c (column c n)) = _
    rw [center_step c _ (column_even c n), prior]
    change _ = _ + Finsupp.linearCombination ℂ (centeredLogColumn (barC c))
      (Finsupp.single 0 (currentAmplitude (barC c) (F (column c n))))
    rw [Finsupp.linearCombination_single]

private theorem stock_top (c : BurnolCompletedMellinCoordinate) (n : Nat) :
    stock c n n = (-2:ℂ)^n := by
  induction n with
  | zero => simp [stock]
  | succ n prior =>
    rw [stock_succ, Finsupp.add_apply, log_inventory_succ,
      Finsupp.single_eq_of_ne (Nat.succ_ne_zero n), add_zero, prior, pow_succ']

private theorem stock_above (c : BurnolCompletedMellinCoordinate) (n j : Nat) (higher : n < j) :
    stock c n j = 0 := by
  induction n generalizing j with
  | zero =>
    change Finsupp.single 0 (1:ℂ) j = 0
    exact Finsupp.single_eq_of_ne (Nat.ne_of_gt higher)
  | succ n prior =>
    cases j with
    | zero => omega
    | succ j =>
      rw [stock_succ, Finsupp.add_apply, log_inventory_succ,
        Finsupp.single_eq_of_ne (Nat.succ_ne_zero j), add_zero, prior j (by omega), mul_zero]

/-- Each genuine outside self-action appends a fresh log degree to the original source column. -/
theorem column_linearIndependent (c : BurnolCompletedMellinCoordinate) :
    LinearIndependent ℂ (column c) := by
  classical
  rw [linearIndependent_iff']
  intro indices a erased i included
  by_contra nonzero
  have synth : Function.Injective (logSynthesis (barC c)) :=
    linearIndependent_iff_injective_finsuppLinearCombination.mp (centered_log_columns_linearIndependent (barC c))
  have zero : ∑ j ∈ indices, a j • stock c j = 0 := by
    apply synth
    simpa only [map_sum, map_smul, map_zero, ← column_center c] using congrArg centerRead erased
  let active := indices.filter (fun j => a j ≠ 0)
  have inhabited : active.Nonempty := ⟨i, Finset.mem_filter.mpr ⟨included, nonzero⟩⟩
  let k := active.max' inhabited
  have live := Finset.mem_filter.mp (Finset.max'_mem active inhabited)
  let read : LogStock →ₗ[ℂ] ℂ := Finsupp.lapply k
  have scalar : ∑ j ∈ indices, a j * stock c j k = 0 := by
    simpa only [read, map_sum, map_smul, map_zero, Finsupp.lapply_apply, smul_eq_mul]
      using congrArg read zero
  have select : ∑ j ∈ indices, a j * stock c j k = a k * stock c k k := by
    apply Finset.sum_eq_single k
    · intro j hj other
      rcases lt_or_gt_of_ne other with earlier | later
      · rw [stock_above c j k earlier, mul_zero]
      · have gone : a j = 0 := by
          by_contra has
          exact (not_le_of_gt later) (Finset.le_max' active j (Finset.mem_filter.mpr ⟨hj, has⟩))
        rw [gone, zero_mul]
    · exact fun absent => (absent live.1).elim
  rw [select, stock_top] at scalar
  exact mul_ne_zero live.2 (pow_ne_zero _ (by norm_num)) scalar

end OriginalKFiniteOrderRelease.PositionGapCayley.OutsideLogRank.SelfOrbit
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
