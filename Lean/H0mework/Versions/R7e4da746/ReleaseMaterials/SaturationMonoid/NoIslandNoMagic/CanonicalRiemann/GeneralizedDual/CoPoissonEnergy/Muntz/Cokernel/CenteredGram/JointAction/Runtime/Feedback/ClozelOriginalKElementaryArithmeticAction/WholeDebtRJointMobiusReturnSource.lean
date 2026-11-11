import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.WholeDebtRJointMobiusReturnRealization

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1400000
noncomputable section

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalWholeDebtRJointMobiusReturnSource
open Complex MeasureTheory Set Filter FourierTransform BurnolPhysicalState OriginalRieszSource
open scoped Topology InnerProductSpace BigOperators ContDiff ArithmeticFunction
open private actual_fourier_next action_even from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.WholeDebtRJointMobiusTateRSource
open private fourier_c1 inverse_bounds positive_c1 from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.WholeDebtRJointMobiusAnnulusSource
open private coordinate_eq forward_zero_window from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.WholeDebtRJointMobiusUnitSource
open private forward_cut from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.WholeDebtRJointMobiusProgrammeSource
open private adjoint_volterra adjoint_evenPart adjoint_fourier_eq_inverse from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCrossParameterRAdjointSource.PhysicalDefectSource
open private conjugateCoordinate_twice from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKDirectRCofinalOutsideVolterraSource.PaAdjointSource
local notation "q" => (1 / 4 : ℝ)
local notation "Hq" => BurnolQuarterIntervalL2
local notation "P" => burnolEvenAmbientProjection
variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
variable (half : OriginalKCombCalculation.Half observation)
local notation "coord" => OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half
local notation "w" => T.updatedWave observation nontrivial half

open private outside_gap from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.WholeDebtRJointMobiusReturnRealization
/-- The actual contact and compact-source mean price the same original whole unit. -/
def unitCoefficient : ℂ := (contact observation nontrivial half + sourceMean observation nontrivial half) /
  OriginalWholeDebtRJointMobiusUnitSource.unitGap coord

def normalizedSourceRaw (x : ℝ) : ℂ := outsideSourceRaw observation nontrivial half x -
  unitCoefficient observation nontrivial half * OriginalWholeDebtRJointMobiusUnitSource.unitRaw coord x

def normalizedResponseRaw : ℝ → ℂ := burnolInnerGapForward (normalizedSourceRaw observation nontrivial half)

private theorem unit_balance : unitCoefficient observation nontrivial half *
    OriginalWholeDebtRJointMobiusUnitSource.unitGap coord = contact observation nontrivial half + sourceMean observation nontrivial half := by
  have nonzero : (coord).value ≠ 0 := by
    intro zero
    have right := (coord).rightHalf
    rw [zero] at right
    norm_num at right
  have gap : OriginalWholeDebtRJointMobiusUnitSource.unitGap coord ≠ 0 := by
    unfold OriginalWholeDebtRJointMobiusUnitSource.unitGap
    exact div_ne_zero (Complex.cpow_ne_zero_iff.mpr (Or.inl (by norm_num))) nonzero
  exact div_mul_cancel₀ _ gap

theorem actual_normalized_source_gap {x : ℝ} (inside : |x| ≤ (4 : ℝ)) :
    normalizedSourceRaw observation nontrivial half x = 0 := by
  have outside : outsideSourceRaw observation nontrivial half x = 0 :=
    indicator_of_notMem (not_not.mpr (show x ∈ symmetricInterval (4 : ℝ) from abs_le.mp inside)) _
  rw [normalizedSourceRaw, outside]
  simp only [OriginalWholeDebtRJointMobiusUnitSource.unitRaw, burnolRadiusUnitTailRaw,
    if_neg (not_lt.mpr inside), mul_zero, sub_zero]

private theorem normalized_forward (x : ℝ) : normalizedResponseRaw observation nontrivial half x =
    burnolInnerGapForward (outsideSourceRaw observation nontrivial half) x -
      unitCoefficient observation nontrivial half * burnolInnerGapForward
        (OriginalWholeDebtRJointMobiusUnitSource.unitRaw coord) x := by
  have unitGap : ∀ {x : ℝ}, |x| ≤ q → OriginalWholeDebtRJointMobiusUnitSource.unitRaw coord x = 0 := by
    intro x inside
    exact if_neg (not_lt.mpr (by linarith))
  have gap : ∀ {x : ℝ}, |x| ≤ q → normalizedSourceRaw observation nontrivial half x = 0 :=
    fun inside => actual_normalized_source_gap observation nontrivial half (by linarith)
  rw [normalizedResponseRaw, forward_cut _ gap, forward_cut _ (outside_gap observation nontrivial half),
    forward_cut _ unitGap, Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro n _
  unfold normalizedSourceRaw
  ring

private theorem normalized_read :
    ((response observation nontrivial half - unitCoefficient observation nontrivial half • burnolUnitTailResponse coord 4 : BurnolL2) : ℝ → ℂ)
      =ᵐ[volume] normalizedResponseRaw observation nontrivial half := by
  have unitRead : (burnolUnitTailResponse coord 4 : ℝ → ℂ) =ᵐ[volume]
      fun x => burnolInnerGapForward (OriginalWholeDebtRJointMobiusUnitSource.unitRaw coord) x +
        OriginalWholeDebtRJointMobiusUnitSource.unitGap coord := by
    filter_upwards [burnolUnitTailResponse_coeFn coord 4 (by norm_num) (by norm_num)] with x actual
    rw [actual]
    unfold OriginalWholeDebtRJointMobiusUnitSource.unitRaw OriginalWholeDebtRJointMobiusUnitSource.unitGap burnolUnitTailDirichletRaw
    rw [burnolRadiusUnitTail_finiteCoSum (coord).value 4 x (by norm_num)]
    simp only [Complex.ofReal_ofNat]
    ring
  filter_upwards [Lp.coeFn_sub (response observation nontrivial half)
      (unitCoefficient observation nontrivial half • burnolUnitTailResponse coord 4),
    Lp.coeFn_smul (unitCoefficient observation nontrivial half) (burnolUnitTailResponse coord 4),
    actual_response_raw observation nontrivial half, unitRead] with x difference scalar outside unit
  rw [difference]
  change response observation nontrivial half x -
    (unitCoefficient observation nontrivial half • burnolUnitTailResponse coord 4 : BurnolL2) x = _
  rw [scalar]
  change response observation nontrivial half x - unitCoefficient observation nontrivial half * burnolUnitTailResponse coord 4 x = _
  rw [outside, unit, normalized_forward]
  unfold responseRaw
  rw [mul_add, unit_balance]
  ring

private theorem normalized_native : MemLp (normalizedResponseRaw observation nontrivial half) 2 volume :=
  (Lp.memLp (response observation nontrivial half - unitCoefficient observation nontrivial half •
    burnolUnitTailResponse coord 4)).ae_eq (normalized_read observation nontrivial half)

def normalizedResponse : BurnolL2 :=
  (normalized_native observation nontrivial half).toLp (normalizedResponseRaw observation nontrivial half)

theorem actual_normalized_raw : (normalizedResponse observation nontrivial half : ℝ → ℂ) =ᵐ[volume]
    normalizedResponseRaw observation nontrivial half := (normalized_native observation nontrivial half).coeFn_toLp

theorem actual_normalized_update : (value observation nontrivial half : BurnolL2) =
    paWave observation nontrivial half + unitCoefficient observation nontrivial half • burnolUnitTailResponse coord 4 +
      normalizedResponse observation nontrivial half := by
  have read : response observation nontrivial half - unitCoefficient observation nontrivial half • burnolUnitTailResponse coord 4 =
      normalizedResponse observation nontrivial half := Lp.ext
    ((normalized_read observation nontrivial half).trans (actual_normalized_raw observation nontrivial half).symm)
  rw [actual_source_update]
  linear_combination (norm := module) read

theorem actual_normalized_physical : normalizedResponse observation nontrivial half ∈ evenBurnolClosedFace q := by
  obtain ⟨ambient, _, wave⟩ := Submodule.mem_map.mp (actual_pa_wave observation nontrivial half)
  have waveMem : paWave observation nontrivial half ∈ (evenBurnolClosedFace q).toSubmodule := by
    rw [← wave]
    exact ambient.property
  have responseMem : response observation nontrivial half ∈ (evenBurnolClosedFace q).toSubmodule := by
    have same : response observation nontrivial half = (value observation nontrivial half : BurnolL2) - paWave observation nontrivial half := by
      rw [actual_source_update]
      abel
    rw [same]
    exact Submodule.sub_mem _ (value observation nontrivial half).property waveMem
  have unitMem := burnolZeroOwnedUnitTailResponse_physical observation nontrivial half.down
  have same : burnolDivisionZeroCompletedMellinCoordinate observation half.down = coord := by
    apply coordinate_eq
    rfl
  rw [same] at unitMem
  have read : normalizedResponse observation nontrivial half = response observation nontrivial half -
      unitCoefficient observation nontrivial half • burnolUnitTailResponse coord 4 :=
    (Lp.ext ((normalized_read observation nontrivial half).trans (actual_normalized_raw observation nontrivial half).symm)).symm
  rw [read]
  exact Submodule.sub_mem _ responseMem (Submodule.smul_mem _ _ unitMem)

/-- Both source-generated payments preserve the cotest of this same actual projected R update. -/
theorem actual_normalized_K_price :
    inner ℂ (burnolCompletedMellinRieszVector coord : BurnolL2) (value observation nontrivial half : BurnolL2) =
      inner ℂ (burnolCompletedMellinRieszVector coord : BurnolL2) (normalizedResponse observation nontrivial half) := by
  have orthogonal := riemannZeta_zero_burnolCompletedMellinRieszVector_mem_Pa_orthogonal coord observation.mathlibZero
  obtain ⟨ambient, ambientPa, wave⟩ := Submodule.mem_map.mp (actual_pa_wave observation nontrivial half)
  have paid : inner ℂ (burnolCompletedMellinRieszVector coord : BurnolL2) (paWave observation nontrivial half) = 0 := by
    rw [← wave]
    exact inner_eq_zero_symm.mp (orthogonal ambient ambientPa)
  have unitPaid := OriginalKCrossParameterRAdjointSource.UnitKSource.wholeUnitSourcePrice_zero observation nontrivial half
  unfold OriginalKDirectRCofinalOutsideVolterraSource.wholeUnitSourcePrice at unitPaid
  rw [OriginalKSourceResolventReconstruction.generatedK_eq_original] at unitPaid
  rw [actual_normalized_update, inner_add_right, inner_add_right, inner_smul_right, paid, unitPaid, mul_zero, zero_add, zero_add]


/-- This source feed belongs to the Fourier face of the same literal R occurrence. -/
theorem actual_original_R_face : value observation nontrivial half =
    evenFaceFourierEquiv q (P (OriginalWholeDebtRJointMobiusRActionSource.sourceNext observation nontrivial half)) := by
  unfold value
  rw [OriginalWholeDebtRJointMobiusTateRSource.actual_updated_wave]
  apply Subtype.ext
  exact (fourierL2_evenBurnolPhysicalProjection q _).symm

/-- The complete source update writes back with the original full B column and the original amplitude. -/
theorem actual_same_occurrence_writeback : OriginalWholeDebtRJointMobiusRActionSource.sourceNext observation nontrivial half =
    fourierL2.symm (paWave observation nontrivial half +
      unitCoefficient observation nontrivial half • burnolUnitTailResponse coord 4 + normalizedResponse observation nontrivial half) +
        T.homogeneousCoefficient coord • OriginalKCrossParameterRAdjointSource.PhysicalOutsideSource.physicalOutsideColumn coord := by
  have read : fourierL2.symm (value observation nontrivial half : BurnolL2) =
      (P (OriginalWholeDebtRJointMobiusRActionSource.sourceNext observation nontrivial half) : BurnolL2) := by
    rw [actual_original_R_face]
    change fourierL2.symm (fourierL2 _) = _
    exact fourierL2.symm_apply_apply _
  have full := OriginalWholeDebtRJointMobiusTateRSource.actual_complete_B_writeback observation nontrivial half
  rw [OriginalWholeDebtRJointMobiusTateRSource.actual_source_writeback] at full
  rw [← read, actual_normalized_update] at full
  exact full

theorem actual_normalized_zero_window : (normalizedResponse observation nontrivial half : ℝ → ℂ)
    =ᵐ[volume.restrict (symmetricInterval (4 : ℝ))] fun _ => 0 := by
  filter_upwards [ae_restrict_of_ae (actual_normalized_raw observation nontrivial half),
    ae_restrict_mem (measurableSet_symmetricInterval (4 : ℝ))] with x raw inside
  exact raw.trans (forward_zero_window _ (actual_normalized_source_gap observation nontrivial half) (abs_le.mpr inside))


private theorem actual_adjoint : w = OriginalKFullAdjointSource.sourceAdjoint
    (OriginalPrimitiveRankBalance.conjugateCoordinate coord) (OriginalWholeDebtRJointMobiusUnitSource.response coord) := by
  rw [OriginalWholeDebtRJointMobiusTateRSource.actual_updated_wave, actual_fourier_next,
    adjoint_volterra, conjugateCoordinate_twice]

private theorem actual_amplitude : OriginalKCrossParameterRAdjointSource.PhysicalDefectSource.physicalAmplitude
    (OriginalPrimitiveRankBalance.conjugateCoordinate coord)
      ⟨OriginalWholeDebtRJointMobiusUnitSource.response coord,
        OriginalWholeDebtRJointMobiusUnitSource.actual_physical observation nontrivial half⟩ =
          T.homogeneousCoefficient coord := by
  change (-2 : ℂ) * burnolCompletedMellinEvaluator
    (OriginalPrimitiveRankBalance.conjugateCoordinate (OriginalPrimitiveRankBalance.conjugateCoordinate coord)) _ = _
  rw [conjugateCoordinate_twice, ← burnolCompletedMellinRieszVector_readback]
  rfl

/-- The actual B columns are dependent reads of the same source action, not free profile data. -/
theorem actual_B_columns :
    burnolAmbientMeanZeroFirstCorrection w = T.homogeneousCoefficient coord •
      OriginalKDirectRCofinalOutsideVolterraSource.hPowerBColumn (OriginalPrimitiveRankBalance.conjugateCoordinate coord) ∧
    second observation nontrivial half = T.homogeneousCoefficient coord •
      OriginalKDirectRCofinalOutsideVolterraSource.hPowerBSecond (OriginalPrimitiveRankBalance.conjugateCoordinate coord) := by
  let physical : BurnolPaAmbientCarrier := ⟨OriginalWholeDebtRJointMobiusUnitSource.response coord,
    OriginalWholeDebtRJointMobiusUnitSource.actual_physical observation nontrivial half⟩
  have position : burnolAmbientMeanZeroPosition w = T.homogeneousCoefficient coord •
      OriginalRieszFinitePairing.CoPoisson.Ward.SingularCounting.centeredPower (OriginalPrimitiveRankBalance.conjugateCoordinate coord) := by
    change OriginalKDirectRCofinalOutsideVolterraSource.quarterCotest (burnolAmbientEvenPart w) = _
    rw [actual_adjoint, adjoint_evenPart _ physical,
      OriginalKCrossParameterRAdjointSource.PhysicalDefectSource.physical_adjoint_quarter_source _ physical,
      actual_amplitude]
  have Fourier : burnolAmbientMeanZeroFourier w = 0 := by
    change OriginalKDirectRCofinalOutsideVolterraSource.quarterCotest (fourierL2 (burnolAmbientEvenPart w)) = _
    rw [actual_adjoint, adjoint_evenPart _ physical, adjoint_fourier_eq_inverse _ physical,
      OriginalKCrossParameterRAdjointSource.PhysicalDefectSource.physical_adjoint_inverseFourier_quarter_zero _ physical]
  have first : burnolAmbientMeanZeroFirstCorrection w = T.homogeneousCoefficient coord •
      OriginalKDirectRCofinalOutsideVolterraSource.hPowerBColumn (OriginalPrimitiveRankBalance.conjugateCoordinate coord) := by
    change burnolMeanZeroBlockInverse (burnolAmbientMeanZeroPosition w -
      burnolMeanZeroTruncatedFourier (burnolAmbientMeanZeroFourier w)) = _
    rw [position, Fourier, map_zero, sub_zero, map_smul]
    rfl
  refine ⟨first, ?_⟩
  change burnolAmbientMeanZeroFourier w - burnolMeanZeroTruncatedFourier (burnolAmbientMeanZeroFirstCorrection w) = _
  rw [Fourier, first, map_smul, zero_sub]
  simp only [OriginalKDirectRCofinalOutsideVolterraSource.hPowerBSecond, smul_neg]

def canonicalBProfile (coordinate : BurnolCompletedMellinCoordinate) (x : ℝ) : ℂ :=
  T.powerRaw coordinate x -
    (Constructor.fourierRaw (OriginalKDirectRCofinalOutsideVolterraSource.hPowerBSecond
        (OriginalPrimitiveRankBalance.conjugateCoordinate coordinate) : Hq) x +
      Constructor.fourierRaw (OriginalKDirectRCofinalOutsideVolterraSource.hPowerBSecond
        (OriginalPrimitiveRankBalance.conjugateCoordinate coordinate) : Hq) (-x)) / 2

theorem actual_outer_source (x : ℝ) : outerProfile observation nontrivial half x =
    T.homogeneousCoefficient coord * canonicalBProfile coord x := by
  unfold outerProfile canonicalBProfile
  rw [(actual_B_columns observation nontrivial half).2]
  simp only [SetLike.val_smul]
  change T.homogeneousCoefficient coord * T.powerRaw coord x -
    (burnolRadiusTruncatedFourierRaw q (T.homogeneousCoefficient coord • _) x +
      burnolRadiusTruncatedFourierRaw q (T.homogeneousCoefficient coord • _) (-x)) / 2 = _
  rw [burnolRadiusTruncatedFourierRaw_smul]
  simp only [Pi.smul_apply, smul_eq_mul]
  simp only [Constructor.fourierRaw_state]
  ring

end OriginalWholeDebtRJointMobiusReturnSource
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
