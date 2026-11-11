import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.WholeDebtRJointMobiusReturnSource
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCrossParameterRAdjointSource.UnweightedCayleySource

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalWholeDebtRJointMobiusReturnAction
open Complex MeasureTheory BurnolPhysicalState
open OriginalKCrossParameterRAdjointSource.CayleyEnergySource
open OriginalKCrossParameterRAdjointSource.CayleyIntertwiningSource
open OriginalKDirectRCofinalOutsideVolterraSource
open scoped InnerProductSpace
open private actual_adjoint actual_amplitude from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.WholeDebtRJointMobiusReturnSource
open private source_right_inverse source_B_block physical_O from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCrossParameterRAdjointSource.CayleyIntertwiningSource
open private conjugateCoordinate_twice from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKDirectRCofinalOutsideVolterraSource.PaAdjointSource
namespace J
export OriginalWholeDebtRJointMobiusReturnSource
  (value paWave unitCoefficient normalizedResponse actual_normalized_update actual_B_columns actual_original_R_face)
end J
variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
variable (half : OriginalKCombCalculation.Half observation)
local notation "q" => (1 / 4 : ℝ)
local notation "coord" => OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half
local notation "bar" => OriginalPrimitiveRankBalance.conjugateCoordinate coord
local notation "u" => OriginalWholeDebtRJointMobiusUnitSource.response coord
local notation "a" => OriginalWholeDebtRJointMobiusTateRSource.homogeneousCoefficient coord
local notation "d" => (sourceDamping bar : ℂ)
local notation "w" => OriginalWholeDebtRJointMobiusTateRSource.updatedWave observation nontrivial half
local notation "P" => burnolEvenAmbientProjection
local notation "O" => OriginalKCombPhysicalAction.physicalRemainder
local notation "U" => sourceCayley bar
local notation "H" => hPowerPhysicalCorrection bar

/-- The new source's physical response is the actual return input of the same Cayley action. -/
def returnInput : BurnolL2 := u + d • (J.paWave observation nontrivial half +
  J.unitCoefficient observation nontrivial half • burnolUnitTailResponse coord 4 +
    J.normalizedResponse observation nontrivial half)

def returned : BurnolPaAmbientCarrier := P (U (returnInput observation nontrivial half))

def returnAmplitude : ℂ := 2 * d ^ 2 * a * ((‖H‖ ^ 2 : ℝ) : ℂ)

theorem actual_source_return_input : returnInput observation nontrivial half =
    u + d • (J.value observation nontrivial half : BurnolL2) := by
  rw [returnInput, ← J.actual_normalized_update]

private theorem actual_outside_adjoint : O (sourceAdjointCayley bar u) = (d * a) • H := by
  let physical : BurnolPaAmbientCarrier := ⟨u, OriginalWholeDebtRJointMobiusUnitSource.actual_physical observation nontrivial half⟩
  have outsideWave : O w = a • H := by
    have generated := congrArg fourierL2
      (OriginalWholeDebtRJointMobiusReturnSource.actual_same_occurrence_writeback observation nontrivial half)
    rw [map_add, map_smul, fourierL2.apply_symm_apply] at generated
    change fourierL2 (OriginalWholeDebtRJointMobiusRActionSource.sourceNext observation nontrivial half) =
      J.paWave observation nontrivial half + J.unitCoefficient observation nontrivial half • burnolUnitTailResponse coord 4 +
        J.normalizedResponse observation nontrivial half + a • fourierL2 (fourierL2.symm H) at generated
    rw [fourierL2.apply_symm_apply, ← J.actual_normalized_update,
      ← OriginalWholeDebtRJointMobiusTateRSource.actual_updated_wave] at generated
    rw [show O w = w - (P w : BurnolL2) from Submodule.starProjection_orthogonal_val w]
    change w - (J.value observation nontrivial half : BurnolL2) = _
    linear_combination (norm := module) generated

  rw [sourceAdjointCayley, map_add, map_smul, physical_O physical,
    ← actual_adjoint observation nontrivial half, outsideWave, zero_add, smul_smul]

private theorem actual_inside_adjoint : (P (sourceAdjointCayley bar u) : BurnolL2) =
    returnInput observation nontrivial half := by
  let physical : BurnolPaAmbientCarrier := ⟨u, OriginalWholeDebtRJointMobiusUnitSource.actual_physical observation nontrivial half⟩
  have fixed : P u = physical := Submodule.orthogonalProjectionOnto_mem_subspace_eq_self physical
  rw [sourceAdjointCayley, map_add, map_smul, fixed, ← actual_adjoint observation nontrivial half]
  rw [actual_source_return_input]
  rfl

/-- The independently generated outside B column is paid by the original incoming R action. -/
private theorem actual_outside_return : (P (U (O (sourceAdjointCayley bar u))) : BurnolL2) =
    (-returnAmplitude observation nontrivial half) • (burnolCompletedMellinRieszVector coord : BurnolL2) := by
  have source := source_B_block bar (sourceAdjointCayley bar u)
  change (P (U (O (sourceAdjointCayley bar u))) : BurnolL2) = _ at source
  rw [actual_outside_adjoint, inner_smul_right, inner_self_eq_norm_sq_to_K,
    conjugateCoordinate_twice, OriginalKSourceResolventReconstruction.generatedK_eq_original] at source
  rw [actual_outside_adjoint]
  calc
    _ = (-2 * d * ((d * a) * (‖H‖ : ℂ) ^ 2)) • (burnolCompletedMellinRieszVector coord : BurnolL2) := source
    _ = _ := by
      congr 1
      unfold returnAmplitude
      push_cast
      ring

/-- The source-generated return closes as a whole vector with the original K defect. -/
theorem actual_complete_return : (returned observation nontrivial half : BurnolL2) = u +
    returnAmplitude observation nontrivial half • (burnolCompletedMellinRieszVector coord : BurnolL2) := by
  have inverse : U (sourceAdjointCayley bar u) = u := by
    rw [← sourceCayley_actual_adjoint]
    exact source_right_inverse bar u
  have split : sourceAdjointCayley bar u = returnInput observation nontrivial half + O (sourceAdjointCayley bar u) := by
    rw [← actual_inside_adjoint observation nontrivial half,
      show O (sourceAdjointCayley bar u) = sourceAdjointCayley bar u -
        (P (sourceAdjointCayley bar u) : BurnolL2) from Submodule.starProjection_orthogonal_val _]
    abel
  have source := congrArg (fun v : BurnolL2 => (P (U v) : BurnolL2)) split
  rw [inverse, map_add, map_add] at source
  change (P u : BurnolL2) = (P (U (returnInput observation nontrivial half)) : BurnolL2) +
    (P (U (O (sourceAdjointCayley bar u))) : BurnolL2) at source
  rw [actual_outside_return] at source
  have fixed : P u = (⟨u, OriginalWholeDebtRJointMobiusUnitSource.actual_physical observation nontrivial half⟩ : BurnolPaAmbientCarrier) :=
    Submodule.orthogonalProjectionOnto_mem_subspace_eq_self
      (⟨u, OriginalWholeDebtRJointMobiusUnitSource.actual_physical observation nontrivial half⟩ : BurnolPaAmbientCarrier)
  rw [fixed] at source
  change u = (returned observation nontrivial half : BurnolL2) +
    (-returnAmplitude observation nontrivial half) • (burnolCompletedMellinRieszVector coord : BurnolL2) at source
  linear_combination (norm := module) -source


theorem actual_return_amplitude_ne_zero : returnAmplitude observation nontrivial half ≠ 0 := by
  have damping : d ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt (sourceDamping_pos bar))
  have power : ((‖H‖ ^ 2 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast pow_ne_zero 2 (norm_ne_zero_iff.mpr
      (OriginalKCrossParameterRAdjointSource.UnweightedCayleySource.powerCorrection_ne_zero bar))
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 2 damping))
    (OriginalWholeDebtRJointMobiusTateRSource.actual_homogeneous_ne_zero observation nontrivial half)) power

/-- The actual return's source-born K defect cannot be dropped. -/
theorem actual_return_not_fixed : (returned observation nontrivial half : BurnolL2) ≠ u := by
  have kernel : (burnolCompletedMellinRieszVector coord : BurnolL2) ≠ 0 := by
    intro zero
    apply OriginalWholeDebtRJointMobiusTateRSource.actual_homogeneous_ne_zero observation nontrivial half
    unfold OriginalWholeDebtRJointMobiusTateRSource.homogeneousCoefficient
    rw [zero, inner_zero_left, mul_zero]
  intro fixed
  have source := actual_complete_return observation nontrivial half
  rw [fixed] at source
  have defect : returnAmplitude observation nontrivial half • (burnolCompletedMellinRieszVector coord : BurnolL2) = 0 := by
    linear_combination (norm := module) -source
  exact (smul_ne_zero (actual_return_amplitude_ne_zero observation nontrivial half) kernel) defect

/-- Both original K/FK mouths consume this same source update through their actual generated adjoint fields. -/
theorem actual_joint_source_return_reads :
    inner ℂ (burnolCompletedMellinRieszVector coord : BurnolL2) (J.value observation nontrivial half : BurnolL2) =
      inner ℂ (OriginalKCrossParameterRAdjointSource.sourceConjugateKResponse coord) u ∧
    inner ℂ (fourierL2 (burnolCompletedMellinRieszVector coord : BurnolL2)) (J.value observation nontrivial half : BurnolL2) =
      inner ℂ (OriginalKCrossParameterRAdjointSource.sourceFKResponse coord bar) u := by
  let nextValue : BurnolL2 := OriginalWholeDebtRJointMobiusRActionSource.sourceNext observation nontrivial half
  have firstProjection := Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left
    (burnolCompletedMellinRieszVector coord) w
  change inner ℂ (burnolCompletedMellinRieszVector coord : BurnolL2) (P w : BurnolL2) =
    inner ℂ (burnolCompletedMellinRieszVector coord : BurnolL2) w at firstProjection
  have secondProjection := Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left
    (evenFaceFourierEquiv q (burnolCompletedMellinRieszVector coord)) w
  have source := OriginalKCrossParameterRAdjointSource.original_R_adjoint_reads coord
    (OriginalWholeDebtRJointMobiusRActionSource.sourceInput observation nontrivial half : BurnolL2)
  have firstFourier := fourierL2.inner_map_map (burnolCompletedMellinRieszVector coord : BurnolL2) nextValue
  have kernelEven : reflectL2 (burnolCompletedMellinRieszVector coord : BurnolL2) =
      (burnolCompletedMellinRieszVector coord : BurnolL2) :=
    mem_evenL2ClosedFace_iff.mp (burnolCompletedMellinRieszVector coord).property.2
  have secondFourier := fourierL2.inner_map_map (fourierL2 (burnolCompletedMellinRieszVector coord : BurnolL2)) nextValue
  rw [fourierL2_fourierL2, kernelEven] at secondFourier
  have firstNative := fourierL2.inner_map_map (OriginalKCrossParameterRAdjointSource.sourceConjugateKResponse coord) u
  have secondNative := fourierL2.inner_map_map (OriginalKCrossParameterRAdjointSource.sourceFKResponse coord bar) u
  constructor
  · change inner ℂ (burnolCompletedMellinRieszVector coord : BurnolL2) (P w : BurnolL2) = _
    rw [firstProjection, OriginalWholeDebtRJointMobiusTateRSource.actual_updated_wave, secondFourier]
    exact source.2.trans firstNative
  · change inner ℂ (fourierL2 (burnolCompletedMellinRieszVector coord : BurnolL2)) (P w : BurnolL2) = _
    change inner ℂ (fourierL2 (burnolCompletedMellinRieszVector coord : BurnolL2)) (P w : BurnolL2) =
      inner ℂ (fourierL2 (burnolCompletedMellinRieszVector coord : BurnolL2)) w at secondProjection
    rw [secondProjection, OriginalWholeDebtRJointMobiusTateRSource.actual_updated_wave, firstFourier]
    exact source.1.trans secondNative

end OriginalWholeDebtRJointMobiusReturnAction
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
