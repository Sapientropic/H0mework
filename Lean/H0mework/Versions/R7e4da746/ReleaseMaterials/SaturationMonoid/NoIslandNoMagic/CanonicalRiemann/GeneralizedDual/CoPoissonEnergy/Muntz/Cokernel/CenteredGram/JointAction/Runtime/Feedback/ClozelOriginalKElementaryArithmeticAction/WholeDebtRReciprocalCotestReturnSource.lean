import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.WholeDebtRReciprocalCotestActionSource
import H0mework.Versions.R7e4da746.Arithmetic.RieszSynthesis.WholeTranspose

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
set_option maxRecDepth 6000
set_option cleanup.letToHave false

noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalWholeDebtRReciprocalCotestReturnSource
open Complex MeasureTheory BurnolPhysicalState OriginalRieszFiniteSynthesis FiniteMobiusResolventFlux
open OriginalWholeDebtRPowerWaveDilationSource OriginalKSourceResolventReconstruction
open OriginalWholeDebtRAdjointContactSource OriginalKPairedBEulerJunctionSource
open OriginalPaPhysicalGreen
open scoped InnerProductSpace
namespace A
export OriginalWholeDebtRReciprocalCotestActionSource
  (positionColumn fourierColumn reciprocalCotest weight weightedField effectCotest
   actual_columns position_supported fourier_supported weighted_field_action actual_defect_fee)
end A
local notation "q" => burnolUnscaledCommonGapRadius
local notation "Tate" => burnolTateReciprocalL2
local notation "sample" => fun value : BurnolL2 => burnolAnnulusSamplingL2 value 0
local notation "gap" => burnolConstantGapCoefficient q
local instance : CompleteSpace BurnolPaAmbientCarrier :=
  IsComplete.completeSpace_coe (evenBurnolClosedFace q).isClosed.isComplete

private theorem tate_pair (left right : BurnolL2) :
    inner ℂ left (Tate right) = inner ℂ (Tate left) right := by
  let action : BurnolL2 →ₗᵢ[ℂ] BurnolL2 :=
    { toLinearMap := burnolTateReciprocalL2.toLinearMap
      norm_map' := burnolTateReciprocalValue_norm }
  have paid := action.inner_map_map left (Tate right)
  change inner ℂ (Tate left) (Tate (Tate right)) = _ at paid
  rw [burnolTateReciprocalL2_involutive] at paid
  exact paid.symm

private theorem joint_transpose (x y : BurnolL2)
    (position : originalPhysicalCutoff (1/2 : ℝ) x = x)
    (fourier : originalPhysicalCutoff (1/2 : ℝ) y = y)
    (value : BurnolPaAmbientCarrier) :
    inner ℂ (x + fourierL2 y) (value : BurnolL2) =
      inner ℂ (sample x + Tate (sample y)) (M (value : BurnolL2)) +
        (gap value * star (∫ t : ℝ, x t) +
          gap (evenFaceFourierEquiv q value) * star (∫ t : ℝ, y t)) +
        inner ℂ (sample y) (D (value : BurnolL2)) := by
  have paid := twoColumn_wholeAmbient_transpose x y position fourier value
  rw [← lower_source_physical value,
    ← lower_source_physical (evenFaceFourierEquiv q value)] at paid
  have source : M (fourierL2 (value : BurnolL2)) =
      D (value : BurnolL2) + Tate (M (value : BurnolL2)) := by
    simp only [D, sub_apply, ContinuousLinearMap.comp_apply,
      LinearIsometry.coe_toContinuousLinearMap, LinearIsometryEquiv.coe_toLinearIsometry]
    module
  change inner ℂ (x + fourierL2 y) (value : BurnolL2) =
    (inner ℂ (sample x) (M (value : BurnolL2)) + gap value * star (∫ t : ℝ, x t)) +
    (inner ℂ (sample y) (M (fourierL2 (value : BurnolL2))) +
      gap (evenFaceFourierEquiv q value) * star (∫ t : ℝ, y t)) at paid
  rw [source, inner_add_right, tate_pair] at paid
  simp only [inner_add_left] at paid ⊢
  linear_combination paid

private def physicalK (coordinate : BurnolCompletedMellinCoordinate) : BurnolPaAmbientCarrier :=
  burnolCompletedMellinRieszVector coordinate
private def physicalFK (coordinate : BurnolCompletedMellinCoordinate) : BurnolPaAmbientCarrier :=
  evenFaceFourierEquiv q (physicalK coordinate)
private theorem physical_fk_value (coordinate : BurnolCompletedMellinCoordinate) :
    (physicalFK coordinate : BurnolL2) = fourierL2 (generatedK coordinate) := by
  change fourierL2 (burnolCompletedMellinRieszVector coordinate : BurnolL2) = _
  rw [generatedK_eq_original]

/-- Both original mean fields remain alongside the complete joint Mobius source. -/
private def meanPrice (coordinate : BurnolCompletedMellinCoordinate) : ℂ :=
  star (gap (physicalFK coordinate)) * (∫ t : ℝ, A.positionColumn coordinate t) +
    star (gap (evenFaceFourierEquiv q (physicalFK coordinate))) *
      (∫ t : ℝ, A.fourierColumn coordinate t)

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
variable (half : OriginalKCombCalculation.Half observation)
local notation "c" => OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half
local notation "wave" => pairedSource c junctionShift

def returnPrice : ℂ :=
  inner ℂ (M (fourierL2 (generatedK c)))
    (A.weight c • (sample (A.positionColumn c) + A.reciprocalCotest c)) +
    A.weight c * meanPrice c +
    inner ℂ (defectForcing observation nontrivial half) (A.effectCotest c)

theorem actual_weighted_wave :
    A.weight c * inner ℂ (fourierL2 (generatedK c)) wave =
      returnPrice observation nontrivial half := by
  have paid := joint_transpose (A.positionColumn c) (A.fourierColumn c)
    (A.position_supported c) (A.fourier_supported c) (physicalFK c)
  rw [← A.actual_columns c, physical_fk_value] at paid
  have weighted := congrArg (fun value : ℂ => star (A.weight c) * value) paid
  rw [mul_add, mul_add, A.actual_defect_fee observation nontrivial half] at weighted
  have conjugated := congrArg (starRingEnd ℂ) weighted
  simp only [map_add, map_mul, inner_conj_symm] at conjugated
  simp only [starRingEnd_apply, star_star] at conjugated
  unfold returnPrice meanPrice
  change A.weight c * inner ℂ (fourierL2 (generatedK c)) wave =
    inner ℂ (M (fourierL2 (generatedK c)))
      (A.weight c • (sample (A.positionColumn c) + Tate (sample (A.fourierColumn c)))) +
      A.weight c * _ + _
  rw [inner_smul_right]
  linear_combination conjugated

theorem actual_rho :
    A.weight c * ((2 * kernelMass c) *
      inner ℂ (BandFullStockEuler.correctionRaw c)
        (OriginalKCrossParameterRAdjointSource.PhysicalOutsideSource.physicalOutsideColumn c)) =
      returnPrice observation nontrivial half := by
  have paid := congrArg (fun value : ℂ => A.weight c * value)
    (rho_return c)
  exact paid.trans (actual_weighted_wave observation nontrivial half)


end OriginalWholeDebtRReciprocalCotestReturnSource
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
