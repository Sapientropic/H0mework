import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.Source
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCrossParameterRAdjointSource.PaFeedbackSource
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCrossParameterRAdjointSource.UnitKSource

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKFiniteOrderRelease.UnitJetSource
open Complex MeasureTheory Set BurnolPhysicalState
open NoIslandNoMagic.CanonicalRiemann NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
open OriginalKSourceResolventReconstruction OriginalKFullAdjointSource
open OriginalKDirectRCofinalOutsideVolterraSource
open OriginalKCrossParameterRAdjointSource.SharedOutsideSource
open OriginalKCrossParameterRAdjointSource.PaFeedbackSource
open OriginalKCrossParameterRAdjointSource.PaSpectralSource
open OriginalKCrossParameterRAdjointSource.UnitKSource
open scoped InnerProductSpace
local notation "q" => burnolUnscaledCommonGapRadius
local notation "F" => evenFaceFourierEquiv q
local instance unitJetPhysicalComplete : CompleteSpace BurnolPaAmbientCarrier := by
  apply IsComplete.completeSpace_coe
  exact (evenBurnolClosedFace q).isClosed.isComplete

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃n:Nat,observation.coordinate=-2*(n+1))
variable (half : OriginalKCombCalculation.Half observation)
local notation "c" => burnolDivisionZeroCompletedMellinCoordinate observation half.down
local notation "m" => generatedRiemannXiZeroOrder ActualAnalyticOwner observation.coordinate
local notation "e" => burnolAnalyticComplementExpectedPhysicalFourierRead ActualAnalyticOwner observation

/-- The exact natural order is read from the original observation, without a simple-zero premise. -/
def unitJetPrice :ℂ := if m=1 then e else 0

def unitJetPaCoefficient :ℂ := if m=1 then -hQuarterAmplitude c*star e else 0

def unitJetPaField :BurnolPaAmbientCarrier :=
  unitJetPaCoefficient observation half • paCoefficientSource c

def unitJetQSource :BurnolL2 := sourceL c-(unitJetPaField observation half:BurnolL2)

def unitJetFeedbackCoefficient :ℂ := if m=1 then -star (hQuarterAmplitude c)*e else 0

private theorem FourierK_Pa_read (value:BurnolPaAmbientCarrier)
    (inside:value∈burnolCompactCoPoissonClosedRange) :
    inner ℂ (F (burnolCompletedMellinRieszVector c)) value=0 := by
  have source := allPa_fourier_source_read c value inside
  rw [show riemannZeta (c).value=0 from observation.mathlibZero,zero_div,zero_mul] at source
  exact source

private theorem physical_fourier_read (value:BurnolPaAmbientCarrier) :
    CombSource.Division.fourierRead observation half.down (value:BurnolL2)=
      inner ℂ (F (burnolCompletedMellinRieszVector c)) value := by
  have fixed : burnolEvenAmbientProjection (value:BurnolL2)=value :=
    Submodule.orthogonalProjectionOnto_mem_subspace_eq_self value
  change burnolCompletedMellinEvaluator c (evenFaceFourier q (burnolEvenAmbientProjection (value:BurnolL2)))=_
  rw [fixed,←burnolCompletedMellinRieszVector_readback]
  have moved := (evenFaceFourierEquiv q).inner_map_map (burnolCompletedMellinRieszVector c) (F value)
  have invol : F (F value)=value := evenFaceFourier_involutive q value
  rw [invol] at moved
  exact moved.symm

include nontrivial

private theorem actual_first_response_read :
    inner ℂ (F (burnolCompletedMellinRieszVector c))
      (burnolPaCombPhysicalResponse observation nontrivial half.down 0)=
      2*burnolPaCombResponseCoefficient observation.coordinate 0*unitJetPrice observation := by
  rw [←physical_fourier_read observation half (burnolPaCombPhysicalResponse observation nontrivial half.down 0)]
  have actual : (burnolPaCombPhysicalResponse observation nontrivial half.down 0:BurnolL2)=
      actor observation half.down 0 1 := by
    rw [show 1=0+1 by rfl,actor_succ]
    rfl
  rw [actual]
  by_cases simple:m=1
  · have source := actor_exact_order_fourier observation nontrivial half.down 0
    rw [simple] at source
    rw [source,unitJetPrice,if_pos simple]
  · have positive := generatedRiemannXiZeroOrder_pos observation nontrivial
    have source := CombSource.Division.actual_comb_fourier_zero observation nontrivial half.down 0 1 (by omega)
    change CombSource.Division.fourierRead observation half.down (actor observation half.down 0 1)=0 at source
    rw [source,unitJetPrice,if_neg simple,mul_zero]

private theorem actual_unit_one_price :
    inner ℂ (F (burnolCompletedMellinRieszVector c):BurnolPaAmbientCarrier)
      (burnolZeroOwnedUnitOneState observation nontrivial half.down)=unitJetPrice observation := by
  have orthogonal : F (burnolCompletedMellinRieszVector c)∈burnolCompactCoPoissonClosedRange.toSubmoduleᗮ := by
    intro value inside
    exact inner_eq_zero_symm.mpr (FourierK_Pa_read observation half value inside)
  let Q := burnolCompactCoPoissonClosedRange.toSubmoduleᗮ.starProjection
  have normal (value:BurnolPaAmbientCarrier) :
      inner ℂ (F (burnolCompletedMellinRieszVector c)) (Q value)=
      inner ℂ (F (burnolCompletedMellinRieszVector c)) value :=
    burnolCompactCoPoissonClosedRange.toSubmoduleᗮ.inner_orthogonalProjectionOnto_eq_of_mem_left
      ⟨F (burnolCompletedMellinRieszVector c),orthogonal⟩ value
  have scaled := congrArg (inner ℂ (F (burnolCompletedMellinRieszVector c)))
    (burnolPaCombPhysicalResponse_scaledQ observation nontrivial half.down 0)
  rw [inner_smul_right,inner_smul_right,normal,normal] at scaled
  simp only [Nat.cast_zero] at scaled
  have parameterNe : observation.coordinate≠0 := by
    exact ne_of_apply_ne Complex.re (by simpa only [zero_re] using (lt_trans (by norm_num) half.down).ne')
  have factor : ((0:ℂ)+2)*(Complex.exp (observation.coordinate*(Real.log (1+burnolPaCombSourceWidth 0):ℂ))-1)=
      (observation.coordinate/2)*(2*burnolPaCombResponseCoefficient observation.coordinate 0) := by
    unfold burnolPaCombResponseCoefficient
    simp only [Nat.cast_zero]
    field_simp [parameterNe]
  rw [factor] at scaled
  have response : inner ℂ (F (burnolCompletedMellinRieszVector c))
      (burnolPaCombPhysicalResponse observation nontrivial half.down 0)=
      2*burnolPaCombResponseCoefficient observation.coordinate 0*
        inner ℂ (F (burnolCompletedMellinRieszVector c)) (burnolZeroOwnedUnitOneState observation nontrivial half.down) := by
    apply mul_left_cancel₀ (div_ne_zero parameterNe (by norm_num : (2:ℂ)≠0))
    rw [scaled]
    ring
  have coefficientNe : 2*burnolPaCombResponseCoefficient observation.coordinate 0≠0 :=
    mul_ne_zero (by norm_num) (burnolPaCombResponseCoefficient_ne_zero observation.coordinate (by linarith [half.down]) 0)
  exact mul_left_cancel₀ coefficientNe (response.symm.trans (actual_first_response_read observation nontrivial half))

/-- The original unit1 and unit4 differ by the actual Pa shell; no unit is declared Pa. -/
theorem actual_fourier_whole_unit_source : fourierWholeUnitSourcePrice c=unitJetPrice observation := by
  have one := actual_unit_one_price observation nontrivial half
  change inner ℂ (F (burnolCompletedMellinRieszVector c):BurnolL2) (burnolUnitTailResponse c 1)=_ at one
  obtain ⟨wave,wavePa,waveRead⟩ := Submodule.mem_map.mp
    (burnolUnitPowerShellWave_originalPa c 1 (by norm_num) (by norm_num))
  have shellZero : inner ℂ (F (burnolCompletedMellinRieszVector c):BurnolL2) (wave:BurnolL2)=0 :=
    FourierK_Pa_read observation half wave wavePa
  have shell := burnolUnitTailResponse_shell c 1 (by norm_num) (by norm_num)
  rw [←waveRead] at shell
  have price := congrArg (inner ℂ (F (burnolCompletedMellinRieszVector c):BurnolL2)) shell
  rw [inner_sub_right] at price
  change _=inner ℂ (F (burnolCompletedMellinRieszVector c):BurnolL2) (wave:BurnolL2) at price
  rw [shellZero] at price
  change inner ℂ (F (burnolCompletedMellinRieszVector c):BurnolL2) (burnolUnitTailResponse c 1)-
    inner ℂ (F (burnolCompletedMellinRieszVector c):BurnolL2) (burnolUnitTailResponse c 4)=0 at price
  unfold fourierWholeUnitSourcePrice
  rw [generatedK_eq_original]
  change inner ℂ (F (burnolCompletedMellinRieszVector c):BurnolL2) (burnolUnitTailResponse c 4)=_
  linear_combination one-price

/-- Both full unit prices are now consumed to generate the actual Pa coefficient. -/
theorem actual_pa_coefficient_source : sourcePaCoefficient c=unitJetPaCoefficient observation half := by
  have diagonal := wholeUnitSourcePrice_zero observation nontrivial half
  change wholeUnitSourcePrice c=0 at diagonal
  rw [sourcePaCoefficient,diagonal,actual_fourier_whole_unit_source observation nontrivial half,
    star_zero,mul_zero,zero_sub]
  unfold unitJetPrice unitJetPaCoefficient
  split_ifs <;> simp

theorem actual_pa_field_source : sourcePaField c=unitJetPaField observation half := by
  rw [sourcePaField,actual_pa_coefficient_source observation nontrivial half]
  rfl

theorem actual_Q_source : sourceQ c=unitJetQSource observation half := by
  rw [sourceQ,actual_pa_field_source observation nontrivial half]
  rfl

/-- A full Pa source field and the complete complementary Q vector, generated by the exact order. -/
theorem actual_sourceL_E_Q :
    PA.E (sourceL c)=unitJetPaField observation half ∧
    (PA.Q (sourceL c):BurnolL2)=unitJetQSource observation half := by
  constructor
  · exact (sourceL_E_actual c observation.mathlibZero).trans (actual_pa_field_source observation nontrivial half)
  · exact (sourceL_Q_actual c observation.mathlibZero).trans (actual_Q_source observation nontrivial half)

private theorem actual_star_coefficient : star (sourcePaCoefficient c)=unitJetFeedbackCoefficient observation half := by
  rw [actual_pa_coefficient_source observation nontrivial half]
  unfold unitJetPaCoefficient unitJetFeedbackCoefficient
  split_ifs
  · simp only [star_mul,star_neg,star_star]
    ring
  · simp only [star_zero]

/-- The full original feedback consumes the newly generated Pa coefficient and complete Q field. -/
theorem actual_sourceL_Q_feedback (value:BurnolL2) :
    inner ℂ (sourceKernelCombo c) (PA.Q (burnolDirectRightResolvent ((c).value/2) value):BurnolL2)=
      unitJetFeedbackCoefficient observation half*burnolPaResolventSourceCoefficient c (PA.E value)+
        inner ℂ (unitJetQSource observation half) (PA.Q value:BurnolL2) := by
  have source := original_R_sourceL_Q_feedback c observation.mathlibZero value
  rw [actual_star_coefficient observation nontrivial half,actual_Q_source observation nontrivial half] at source
  exact source

end OriginalKFiniteOrderRelease.UnitJetSource
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
