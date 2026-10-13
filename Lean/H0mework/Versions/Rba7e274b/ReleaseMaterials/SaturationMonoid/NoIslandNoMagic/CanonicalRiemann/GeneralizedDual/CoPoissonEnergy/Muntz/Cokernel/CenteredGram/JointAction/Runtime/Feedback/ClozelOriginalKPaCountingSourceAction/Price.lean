import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKPaCountingSourceAction.Effect
import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKPaCountingSourceAction.Realization
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKPaCountingSourceAction
open Complex MeasureTheory Filter FourierTransform
open scoped InnerProductSpace Topology
open NoIslandNoMagic.CanonicalRiemann NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
open BurnolPhysicalState OriginalPaPhysicalGreen
local notation "Fphysical" => evenFaceFourierEquiv burnolUnscaledCommonGapRadius
local notation "K" => burnolCompletedMellinRieszVector
local instance paCountingPriceComplete : CompleteSpace BurnolPaAmbientCarrier :=by
 apply IsComplete.completeSpace_coe
 exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete


local notation "P" => burnolEvenAmbientProjection
local notation "Q" => OriginalKFullSourceRResponse.Paid.Q
variable (observation:GeneratedRiemannZeroObservation)
variable (nontrivial:¬∃ n:Nat,observation.coordinate=-2*(n+1))
variable (half:OriginalKCombCalculation.Half observation)
local notation "c" => (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half)

def actualWaveSource (h:ℝ) (nonnegative:0≤h) (bounded:h≤Real.log 2):BurnolPaAmbientCarrier:=
 OriginalCommonInverseForcing.SourceJoint.upperSourceWaveAmbient c h nonnegative bounded

def actualFiniteWavePairPrice (h:ℝ) (nonnegative:0≤h) (bounded:h≤Real.log 2) (n:Nat):ℂ:=
 star (inner ℂ (K c+Fphysical (K c)) (actualFinitePaCountingResponse c
  (actualWaveSource observation nontrivial half h nonnegative bounded) n))
def actualFiniteWaveSiblingPrice (h:ℝ) (nonnegative:0≤h) (bounded:h≤Real.log 2) (n:Nat):ℂ:=
 inner ℂ (K c-Fphysical (K c)) (actualFinitePaCountingResponse c
  (actualWaveSource observation nontrivial half h nonnegative bounded) n)
def actualWavePairPriceResidual (h:ℝ) (nonnegative:0≤h) (bounded:h≤Real.log 2) (n:Nat):ℂ:=
 star (inner ℂ (K c+Fphysical (K c)) (actualPaCountingResponseResidual c
  (actualWaveSource observation nontrivial half h nonnegative bounded) n))
def actualWaveSiblingPriceResidual (h:ℝ) (nonnegative:0≤h) (bounded:h≤Real.log 2) (n:Nat):ℂ:=
 inner ℂ (K c-Fphysical (K c)) (actualPaCountingResponseResidual c
  (actualWaveSource observation nontrivial half h nonnegative bounded) n)

/-- The original K's Pa-orthogonal physical reader consumes Q only after actual source R; no Pa membership is transferred to the finite ambient actor. -/
theorem actual_original_Q_orthogonal_reader (left:BurnolPaOrthogonalCarrier) (material:BurnolL2):
 inner ℂ (left:BurnolPaAmbientCarrier) (Q material)=inner ℂ (left:BurnolL2) material :=by
 have pa:=burnolCompactCoPoissonClosedRange.toSubmoduleᗮ.inner_orthogonalProjectionOnto_eq_of_mem_left left (P material)
 have physical:=(evenBurnolClosedFace burnolUnscaledCommonGapRadius).toSubmodule.inner_orthogonalProjectionOnto_eq_of_mem_left
  (left:BurnolPaAmbientCarrier) material
 exact pa.trans physical

/-- Same actual PaWave source receipt and complete original R/Q field generate both physical prices from the counting programme, preserving original K and its true Fourier sibling. -/
theorem actual_original_wave_counting_two_price_residuals (h:ℝ) (nonnegative:0≤h) (bounded:h≤Real.log 2) (n:Nat):
 OriginalKInsideDebtRSource.actualWavePaPairPrice observation nontrivial half h nonnegative bounded-
 actualFiniteWavePairPrice observation nontrivial half h nonnegative bounded n=
 actualWavePairPriceResidual observation nontrivial half h nonnegative bounded n ∧
 OriginalKInsideDebtRSource.actualWavePaSiblingPrice observation nontrivial half h nonnegative bounded-
 actualFiniteWaveSiblingPrice observation nontrivial half h nonnegative bounded n=
 actualWaveSiblingPriceResidual observation nontrivial half h nonnegative bounded n :=by
 let p:=actualWaveSource observation nontrivial half h nonnegative bounded
 have qualification:p∈burnolCompactCoPoissonClosedRange:=
  OriginalCommonInverseForcing.SourceJoint.actual_upper_ambient_inPa c h nonnegative bounded
 let k:BurnolPaOrthogonalCarrier:=⟨K c,riemannZeta_zero_burnolCompletedMellinRieszVector_mem_Pa_orthogonal c observation.mathlibZero⟩
 let fk:=burnolCompactCoPoissonActionSquare.orthogonalAction k
 have source:=actual_original_Pa_counting_response_residual c p qualification n
 have first:=congrArg (fun value:BurnolPaAmbientCarrier=>star (inner ℂ (K c+Fphysical (K c)) value)) source
 have second:=congrArg (inner ℂ (K c-Fphysical (K c))) source
 rw [inner_sub_right,star_sub] at first
 rw [inner_sub_right] at second
 have kread:=actual_original_Q_orthogonal_reader k (burnolDirectRightResolvent ((c).value/2) (p:BurnolL2))
 have fread:=actual_original_Q_orthogonal_reader fk (burnolDirectRightResolvent ((c).value/2) (p:BurnolL2))
 change inner ℂ (Fphysical (K c)) (Q (burnolDirectRightResolvent ((c).value/2) (p:BurnolL2)))=
  inner ℂ (fourierL2 (K c:BurnolL2)) (burnolDirectRightResolvent ((c).value/2) (p:BurnolL2)) at fread
 change inner ℂ (K c) (Q (burnolDirectRightResolvent ((c).value/2) (p:BurnolL2)))=
  inner ℂ (K c:BurnolL2) (burnolDirectRightResolvent ((c).value/2) (p:BurnolL2)) at kread
 rw [inner_add_left,kread,fread] at first
 rw [inner_sub_left,kread,fread] at second
 have kprice:=burnolPaResolvent_source_pairing c p qualification k
 have fprice:=burnolPaResolvent_source_pairing c p qualification fk
 change inner ℂ (K c:BurnolL2) (burnolDirectRightResolvent ((c).value/2) (p:BurnolL2))=
  burnolPaResolventSourceCoefficient c p*inner ℂ (K c:BurnolL2) (burnolUnitTailResponse c 4) at kprice
 change inner ℂ (fourierL2 (K c:BurnolL2)) (burnolDirectRightResolvent ((c).value/2) (p:BurnolL2))=
  burnolPaResolventSourceCoefficient c p*inner ℂ (fourierL2 (K c:BurnolL2)) (burnolUnitTailResponse c 4) at fprice
 rw [kprice,fprice] at first second
 unfold OriginalKInsideDebtRSource.actualWavePaPairPrice OriginalKInsideDebtRSource.actualWavePaSiblingPrice
  actualFiniteWavePairPrice actualFiniteWaveSiblingPrice actualWavePairPriceResidual actualWaveSiblingPriceResidual
 exact ⟨by simpa only [p,actualWaveSource,mul_add] using first,by simpa only [p,actualWaveSource,mul_sub] using second⟩

/-- Complete original wave prices retain their own source coefficient and full R/Q counting-source error, not a source norm projected margin. -/
theorem actual_original_wave_counting_two_price_errors (h:ℝ) (nonnegative:0≤h) (bounded:h≤Real.log 2) (n:Nat):
 ‖actualWavePairPriceResidual observation nontrivial half h nonnegative bounded n‖≤
 ‖K c+Fphysical (K c)‖*actualPaCountingResponseError c (actualWaveSource observation nontrivial half h nonnegative bounded) n ∧
 ‖actualWaveSiblingPriceResidual observation nontrivial half h nonnegative bounded n‖≤
 ‖K c-Fphysical (K c)‖*actualPaCountingResponseError c (actualWaveSource observation nontrivial half h nonnegative bounded) n :=by
 have qualification:=OriginalCommonInverseForcing.SourceJoint.actual_upper_ambient_inPa c h nonnegative bounded
 have source:=actual_original_Pa_counting_response_error c (actualWaveSource observation nontrivial half h nonnegative bounded) qualification n
 rw [actual_original_Pa_counting_response_residual c (actualWaveSource observation nontrivial half h nonnegative bounded) qualification n] at source
 constructor
 · unfold actualWavePairPriceResidual
   rw [norm_star]
   exact (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left source (norm_nonneg _))
 · unfold actualWaveSiblingPriceResidual
   exact (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left source (norm_nonneg _))

theorem actual_wave_counting_two_price_residuals_tendsto (h:ℝ) (nonnegative:0≤h) (bounded:h≤Real.log 2):
 Tendsto (actualWavePairPriceResidual observation nontrivial half h nonnegative bounded) atTop (𝓝 0) ∧
 Tendsto (actualWaveSiblingPriceResidual observation nontrivial half h nonnegative bounded) atTop (𝓝 0) :=by
 have paid:=actual_Pa_counting_response_error_tendsto c (actualWaveSource observation nontrivial half h nonnegative bounded)
 have costs:=actual_original_wave_counting_two_price_errors observation nontrivial half h nonnegative bounded
 constructor
 · apply tendsto_zero_iff_norm_tendsto_zero.mpr
   exact squeeze_zero (fun n=>norm_nonneg _) (fun n=>(costs n).1)
    (by simpa only [mul_zero] using paid.const_mul ‖K c+Fphysical (K c)‖)
 · apply tendsto_zero_iff_norm_tendsto_zero.mpr
   exact squeeze_zero (fun n=>norm_nonneg _) (fun n=>(costs n).2)
    (by simpa only [mul_zero] using paid.const_mul ‖K c-Fphysical (K c)‖)

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKPaCountingSourceAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
