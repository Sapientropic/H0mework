import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKPaCountingSourceAction.Source
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
local instance paCountingRealizationComplete : CompleteSpace BurnolPaAmbientCarrier :=by
 apply IsComplete.completeSpace_coe
 exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete


local notation "q" => (1/4:ℝ)
local notation "reciprocal" => burnolUnitReciprocalPrimitiveL2

def actualReciprocalActor (c:BurnolCompletedMellinCoordinate) (u:ℝ):BurnolL2:=
 burnolUnitTailSlope c u • burnolSourceScalePrimitive reciprocal u

def actualFiniteReciprocalUnitSource (c:BurnolCompletedMellinCoordinate) (lower:ℝ):BurnolL2:=
 burnolUnitPowerWeight c q • burnolSourceScalePrimitive reciprocal q-
 ∫ u:ℝ in lower..q,actualReciprocalActor c u

/-- The finite actual counting and reciprocal programmes retain their same source realization, rather than recognizing independent target values. -/
theorem actual_finite_counting_reciprocal_source_realization (c:BurnolCompletedMellinCoordinate)
 (lower:ℝ) (nonnegative:0≤lower) (bounded:lower≤q) (test:SchwartzMap ℝ ℂ):
 burnolRemainderSourceRead (actualFiniteReciprocalUnitSource c lower) test=
 (Lp.toTemperedDistributionCLM ℂ volume 2 (actualFiniteCountingUnitSource c lower)) test :=by
 have containment:Set.Ioc lower q⊆Set.Ioc 0 q:=by
  intro u inside
  exact ⟨nonnegative.trans_lt inside.1,inside.2⟩
 have reciprocalIntegrable:IntegrableOn (actualReciprocalActor c) (Set.Ioc lower q):=
  (burnolUnitTailSlope_integrable c reciprocal q).mono_set containment
 have countingIntegrable:IntegrableOn (actualCountingActor c) (Set.Ioc lower q):=
  (burnolUnitTailSlope_integrable c burnolUnitCountingPrimitiveL2 q).mono_set containment
 have field:∀ᵐ u∂volume.restrict (Set.Ioc lower q),∀ ψ:SchwartzMap ℝ ℂ,
  burnolRemainderSourceRead (actualReciprocalActor c u) ψ=
  (Lp.toTemperedDistributionCLM ℂ volume 2 (actualCountingActor c u)) ψ :=by
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with u inside
  intro ψ
  unfold actualReciprocalActor actualCountingActor
  rw [←burnolRemainderSourceReadCLM_apply,map_smul,burnolRemainderSourceReadCLM_apply,
   burnolSourceScalePrimitive_realizes u (nonnegative.trans_lt inside.1) (by linarith [inside.2])]
  simp only [map_smul,smul_apply,smul_eq_mul]
 have integrated:=burnolRemainderSourceRead_bochner (volume.restrict (Set.Ioc lower q))
  (actualReciprocalActor c) (actualCountingActor c) reciprocalIntegrable countingIntegrable field test
 unfold actualFiniteReciprocalUnitSource actualFiniteCountingUnitSource
 rw [intervalIntegral.integral_of_le bounded,intervalIntegral.integral_of_le bounded,
  ←burnolRemainderSourceReadCLM_apply,map_sub,map_smul,burnolRemainderSourceReadCLM_apply,
  burnolSourceScalePrimitive_realizes q (by norm_num) (by norm_num),burnolRemainderSourceReadCLM_apply,integrated]
 simp only [map_sub,map_smul,sub_apply,smul_apply,smul_eq_mul]

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKPaCountingSourceAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
