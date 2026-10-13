import Lean
import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFourierKernelDependentRAction.Boundary
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKFourierKernelDependentRAction
open Complex MeasureTheory Set Filter SourceGeneratedHilbertCokernel
open scoped InnerProductSpace Topology
open NoIslandNoMagic.CanonicalRiemann NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
open BurnolPhysicalState OriginalPaPhysicalGreen
namespace Paid
export _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState.FiniteMobiusResolventFlux (actualMean Rplus RplusIntegrand Rplus_integrable)
export _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState.OriginalJointFluxSource (actual_mean_source_integral actual_mean_dilation_source source_weight_mean_phase)
end Paid
local notation "q" => (1/4:ℝ)

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n:Nat,observation.coordinate=-2*(n+1))
variable (half : OriginalKCombCalculation.Half observation)





/-- The actual weighted source boundary emits the strong Jordan successor, with no derivative or cancellation target input. -/
theorem actual_resonant_source_strong (z : ℂ) (right : 1/4<z.re) (source : BurnolL2) :
 HasDerivAt (fun shift : ℝ=>burnolMultiplicativeDilation (-shift/2) (actualResonantField z source))
  ((z-1/4) • actualResonantField z source+burnolDirectRightResolvent z source) 0 := by
 have weightedContinuous : Continuous (actualResonantIntegrand z source) :=by
  unfold actualResonantIntegrand burnolDirectRightResolventIntegrand
  exact continuous_id.smul ((positiveMellinQuarterRightResolventWeight_continuous z).smul
    ((burnolMultiplicativeDilation_stronglyContinuous source).comp (by fun_prop)))
 have boundary:=intervalIntegral.integral_hasDerivAt_right
   (weightedContinuous.intervalIntegrable 0 0) weightedContinuous.stronglyMeasurable.stronglyMeasurableAtFilter
   weightedContinuous.continuousAt
 have boundaryZero : HasDerivAt
   (fun shift : ℝ=>∫ time : ℝ in (0:ℝ)..shift,actualResonantIntegrand z source time) (0:BurnolL2) 0 :=by
  convert! boundary using 1
  simp [actualResonantIntegrand]
 have realScalar : HasDerivAt (fun shift:ℝ=>shift) 1 0:=hasDerivAt_id 0
 have first:=(hasDerivAt_const (0:ℝ) (actualResonantField z source)).add
   (realScalar.smul_const (burnolDirectRightResolvent z source))
 have stock:=first.sub boundaryZero
 have ordinary:=burnolDirectRightResolventSignedBoundary_hasDerivAt z source
 have last:=realScalar.smul ordinary
 have inside:=stock.add last
 have complexInside : HasDerivAt
   (fun shift:ℝ=>actualResonantField z source+shift • burnolDirectRightResolvent z source-
      (∫ time:ℝ in (0:ℝ)..shift,actualResonantIntegrand z source time)+
      shift • burnolDirectRightResolventSignedBoundary z source shift)
   (burnolDirectRightResolvent z source) 0:=by
  convert! inside using 1
  simp [burnolDirectRightResolventSignedBoundary]
 have generated:=(positiveMellinQuarterRightResolventCharacter_hasDerivAt z).smul complexInside
 have zeroCharacter : positiveMellinQuarterRightResolventCharacter z 0=1 :=by
  rw [positiveMellinQuarterRightResolventCharacter_exp]
  simp
 simp only [zero_smul,add_zero,sub_zero,one_smul,zeroCharacter,intervalIntegral.integral_same] at generated
 have same : (fun shift:ℝ=>burnolMultiplicativeDilation (-shift/2) (actualResonantField z source))=
  fun shift:ℝ=>positiveMellinQuarterRightResolventCharacter z shift •
    (actualResonantField z source+shift • burnolDirectRightResolvent z source-
      (∫ time:ℝ in (0:ℝ)..shift,actualResonantIntegrand z source time)+
      shift • burnolDirectRightResolventSignedBoundary z source shift) :=by
  funext shift
  exact actual_resonant_source_boundary z right source shift
 rw [same]
 convert! generated using 1
 module

/-- Existing source strong uniqueness identifies the generated weighted orbit as the actual same-parameter repeated R action. -/
theorem actual_resonant_repeated_R (z : ℂ) (right : 1/4<z.re) (source : BurnolL2) :
 burnolDirectRightResolvent z (burnolDirectRightResolvent z source)=actualResonantField z source :=
 (burnolDirectRightResolvent_of_strongEquation z right _ _ (actual_resonant_source_strong z right source)).symm

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKFourierKernelDependentRAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
