import Lean
import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFourierKernelDependentRAction.Orbit
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





private theorem actual_integral_tail_shift (integrand : ℝ→BurnolL2) (shift : ℝ) :
 (∫ time : ℝ in Ioi 0,integrand (time+shift))=
   ∫ time : ℝ in Ioi shift,integrand time := by
 have translated := (measurePreserving_add_left (volume : Measure ℝ) shift).integral_comp
   (Homeomorph.addLeft shift).measurableEmbedding ((Ioi shift).indicator integrand)
 rw [integral_indicator measurableSet_Ioi] at translated
 calc
  _=∫ time : ℝ,(Ioi shift).indicator integrand (shift+time) :=by
   rw [←integral_indicator measurableSet_Ioi]
   apply integral_congr_ae
   filter_upwards with time
   by_cases positive : 0<time
   · have shifted : shift<shift+time:=by linarith
     simp [positive,shifted,add_comm]
   · have shifted : ¬shift<shift+time:=by linarith
     simp [positive,shifted]
  _=_:=translated

private theorem actual_resonant_finite_split (z : ℂ) (right : 1/4<z.re)
 (source : BurnolL2) (shift : ℝ) :
 (∫ time : ℝ in Ioi shift,actualResonantIntegrand z source time)=
 actualResonantField z source-(∫ time : ℝ in (0:ℝ)..shift,actualResonantIntegrand z source time) := by
 have continuous : Continuous (actualResonantIntegrand z source) :=by
  unfold actualResonantIntegrand burnolDirectRightResolventIntegrand
  exact continuous_id.smul ((positiveMellinQuarterRightResolventWeight_continuous z).smul
   ((burnolMultiplicativeDilation_stronglyContinuous source).comp (by fun_prop)))
 have generated:=intervalIntegral.integral_interval_add_Ioi'
   (continuous.intervalIntegrable shift 0) (actual_resonant_integrable z right source)
 rw [intervalIntegral.integral_symm] at generated
 unfold actualResonantField
 linear_combination (norm:=module) -generated


private theorem actual_integrable_tail (integrand : ℝ→BurnolL2) (continuous : Continuous integrand)
 (integrable : IntegrableOn integrand (Ioi 0)) (shift : ℝ) : IntegrableOn integrand (Ioi shift) :=by
 by_cases nonnegative : 0≤shift
 · exact integrable.mono_set (Ioi_subset_Ioi nonnegative)
 · have ordered : shift≤0:=by linarith
   rw [←Ioc_union_Ioi_eq_Ioi ordered]
   exact ((intervalIntegrable_iff_integrableOn_Ioc_of_le ordered).mp
     (continuous.intervalIntegrable shift 0)).union integrable

private theorem actual_integrable_tail_shift (integrand : ℝ→BurnolL2) (shift : ℝ)
 (integrable : IntegrableOn integrand (Ioi shift)) :
 IntegrableOn (fun time:ℝ=>integrand (time+shift)) (Ioi 0) :=by
 have indicator:=integrable.integrable_indicator measurableSet_Ioi
 have moved:=(measurePreserving_add_left (volume : Measure ℝ) shift).integrable_comp_emb
   (Homeomorph.addLeft shift).measurableEmbedding |>.mpr indicator
 apply (integrable_indicator_iff measurableSet_Ioi).mp
 apply moved.congr
 filter_upwards with time
 by_cases positive : 0<time
 · have shifted : shift<shift+time:=by linarith
   simp [positive,shifted,add_comm]
 · have shifted : ¬shift<shift+time:=by linarith
   simp [positive,shifted]

/-- Finite action emitted by the literal original weighted source orbit, including both finite boundary stocks. -/
theorem actual_resonant_source_boundary (z : ℂ) (right : 1/4<z.re)
 (source : BurnolL2) (shift : ℝ) :
 burnolMultiplicativeDilation (-shift/2) (actualResonantField z source)=
 positiveMellinQuarterRightResolventCharacter z shift •
 (actualResonantField z source+shift • burnolDirectRightResolvent z source-
   (∫ time : ℝ in (0:ℝ)..shift,actualResonantIntegrand z source time)+
   shift • burnolDirectRightResolventSignedBoundary z source shift) := by
 let I:=burnolDirectRightResolventIntegrand z source
 let C:=positiveMellinQuarterRightResolventCharacter z shift
 have action (time : ℝ) :
  burnolMultiplicativeDilation (-shift/2) (actualResonantIntegrand z source time)=
  C • ((time+shift) • I (time+shift)-shift • I (time+shift)) := by
  unfold actualResonantIntegrand
  rw [←algebraMap_smul ℂ time,map_smul]
  have moved : burnolMultiplicativeDilation (-shift/2) (I time)=C • I (time+shift) :=by
   dsimp only [I,C]
   unfold burnolDirectRightResolventIntegrand
   rw [map_smul,burnolMultiplicativeDilation_add]
   rw [show -shift/2+-time/2=-(time+shift)/2 by ring]
   rw [smul_smul]
   exact congrArg (fun scalar : ℂ=>scalar • burnolMultiplicativeDilation (-(time+shift)/2) source)
     (positiveMellinQuarterRightResolventCharacter_mul_weight_add z time shift).symm
  rw [moved]
  rw [algebraMap_smul]
  module

 have weightedContinuous : Continuous (actualResonantIntegrand z source) :=by
  unfold actualResonantIntegrand burnolDirectRightResolventIntegrand
  exact continuous_id.smul ((positiveMellinQuarterRightResolventWeight_continuous z).smul
    ((burnolMultiplicativeDilation_stronglyContinuous source).comp (by fun_prop)))
 have ordinaryContinuous : Continuous I :=by
  dsimp only [I]
  exact (positiveMellinQuarterRightResolventWeight_continuous z).smul
    ((burnolMultiplicativeDilation_stronglyContinuous source).comp (by fun_prop))
 have weightedShift:=actual_integrable_tail_shift _ shift
   (actual_integrable_tail _ weightedContinuous (actual_resonant_integrable z right source) shift)
 have ordinaryShift:=actual_integrable_tail_shift _ shift
   (actual_integrable_tail _ ordinaryContinuous (burnolDirectRightResolventIntegrand_integrableOn z right source) shift)
 unfold actualResonantField
 have mapped : burnolMultiplicativeDilation (-shift/2)
   (∫ time : ℝ in Ioi 0,actualResonantIntegrand z source time)=
   ∫ time : ℝ in Ioi 0,burnolMultiplicativeDilation (-shift/2) (actualResonantIntegrand z source time) :=
   (LinearIsometry.integral_comp_comm (burnolMultiplicativeDilation (-shift/2)).toLinearIsometry
     (actualResonantIntegrand z source)).symm
 rw [mapped]
 simp_rw [action]
 rw [integral_smul]
 change C • (∫ time : ℝ in Ioi 0,actualResonantIntegrand z source (time+shift)-shift • I (time+shift))=_
 have smulIntegrable : IntegrableOn (fun time:ℝ=>shift • I (time+shift)) (Ioi 0) :=
   ordinaryShift.smul shift
 rw [integral_sub weightedShift smulIntegrable,integral_smul]
 rw [actual_integral_tail_shift,actual_integral_tail_shift,
   actual_resonant_finite_split z right source shift]
 have split:=intervalIntegral.integral_interval_add_Ioi'
   ((show Continuous I from (positiveMellinQuarterRightResolventWeight_continuous z).smul
    ((burnolMultiplicativeDilation_stronglyContinuous source).comp (by fun_prop))).intervalIntegrable shift 0)
   (burnolDirectRightResolventIntegrand_integrableOn z right source)
 rw [intervalIntegral.integral_symm] at split
 change C • _=C • _
 congr 1
 unfold burnolDirectRightResolvent burnolDirectRightResolventSignedBoundary
 dsimp only [I] at split ⊢
 rw [←split]
 unfold actualResonantField
 module

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKFourierKernelDependentRAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
