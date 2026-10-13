import Lean
import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCompactAdjointRSource.Rank
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCompactAdjointRSource
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



def actualCompactTailCoefficient (coordinate : BurnolCompletedMellinCoordinate) (source : BurnolL2) : ℂ :=
 2*burnolRadiusMellinTailEvaluator 4 (by norm_num) coordinate.value coordinate.rightHalf
   (burnolTateReciprocalL2 source)

/-- The actual compact source rank and already-paid explicit tail FTC generate the complete quarter response law. -/
theorem actual_compact_quarter_mean_action (coordinate : BurnolCompletedMellinCoordinate) (material : BurnolL2)
 (compact : originalPhysicalCutoff q material=material) (even : reflectL2 material=material) :
 (coordinate.value/2-1/2)*Paid.actualMean (burnolDirectRightResolvent (coordinate.value/2) material)=
 actualCompactTailCoefficient coordinate material*(((2*q:ℝ):ℂ)*(q:ℂ)^(-coordinate.value))-
 Paid.actualMean material := by
 let acted:=burnolDirectRightResolvent (coordinate.value/2) material
 let inside:=originalPhysicalCutoff q acted
 let coefficient:=actualCompactTailCoefficient coordinate material
 have supported : originalPhysicalCutoff q inside=inside := by
  unfold inside originalPhysicalCutoff
  rw [burnolRadiusRestriction_zeroExtension]
 have decomposition : acted=inside+coefficient • burnolRadiusNormalizedUnitTail coordinate q (by norm_num) :=
  actual_compact_R_rank_source coordinate material compact even
 have mean : Paid.actualMean acted=Paid.actualMean inside := by
  have source:=congrArg Paid.actualMean decomposition
  rw [map_add,map_smul,OriginalKPositionQuarterFTCAction.actual_tail_quarter_mean coordinate q (by norm_num) le_rfl,
    intervalIntegral.integral_same,mul_zero,smul_zero,add_zero] at source
  exact source
 have compactDerivative : HasDerivAt (fun time : ℝ=>(Real.exp (time/4):ℂ)*Paid.actualMean inside)
   ((1/4:ℂ)*Paid.actualMean inside) 0 := by
  have source:=((hasDerivAt_id (0:ℝ)).div_const 4).exp
  have complex:=Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt 0 source
  have generated:=complex.mul_const (Paid.actualMean inside)
  convert! generated using 1
  norm_num
 have sourceDerivative : HasDerivWithinAt (fun time : ℝ=>Paid.actualMean
   (burnolMultiplicativeDilation (-time/2) acted))
   ((1/4:ℂ)*Paid.actualMean inside+coefficient*(((2*q:ℝ):ℂ)*(q:ℂ)^(-coordinate.value))) (Iic 0) 0 := by
  apply (compactDerivative.hasDerivWithinAt.add
    (HasDerivWithinAt.const_mul coefficient (OriginalKPositionQuarterFTCAction.actual_tail_quarter_mean_derivative coordinate))).congr_of_mem
  · intro time nonpositive
    have source:=congrArg (fun material : BurnolL2=>Paid.actualMean (burnolMultiplicativeDilation (-time/2) material)) decomposition
    simp only [map_add,map_smul,smul_eq_mul] at source
    rw [OriginalKPositionQuarterFTCAction.actual_compact_positive_mean inside supported (-time/2) (by change time≤0 at nonpositive;linarith)] at source
    rw [show -(-time/2)/2=time/4 by ring] at source
    exact source
  · exact self_mem_Iic

 have right : 1/4<(coordinate.value/2).re := by
  rw [Complex.div_re];norm_num;linarith [coordinate.rightHalf]
 have strong:=(OriginalKPositionQuarterFTCAction.actual_R_mean_orbit (coordinate.value/2) right material).hasDerivWithinAt (s:=Iic 0)
 have equation:=(uniqueDiffWithinAt_Iic (0:ℝ)).eq_deriv (Iic 0) sourceDerivative strong
 rw [←mean] at equation
 change (1/4:ℂ)*Paid.actualMean acted+coefficient*(((2*q:ℝ):ℂ)*(q:ℂ)^(-coordinate.value))=
   (coordinate.value/2-1/4)*Paid.actualMean acted+Paid.actualMean material at equation
 linear_combination -equation

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCompactAdjointRSource
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
