import Lean
import SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFourierKernelDependentRAction.Edge
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





def actualNativeKernelCoefficient (coordinate : BurnolCompletedMellinCoordinate) : ℂ :=
 -star coordinate.value*OriginalRieszSource.GapEuler.gapMean q coordinate

elab "paidNativeKernelCoefficientQualified" : term => do
 let head := ("_private.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Source.Edge".splitOn ".").foldl Lean.Name.str Lean.Name.anonymous
 let full := ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState.OriginalRieszFiniteSource.coefficient_nonzero".splitOn ".").foldl Lean.Name.str (Lean.Name.num head 0)
 return Lean.mkConst full

theorem actual_native_kernel_coefficient_ne_zero (coordinate : BurnolCompletedMellinCoordinate) :
 actualNativeKernelCoefficient coordinate≠0 := paidNativeKernelCoefficientQualified coordinate

/-- Original source normalization is inverted only with its already-generated coefficient qualification. -/
theorem actual_native_kernel_from_edge (coordinate : BurnolCompletedMellinCoordinate) :
 burnolAmbientEvenPart (burnolAmbientCompletedMellinKernelFormula coordinate)=
 actualNativeKernelCoefficient coordinate • OriginalRieszFiniteSource.edgePrimitive coordinate :=by
 change _=actualNativeKernelCoefficient coordinate •
   (actualNativeKernelCoefficient coordinate)⁻¹ • burnolAmbientEvenPart (burnolAmbientCompletedMellinKernelFormula coordinate)
 rw [smul_smul,mul_inv_cancel₀ (actual_native_kernel_coefficient_ne_zero coordinate),one_smul]

def actualResonantNativeKernelField (coordinate : BurnolCompletedMellinCoordinate) : BurnolL2 :=
 let dual:=OriginalKQuarterTailPhysicalSource.actualStarSource coordinate
 actualNativeKernelCoefficient coordinate •
 ((-(dual.value-1)/2:ℂ) • actualResonantField (dual.value/2) Whole.seed-
 Whole.actualWholeSeedRField dual)

/-- Whole original ambient source enters actual R before any physical price, with the full Jordan source and exterior retained. -/
theorem actual_native_kernel_resonant_R (coordinate : BurnolCompletedMellinCoordinate) :
 let dual:=OriginalKQuarterTailPhysicalSource.actualStarSource coordinate
 burnolDirectRightResolvent (dual.value/2)
   (burnolAmbientEvenPart (burnolAmbientCompletedMellinKernelFormula coordinate))=
 actualResonantNativeKernelField coordinate :=by
 dsimp only
 rw [actual_native_kernel_from_edge,burnolDirectRightResolvent_smul,actual_resonant_edge_whole_field]
 rfl

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKFourierKernelDependentRAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
