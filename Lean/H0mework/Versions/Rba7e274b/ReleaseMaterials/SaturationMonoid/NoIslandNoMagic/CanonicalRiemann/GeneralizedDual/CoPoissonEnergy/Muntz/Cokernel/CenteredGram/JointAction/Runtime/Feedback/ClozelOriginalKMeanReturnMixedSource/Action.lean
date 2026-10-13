import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKQuarterTailPhysicalSource.Consumer
import H0mework.Versions.V2.Arithmetic.RiemannNativeCurrent.UnitResponseRadius
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKMeanReturnMixedSource
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

/-- The existing corrected source strong action and original R action are consumed on the actual material. -/
theorem actual_K_material_R_source_action (material : BurnolL2) :
 let coordinate:=OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half
 let k:=(burnolCompletedMellinRieszVector coordinate : BurnolL2)
 let contact:=OriginalKSourceBalance.contactCorrection coordinate
 let regular:=OriginalKSourceBalance.regularSource coordinate
 let r:=OriginalKFullSourceRResponse.Op.R observation nontrivial half
 (coordinate.value-1/2)*inner ℂ k (r material)=
 -inner ℂ (k+contact) material-(coordinate.value-1/2)*inner ℂ contact (r material)+
 (1/2:ℂ)*inner ℂ regular (r material) := by
 dsimp only
 have source:=OriginalKSourceBalance.source_R_originalK_equation observation nontrivial half material
 change (2*(OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half).value-1)*
   inner ℂ (burnolCompletedMellinRieszVector (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) : BurnolL2)
     (OriginalKFullSourceRResponse.Op.R observation nontrivial half material)+
   2*inner ℂ (burnolCompletedMellinRieszVector (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) : BurnolL2) material=
   inner ℂ (OriginalKSourceBalance.regularSource (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half))
     (OriginalKFullSourceRResponse.Op.R observation nontrivial half material)-
   ((2*(OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half).value-1)*
    inner ℂ (OriginalKSourceBalance.contactCorrection (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half))
      (OriginalKFullSourceRResponse.Op.R observation nontrivial half material)+
    2*inner ℂ (OriginalKSourceBalance.contactCorrection (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half)) material) at source
 rw [inner_add_left]
 linear_combination (1/2:ℂ)*source


end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKMeanReturnMixedSource
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
