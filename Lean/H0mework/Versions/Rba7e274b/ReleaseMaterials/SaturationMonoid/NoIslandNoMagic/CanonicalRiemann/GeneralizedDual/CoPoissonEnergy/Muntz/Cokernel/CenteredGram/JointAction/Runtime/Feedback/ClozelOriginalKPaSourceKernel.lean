import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKAmbientPricing
import H0mework.Realization.Operations.Action
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Source.ModifiedWeakFE.Localization.Physical.Division.SourceRealization.Complete.First.Generator.Resolvent.Fourier
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCombCofinalPaAction
section
open Complex MeasureTheory Set Filter
open NoIslandNoMagic.CanonicalRiemann NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
open NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
open scoped InnerProductSpace Topology

local instance physicalComplete : CompleteSpace BurnolPaAmbientCarrier := by
 apply IsComplete.completeSpace_coe
 exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete

def E : BurnolL2 →L[ℂ] BurnolPaAmbientCarrier :=
 burnolCompactCoPoissonClosedRange.toSubmodule.starProjection.comp burnolEvenAmbientProjection

theorem wholePa_normal_read (value : BurnolL2) (g : BurnolPaAmbientCarrier)
 (inside : g ∈ burnolCompactCoPoissonClosedRange) :
 inner ℂ g (E value) = inner ℂ (g : BurnolL2) value := by
 have pa := burnolCompactCoPoissonClosedRange.toSubmodule.inner_orthogonalProjectionOnto_eq_of_mem_left
  ⟨g, inside⟩ (burnolEvenAmbientProjection value)
 have physical := (evenBurnolClosedFace burnolUnscaledCommonGapRadius).toSubmodule.inner_orthogonalProjectionOnto_eq_of_mem_left g value
 exact pa.trans physical

theorem ambient_R_normal (z : ℂ) (right : 1/4 < z.re) (value : BurnolL2)
 (g : BurnolPaAmbientCarrier) (inside : g ∈ burnolCompactCoPoissonClosedRange) :
 inner ℂ g (E (burnolDirectRightResolvent z value)) =
 -(∫ t : ℝ in Ioi 0, positiveMellinQuarterRightResolventWeight z t *
  inner ℂ (g : BurnolL2) (burnolMultiplicativeDilation (-t/2) value)) := by
 rw [wholePa_normal_read _ g inside]
 have integrable := burnolDirectRightResolventIntegrand_integrableOn z right value
 have mapped := (innerSL ℂ (g : BurnolL2)).integral_comp_comm integrable
 change (∫ t : ℝ in Ioi 0, inner ℂ (g : BurnolL2) (burnolDirectRightResolventIntegrand z value t)) =
  inner ℂ (g : BurnolL2) (∫ t : ℝ in Ioi 0, burnolDirectRightResolventIntegrand z value t) at mapped
 unfold burnolDirectRightResolvent
 rw [inner_neg_right, ← mapped]
 congr 1
 apply setIntegral_congr_fun measurableSet_Ioi
 intro t _
 exact inner_smul_right (𝕜 := ℂ) (E := BurnolL2) _ _ _

end

section
open Complex MeasureTheory Set Filter FourierTransform
open NoIslandNoMagic.CanonicalRiemann NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
open NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
open scoped InnerProductSpace Topology
local instance forcingComplete : CompleteSpace BurnolPaAmbientCarrier := physicalComplete

def Q : BurnolL2 →L[ℂ] BurnolPaAmbientCarrier :=
 burnolCompactCoPoissonClosedRange.toSubmoduleᗮ.starProjection.comp burnolEvenAmbientProjection

def paired (value : BurnolL2) : BurnolL2 := (1/2 : ℂ) • (value+fourierL2 value)
def sibling (value : BurnolL2) : BurnolL2 := (1/2 : ℂ) • (value-fourierL2 value)

theorem ambient_R_paired_equations (z : ℂ) (right : 1/4 < z.re) (value : BurnolL2) :
 HasDerivAt (fun h : ℝ => burnolMultiplicativeDilation (-h/2) (paired (burnolDirectRightResolvent z value)))
  ((z-1/4) • sibling (burnolDirectRightResolvent z value) + (1/2 : ℂ) • (value-fourierL2 value)) 0 ∧
 HasDerivAt (fun h : ℝ => burnolMultiplicativeDilation (-h/2) (sibling (burnolDirectRightResolvent z value)))
  ((z-1/4) • paired (burnolDirectRightResolvent z value) + (1/2 : ℂ) • (value+fourierL2 value)) 0 := by
 have forward := burnolDirectRightResolventOrbit_hasDerivAt z right value
 have reverse := burnolFourierOrbit_hasDerivAt _ _ forward
 simp only [map_add, map_smul] at reverse
 constructor
 · have generated := (forward.add reverse).const_smul (1/2 : ℂ)
   convert! generated using 1
   · funext h
     unfold paired
     rw [map_smul, map_add]
     rfl
   · unfold sibling
     module
 · have generated := (forward.sub reverse).const_smul (1/2 : ℂ)
   convert! generated using 1
   · funext h
     unfold sibling
     rw [map_smul, map_sub]
     rfl
   · unfold paired
     module

theorem ambient_R_Pa_forcing (z : ℂ) (right : 1/4 < z.re) (value : BurnolL2) :
 HasDerivAt (fun h : ℝ => Q (burnolMultiplicativeDilation (-h/2) (paired (burnolDirectRightResolvent z value))))
  ((z-1/4) • Q (sibling (burnolDirectRightResolvent z value)) + (1/2 : ℂ) • (Q value-Q (fourierL2 value))) 0 ∧
 HasDerivAt (fun h : ℝ => Q (burnolMultiplicativeDilation (-h/2) (sibling (burnolDirectRightResolvent z value))))
  ((z-1/4) • Q (paired (burnolDirectRightResolvent z value)) + (1/2 : ℂ) • (Q value+Q (fourierL2 value))) 0 := by
 have generated := ambient_R_paired_equations z right value
 constructor
 · have mapped := (Q.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0 generated.1
   change HasDerivAt (fun h : ℝ => Q (burnolMultiplicativeDilation (-h/2) (paired (burnolDirectRightResolvent z value))))
    (Q ((z-1/4) • sibling (burnolDirectRightResolvent z value) + (1/2 : ℂ) • (value-fourierL2 value))) 0 at mapped
   simpa only [map_add, map_sub, map_smul] using mapped
 · have mapped := (Q.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0 generated.2
   change HasDerivAt (fun h : ℝ => Q (burnolMultiplicativeDilation (-h/2) (sibling (burnolDirectRightResolvent z value))))
    (Q ((z-1/4) • paired (burnolDirectRightResolvent z value) + (1/2 : ℂ) • (value+fourierL2 value))) 0 at mapped
   simpa only [map_add, map_smul] using mapped

end

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCombCofinalPaAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
