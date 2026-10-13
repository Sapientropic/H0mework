import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKSeedPhysicalRSource.Source
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKSeedPhysicalRSource
open Complex MeasureTheory Filter FourierTransform
open scoped InnerProductSpace Topology
open NoIslandNoMagic.CanonicalRiemann NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
open BurnolPhysicalState OriginalPaPhysicalGreen
local notation "Fphysical" => evenFaceFourierEquiv burnolUnscaledCommonGapRadius
local notation "K" => burnolCompletedMellinRieszVector
local instance seedPhysicalEffectComplete : CompleteSpace BurnolPaAmbientCarrier :=by
 apply IsComplete.completeSpace_coe
 exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete


local notation "G" => OriginalRieszFiniteSynthesis.gapMeanVector
local notation "U" => OriginalRieszSource.Response.wholeU
local notation "V" => OriginalRieszSource.Response.wholeV
local notation "s" => OriginalKConstantContactSourceAction.ConstantSource.seed

def actualPlusSeedNativeProjectedUpdate (c : BurnolCompletedMellinCoordinate) : BurnolPaAmbientCarrier :=
 (OriginalRieszSource.Kernel.A c-OriginalRieszSource.Kernel.beta c) •
 (-(OriginalKCoupledPhysicalRFieldSource.actualCompactProjectedRField c U+
     OriginalKCoupledPhysicalRFieldSource.actualCompactProjectedRField c V)+
 (1-c.value) • actualNativeSeedProjectedRField c+Fphysical G)+
 (2:ℂ) • OriginalKFourierSectorRGramSource.actualPlusSource c-
 (OriginalRieszSource.Kernel.A c-OriginalRieszSource.Kernel.beta c) • (G+Fphysical G)

def actualMinusSeedNativeProjectedUpdate (c : BurnolCompletedMellinCoordinate) : BurnolPaAmbientCarrier :=
 (OriginalRieszSource.Kernel.A c+OriginalRieszSource.Kernel.beta c) •
 (OriginalKCoupledPhysicalRFieldSource.actualCompactProjectedRField c U-
     OriginalKCoupledPhysicalRFieldSource.actualCompactProjectedRField c V+
 (1-c.value) • actualNativeSeedProjectedRField c-Fphysical G)+
 (2:ℂ) • OriginalKFourierSectorRGramSource.actualMinusSource c-
 (OriginalRieszSource.Kernel.A c+OriginalRieszSource.Kernel.beta c) • (G-Fphysical G)

/-- The two actual coupled source updates consume the complete native seed response, before taking any price. -/
theorem actual_two_seed_native_projected_updates (c : BurnolCompletedMellinCoordinate) :
 OriginalKCoupledPhysicalRFieldSource.actualPlusProjectedUpdate c=actualPlusSeedNativeProjectedUpdate c ∧
 OriginalKCoupledPhysicalRFieldSource.actualMinusProjectedUpdate c=actualMinusSeedNativeProjectedUpdate c :=by
 unfold OriginalKCoupledPhysicalRFieldSource.actualPlusProjectedUpdate OriginalKCoupledPhysicalRFieldSource.actualMinusProjectedUpdate
  OriginalKCoupledPhysicalRFieldSource.actualPlusProjectedForcing OriginalKCoupledPhysicalRFieldSource.actualMinusProjectedForcing
 rw [actual_compact_seed_native_field]
 exact ⟨rfl,rfl⟩

def actualSeedNativeWeightedKField (c : BurnolCompletedMellinCoordinate) : BurnolPaAmbientCarrier :=
 ((star c.value+c.value-1)/2:ℂ) •
 (actualPlusSeedNativeProjectedUpdate c+actualMinusSeedNativeProjectedUpdate c)
def actualSeedNativeWeightedFKField (c : BurnolCompletedMellinCoordinate) : BurnolPaAmbientCarrier :=
 ((star c.value-c.value)/2:ℂ) •
 (actualMinusSeedNativeProjectedUpdate c-actualPlusSeedNativeProjectedUpdate c)

/-- The generated whole response keeps the original kappa, with the paid native seed field in its actual update. -/
theorem actual_two_seed_native_weighted_fields (c : BurnolCompletedMellinCoordinate) :
 OriginalKCoupledPhysicalRFieldSource.actualWeightedKResponseField c=actualSeedNativeWeightedKField c ∧
 OriginalKCoupledPhysicalRFieldSource.actualWeightedFKResponseField c=actualSeedNativeWeightedFKField c :=by
 have updates:=actual_two_seed_native_projected_updates c
 unfold OriginalKCoupledPhysicalRFieldSource.actualWeightedKResponseField OriginalKCoupledPhysicalRFieldSource.actualWeightedFKResponseField
  OriginalKCoupledPhysicalRFieldSource.actualWeightedPlusRField OriginalKCoupledPhysicalRFieldSource.actualWeightedMinusRField
 rw [updates.1,updates.2]
 unfold actualSeedNativeWeightedKField actualSeedNativeWeightedFKField
 constructor <;> module

def actualSeedNativeWholeMField (c : BurnolCompletedMellinCoordinate) (h : ℝ) : BurnolPaAmbientCarrier :=
 OriginalKCoupledPhysicalRFieldSource.actualResponseKappa c • OriginalKCoupledPhysicalRFieldSource.actualProjectedMInputField c h+
 OriginalKFourierSectorRGramSource.actualFirstRWeight c h • actualSeedNativeWeightedKField c+
 OriginalKFourierSectorRGramSource.actualSecondRWeight c h • actualSeedNativeWeightedFKField c

theorem actual_complete_seed_native_M_field (c : BurnolCompletedMellinCoordinate) (h : ℝ) :
 OriginalKCoupledPhysicalRFieldSource.actualWeightedMResponseField c h=actualSeedNativeWholeMField c h :=by
 unfold OriginalKCoupledPhysicalRFieldSource.actualWeightedMResponseField
 rw [(actual_two_seed_native_weighted_fields c).1,(actual_two_seed_native_weighted_fields c).2]
 rfl

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKSeedPhysicalRSource
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
