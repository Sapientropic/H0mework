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
local instance seedPhysicalFeetComplete : CompleteSpace BurnolPaAmbientCarrier :=by
 apply IsComplete.completeSpace_coe
 exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete


namespace Static
export OriginalKStaticKernelSourceGramSource (actualSelfKernelGram actualDualKernelGram actualFourierSelfGram actualFourierDualGram actualCompactKPrice actualCompactFKPrice)
end Static
local notation "G" => OriginalRieszFiniteSynthesis.gapMeanVector
local notation "μ" => FiniteMobiusResolventFlux.actualMean
local notation "s" => OriginalKConstantContactSourceAction.ConstantSource.seed

def actualNativeKSeedPrice (c : BurnolCompletedMellinCoordinate) : ℂ :=
 (-2/(c.value-1))*
 (OriginalKLiteralEdgeMeanSourcePrice.actualEdgeSourceNormalization (OriginalKQuarterTailPhysicalSource.actualStarSource c)*
  Static.actualDualKernelGram c+(1/2)*star (μ (K c:BurnolL2)))
def actualNativeFKSeedPrice (c : BurnolCompletedMellinCoordinate) : ℂ :=
 (-2/(c.value-1))*
 (OriginalKLiteralEdgeMeanSourcePrice.actualEdgeSourceNormalization (OriginalKQuarterTailPhysicalSource.actualStarSource c)*
  Static.actualFourierDualGram c+(1/2)*star (μ (fourierL2 (K c:BurnolL2))))

/-- Both physical feet consume the original source-produced whole seed field and its already-paid dual Gram. -/
theorem actual_native_seed_R_input_prices (c : BurnolCompletedMellinCoordinate) :
 inner ℂ (K c) (actualNativeSeedProjectedRField c)=actualNativeKSeedPrice c ∧
 inner ℂ (Fphysical (K c)) (actualNativeSeedProjectedRField c)=actualNativeFKSeedPrice c :=by
 have Gram:=OriginalKStaticKernelSourceGramSource.actual_original_static_source_Gram_feet c
 have means:=OriginalKStaticKernelSourceGramSource.actual_static_G_FG_input_prices c
 unfold actualNativeSeedProjectedRField
 simp only [inner_smul_right,inner_add_right]
 change _*(_*inner ℂ (K c:BurnolL2) (K (OriginalKQuarterTailPhysicalSource.actualStarSource c):BurnolL2)+_)=_ ∧
  _*(_*inner ℂ (fourierL2 (K c:BurnolL2)) (K (OriginalKQuarterTailPhysicalSource.actualStarSource c):BurnolL2)+_)=_
 rw [Gram.2.1,means.1,means.2.1]
 exact ⟨rfl,rfl⟩

/-- The complete native seed field discharges the actual compact-seed inventory on both original consumer feet. -/
theorem actual_compact_seed_native_prices (c : BurnolCompletedMellinCoordinate) :
 Static.actualCompactKPrice c s=actualNativeKSeedPrice c ∧
 Static.actualCompactFKPrice c s=actualNativeFKSeedPrice c :=by
 have compact:=OriginalKStaticKernelSourceGramSource.actual_compact_static_Gram_prices c s
 have native:=actual_native_seed_R_input_prices c
 rw [actual_compact_seed_native_field] at compact
 exact ⟨compact.1.symm.trans native.1,compact.2.symm.trans native.2⟩

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKSeedPhysicalRSource
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
