import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKBoundaryNextActualSourceDelta.Update.Source

import H0mework.Versions.V2.Arithmetic.RiemannNativeCurrent.ProjectedSourcePhysical
import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKBoundarySourceAction.Consumer
import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.CanonicalRaw.BoundaryTrace.Projection
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKWholePaNativeRankSourceUpdate
open Complex MeasureTheory Set Filter BurnolPhysicalState
open scoped InnerProductSpace Topology
open NoIslandNoMagic.CanonicalRiemann NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
local instance wholePaNativeEffectComplete : CompleteSpace BurnolPaAmbientCarrier := by
  apply IsComplete.completeSpace_coe
  exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete
local notation "P" => burnolEvenAmbientProjection
variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n : Nat, observation.coordinate = -2*(n+1))
variable (half : OriginalKCombCalculation.Half observation)
local notation "c" => OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half


open OriginalKWholePaSourceRankAction

def actualNativePairKernelPriceUpdate (h nextShift : ℝ) : ℂ :=
  OriginalKPairedResponseGramAction.originalPairKernelRead observation nontrivial half
    (actualNonPaNativeRUpdate observation nontrivial half h nextShift)
def actualNativeSiblingKernelPriceUpdate (h nextShift : ℝ) : ℂ :=
  OriginalKPairedResponseGramAction.originalSiblingKernelRead observation nontrivial half
    (actualNonPaNativeRUpdate observation nontrivial half h nextShift)

def actualWholePaPairSourcePrice (h : ℝ) : ℂ :=
  star (actualWholePaSourceCoefficient observation nontrivial half h / 2) *
    actualWholePaUnitPairPrice observation nontrivial half + actualNonPaPairKernelPrice observation nontrivial half h

def actualWholePaSiblingSourcePrice (h : ℝ) : ℂ :=
  (actualWholePaSourceCoefficient observation nontrivial half h / 2) *
    actualWholePaUnitSiblingPrice observation nontrivial half + actualNonPaSiblingKernelPrice observation nontrivial half h

def actualWholePaPairSourcePriceUpdate (h nextShift : ℝ) : ℂ :=
  star (actualNativeSourceCoefficientUpdate observation nontrivial half h nextShift / 2) *
    actualWholePaUnitPairPrice observation nontrivial half + actualNativePairKernelPriceUpdate observation nontrivial half h nextShift

def actualWholePaSiblingSourcePriceUpdate (h nextShift : ℝ) : ℂ :=
  (actualNativeSourceCoefficientUpdate observation nontrivial half h nextShift / 2) *
    actualWholePaUnitSiblingPrice observation nontrivial half + actualNativeSiblingKernelPriceUpdate observation nontrivial half h nextShift

/-- The original paired/sibling kernel readers consume the source-generated nonPa R increment in its original conjugate-linear/linear directions. -/
theorem actual_native_nonPa_kernel_read_update (h nextShift : ℝ) (nonnegative : 0 ≤ h) (ordered : h ≤ nextShift) :
    actualNonPaPairKernelPrice observation nontrivial half nextShift - actualNonPaPairKernelPrice observation nontrivial half h =
      actualNativePairKernelPriceUpdate observation nontrivial half h nextShift ∧
    actualNonPaSiblingKernelPrice observation nontrivial half nextShift - actualNonPaSiblingKernelPrice observation nontrivial half h =
      actualNativeSiblingKernelPriceUpdate observation nontrivial half h nextShift := by
  have source := (actual_native_rank_R_source_update observation nontrivial half h nextShift nonnegative ordered).2
  have pair : OriginalKCombCofinalPaAction.paired (actualNonPaR observation nontrivial half nextShift - actualNonPaR observation nontrivial half h) =
      OriginalKCombCofinalPaAction.paired (actualNonPaR observation nontrivial half nextShift) -
      OriginalKCombCofinalPaAction.paired (actualNonPaR observation nontrivial half h) := by
    unfold OriginalKCombCofinalPaAction.paired
    rw [map_sub]
    module
  have sibling : OriginalKCombCofinalPaAction.sibling (actualNonPaR observation nontrivial half nextShift - actualNonPaR observation nontrivial half h) =
      OriginalKCombCofinalPaAction.sibling (actualNonPaR observation nontrivial half nextShift) -
      OriginalKCombCofinalPaAction.sibling (actualNonPaR observation nontrivial half h) := by
    unfold OriginalKCombCofinalPaAction.sibling
    rw [map_sub]
    module
  unfold actualNonPaPairKernelPrice actualNonPaSiblingKernelPrice actualNativePairKernelPriceUpdate actualNativeSiblingKernelPriceUpdate
    OriginalKPairedResponseGramAction.originalPairKernelRead OriginalKPairedResponseGramAction.originalSiblingKernelRead
  rw [←source,pair,sibling]
  simp only [map_sub,inner_sub_left,inner_sub_right]
  exact ⟨trivial,trivial⟩

/-- Both complete price changes are generated by the source coefficient/R action; no desired character difference enters the programme. -/
theorem actual_native_whole_Pa_price_update (h nextShift : ℝ) (nonnegative : 0 ≤ h) (ordered : h ≤ nextShift) :
    actualWholePaPairSourcePrice observation nontrivial half nextShift - actualWholePaPairSourcePrice observation nontrivial half h =
      actualWholePaPairSourcePriceUpdate observation nontrivial half h nextShift ∧
    actualWholePaSiblingSourcePrice observation nontrivial half nextShift - actualWholePaSiblingSourcePrice observation nontrivial half h =
      actualWholePaSiblingSourcePriceUpdate observation nontrivial half h nextShift := by
  have rank := (actual_native_rank_R_source_update observation nontrivial half h nextShift nonnegative ordered).1
  have reader := actual_native_nonPa_kernel_read_update observation nontrivial half h nextShift nonnegative ordered
  unfold actualWholePaPairSourcePrice actualWholePaSiblingSourcePrice actualWholePaPairSourcePriceUpdate actualWholePaSiblingSourcePriceUpdate
  rw [←rank,←reader.1,←reader.2]
  simp only [sub_div,star_sub]
  constructor <;> ring

def actualWholePaRankSourceCharacterUpdate (h nextShift : ℝ) : ℂ :=
  (actualOriginalCrossFactor observation nextShift-actualOriginalCrossFactor observation h) *
    actualWholePaPairSourcePrice observation nontrivial half h +
  actualOriginalCrossFactor observation nextShift * actualWholePaPairSourcePriceUpdate observation nontrivial half h nextShift +
  star (actualOriginalCrossFactor observation nextShift-actualOriginalCrossFactor observation h) *
    actualWholePaSiblingSourcePrice observation nontrivial half h +
  star (actualOriginalCrossFactor observation nextShift) * actualWholePaSiblingSourcePriceUpdate observation nontrivial half h nextShift

/-- The two-source price effect generates the literal original rank-character increment before the independent target readout. -/
theorem actual_native_rank_character_update (h nextShift : ℝ) (nonnegative : 0 ≤ h) (ordered : h ≤ nextShift) :
    actualWholePaRankSourceCharacter observation nontrivial half nextShift - actualWholePaRankSourceCharacter observation nontrivial half h =
      actualWholePaRankSourceCharacterUpdate observation nontrivial half h nextShift := by
  have price := actual_native_whole_Pa_price_update observation nontrivial half h nextShift nonnegative ordered
  unfold actualWholePaRankSourceCharacter actualWholePaRankSourceCharacterUpdate
  change actualOriginalCrossFactor observation nextShift * actualWholePaPairSourcePrice observation nontrivial half nextShift +
      star (actualOriginalCrossFactor observation nextShift) * actualWholePaSiblingSourcePrice observation nontrivial half nextShift -
      (actualOriginalCrossFactor observation h * actualWholePaPairSourcePrice observation nontrivial half h +
        star (actualOriginalCrossFactor observation h) * actualWholePaSiblingSourcePrice observation nontrivial half h) = _
  rw [←price.1,←price.2,star_sub]
  ring

/-- The independent original Cross reads this same generated source update; it does not provide the effect as an input. -/
theorem actual_original_cross_consumes_native_rank_update (h nextShift : ℝ) (nonnegative : 0 ≤ h) (ordered : h ≤ nextShift) :
    OriginalKPairedResponseGramAction.originalKernelCross observation nontrivial half nextShift -
      OriginalKPairedResponseGramAction.originalKernelCross observation nontrivial half h =
      actualWholePaRankSourceCharacterUpdate observation nontrivial half h nextShift := by
  rw [actual_original_cross_consumes_whole_Pa_rank_source,actual_original_cross_consumes_whole_Pa_rank_source]
  exact actual_native_rank_character_update observation nontrivial half h nextShift nonnegative ordered

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKWholePaNativeRankSourceUpdate
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
