import H0mework.Versions.Y.Arithmetic.RieszCanonicalRaw.RieszDilationRaw
import H0mework.Versions.Y.Arithmetic.RieszCanonicalRaw.EvenProjectionCanonicalRaw

/-!
# Canonical paired boundary raw

The projection uses the actual Sonine block.  Its constant-gap value comes from
the same physical boundary; fixing that value pointwise preserves the proven
almost-everywhere read and makes centred divisor reconstruction locally finite.
-/

set_option autoImplicit false
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
open Complex MeasureTheory Set
noncomputable section

local instance boundaryRawAmbientComplete : CompleteSpace BurnolPaAmbientCarrier := by
  apply IsComplete.completeSpace_coe
  exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete

private theorem pairedProjection_eq (shift : ℝ) (value : BurnolPaAmbientCarrier) :
    burnolEvenAmbientProjection (pairedBurnolMultiplicativeDilation shift (value : BurnolL2)) =
      burnolPairedAmbientCompression shift value := by
  unfold pairedBurnolMultiplicativeDilation burnolPairedAmbientCompression
  simp only [smul_apply, add_apply, map_smul, map_add]
  rfl

def burnolPairedBoundaryUnclampedRaw (coordinate : BurnolCompletedMellinCoordinate)
    (shift x : ℝ) : ℂ :=
  pairedMellinTranslationCharacter coordinate.value shift * burnolRieszStateRaw coordinate x -
    burnolEvenProjectionRaw
      (pairedBurnolMultiplicativeDilation shift (burnolCompletedMellinRieszVector coordinate : BurnolL2))
      (burnolRieszPairedDilationRaw coordinate shift) x

theorem burnolPairedBoundary_ae_unclampedRaw
    (coordinate : BurnolCompletedMellinCoordinate) (zero : riemannZeta coordinate.value = 0)
    (shift : ℝ) :
    ((burnolZeroPairedFixedAnnulusBoundary coordinate zero shift : BurnolPaAmbientCarrier) :
      ℝ → ℂ) =ᵐ[volume] burnolPairedBoundaryUnclampedRaw coordinate shift := by
  let action := pairedBurnolMultiplicativeDilation shift
    (burnolCompletedMellinRieszVector coordinate : BurnolL2)
  let projected := burnolPairedAmbientCompression shift (burnolCompletedMellinRieszVector coordinate)
  let c := pairedMellinTranslationCharacter coordinate.value shift
  have projectionRead : ((projected : BurnolL2) : ℝ → ℂ) =ᵐ[volume]
      burnolEvenProjectionRaw action (burnolRieszPairedDilationRaw coordinate shift) := by
    have generated := burnolEvenProjection_ae_raw action
      (burnolRieszPairedDilationRaw coordinate shift) (burnolRieszPairedDilation_ae_raw coordinate shift)
    change ((burnolEvenAmbientProjection action : BurnolL2) : ℝ → ℂ) =ᵐ[volume] _ at generated
    rw [show burnolEvenAmbientProjection action = projected by
      exact pairedProjection_eq shift (burnolCompletedMellinRieszVector coordinate)] at generated
    exact generated
  change (((c • (burnolCompletedMellinRieszVector coordinate : BurnolL2)) -
    (projected : BurnolL2) : BurnolL2) : ℝ → ℂ) =ᵐ[volume] _
  filter_upwards [Lp.coeFn_sub
      (c • (burnolCompletedMellinRieszVector coordinate : BurnolL2)) (projected : BurnolL2),
    Lp.coeFn_smul c (burnolCompletedMellinRieszVector coordinate : BurnolL2),
    burnolRieszState_ae_raw coordinate, projectionRead] with x subRead scaled kernel projection
  rw [subRead]
  change (c • (burnolCompletedMellinRieszVector coordinate : BurnolL2) : BurnolL2) x -
    (projected : BurnolL2) x = _
  rw [scaled]
  change c * (burnolCompletedMellinRieszVector coordinate : BurnolL2) x - (projected : BurnolL2) x = _
  rw [kernel, projection]
  rfl

def burnolPairedBoundaryGapConstant (coordinate : BurnolCompletedMellinCoordinate)
    (zero : riemannZeta coordinate.value = 0) (shift : ℝ) : ℂ :=
  burnolConstantGapCoefficient burnolUnscaledCommonGapRadius
    (burnolZeroPairedFixedAnnulusBoundary coordinate zero shift)

def burnolPairedBoundaryRaw (coordinate : BurnolCompletedMellinCoordinate)
    (zero : riemannZeta coordinate.value = 0) (shift x : ℝ) : ℂ :=
  if |x| ≤ (1 / 4 : ℝ) then burnolPairedBoundaryGapConstant coordinate zero shift
  else burnolPairedBoundaryUnclampedRaw coordinate shift x

theorem burnolPairedBoundaryRaw_quarterGap
    (coordinate : BurnolCompletedMellinCoordinate) (zero : riemannZeta coordinate.value = 0)
    (shift x : ℝ) (inside : |x| ≤ (1 / 4 : ℝ)) :
    burnolPairedBoundaryRaw coordinate zero shift x = burnolPairedBoundaryRaw coordinate zero shift 0 := by
  simp only [burnolPairedBoundaryRaw, inside, if_true, abs_zero,
    show (0 : ℝ) ≤ 1 / 4 by norm_num]

private theorem physicalGap_ae (value : BurnolPaAmbientCarrier) :
    ∀ᵐ x : ℝ ∂volume, x ∈ symmetricInterval (1 / 4 : ℝ) →
      (value : BurnolL2) x = burnolConstantGapCoefficient burnolUnscaledCommonGapRadius value := by
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp value.property.1.1
  change c • intervalConstant burnolUnscaledCommonGapRadius =
    restrictToInterval burnolUnscaledCommonGapRadius (value : BurnolL2) at hc
  have coefficient := burnolConstantGapCoefficient_eq burnolUnscaledCommonGapRadius
    (by norm_num [burnolUnscaledCommonGapRadius]) value c hc
  rw [coefficient]
  have restricted : (restrictToInterval burnolUnscaledCommonGapRadius (value : BurnolL2) : ℝ → ℂ) =ᵐ[
      volume.restrict (symmetricInterval burnolUnscaledCommonGapRadius)] fun _ => c := by
    rw [← hc]
    filter_upwards [Lp.coeFn_smul c (intervalConstant burnolUnscaledCommonGapRadius),
      intervalConstant_coeFn burnolUnscaledCommonGapRadius] with x scaled constant
    rw [scaled]
    change c * intervalConstant burnolUnscaledCommonGapRadius x = _
    rw [constant, mul_one]
  have actual := (LpToLpRestrictCLM_coeFn ℂ (symmetricInterval burnolUnscaledCommonGapRadius)
    (value : BurnolL2)).symm.trans restricted
  exact (ae_restrict_iff' (measurableSet_symmetricInterval burnolUnscaledCommonGapRadius)).mp actual

theorem burnolPairedBoundary_ae_raw
    (coordinate : BurnolCompletedMellinCoordinate) (zero : riemannZeta coordinate.value = 0)
    (shift : ℝ) :
    ((burnolZeroPairedFixedAnnulusBoundary coordinate zero shift : BurnolPaAmbientCarrier) :
      ℝ → ℂ) =ᵐ[volume] burnolPairedBoundaryRaw coordinate zero shift := by
  filter_upwards [burnolPairedBoundary_ae_unclampedRaw coordinate zero shift,
    physicalGap_ae (burnolZeroPairedFixedAnnulusBoundary coordinate zero shift)] with x raw gap
  by_cases inside : |x| ≤ (1 / 4 : ℝ)
  · rw [burnolPairedBoundaryRaw, if_pos inside]
    apply gap
    simpa only [symmetricInterval, mem_Icc, abs_le] using inside
  · rw [burnolPairedBoundaryRaw, if_neg inside]
    exact raw

end
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
