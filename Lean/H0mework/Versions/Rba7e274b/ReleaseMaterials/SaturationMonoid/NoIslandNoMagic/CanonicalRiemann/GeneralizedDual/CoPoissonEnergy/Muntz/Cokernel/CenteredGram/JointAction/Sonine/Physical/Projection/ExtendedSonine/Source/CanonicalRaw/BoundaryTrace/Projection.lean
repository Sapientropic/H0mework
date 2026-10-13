import H0mework.Versions.V2.Arithmetic.RieszCanonicalRaw.BoundaryTracePosition

/-! The actual even projection and paired dilation generate the boundary outer trace. -/

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState

open Complex Filter MeasureTheory Set
open scoped ENNReal InnerProductSpace Topology
noncomputable section

def burnolEvenProjectionPositiveOuterRaw
    (value : BurnolL2) (raw : ℝ → ℂ) (x : ℝ) : ℂ :=
  burnolEvenRaw raw x -
    burnolEvenRaw
      (burnolRadiusTruncatedFourierRaw (1 / 4 : ℝ)
        (burnolAmbientMeanZeroSecondCorrection value : BurnolQuarterIntervalL2))
      x

def burnolEvenProjectionQuarterOuterRaw
    (value : BurnolL2) (raw : ℝ → ℂ) : ℂ :=
  burnolEvenProjectionPositiveOuterRaw value raw (1 / 4 : ℝ)

def burnolEvenFirstCorrectionQuarterTrace
    (value : BurnolL2) (raw : ℝ → ℂ) : ℂ :=
  (1 / 2 : ℂ) *
    (burnolFirstCorrectionRaw value raw (1 / 4 : ℝ) +
      burnolFirstCorrectionRaw value raw (-(1 / 4 : ℝ)))

/-- Exact fixed-window jump contributed by the first block correction. -/
theorem burnolEvenProjectionQuarterOuterRaw_sub_projectionRaw
    (value : BurnolL2) (raw : ℝ → ℂ) :
    burnolEvenProjectionQuarterOuterRaw value raw -
        burnolEvenProjectionRaw value raw (1 / 4 : ℝ) =
      burnolEvenFirstCorrectionQuarterTrace value raw := by
  have posGap : (1 / 4 : ℝ) ∈ symmetricInterval (1 / 4 : ℝ) := by
    simp [symmetricInterval]
  have negGap : (-(1 / 4 : ℝ)) ∈ symmetricInterval (1 / 4 : ℝ) := by
    simp [symmetricInterval]
  unfold burnolEvenProjectionQuarterOuterRaw
    burnolEvenProjectionPositiveOuterRaw
    burnolEvenFirstCorrectionQuarterTrace burnolEvenProjectionRaw
    burnolRawCorrectionRaw burnolEvenRaw
  simp only [Set.indicator_of_mem posGap, Set.indicator_of_mem negGap]
  ring

theorem burnolEvenProjectionRaw_eq_positiveOuter
    (value : BurnolL2) (raw : ℝ → ℂ) {x : ℝ}
    (outside : (1 / 4 : ℝ) < x) :
    burnolEvenProjectionRaw value raw x =
      burnolEvenProjectionPositiveOuterRaw value raw x := by
  have xNotGap : x ∉ symmetricInterval (1 / 4 : ℝ) := by
    simp only [symmetricInterval, mem_Icc, not_and_or]
    exact Or.inr (not_le_of_gt outside)
  have negXNotGap : -x ∉ symmetricInterval (1 / 4 : ℝ) := by
    simp only [symmetricInterval, mem_Icc, not_and_or]
    exact Or.inl (by linarith)
  unfold burnolEvenProjectionRaw burnolRawCorrectionRaw
    burnolEvenProjectionPositiveOuterRaw burnolEvenRaw
  simp only [Set.indicator_of_notMem xNotGap,
    Set.indicator_of_notMem negXNotGap, zero_add]

theorem burnolEvenProjectionRaw_tendsto_quarter_right
    (value : BurnolL2) (raw : ℝ → ℂ)
    (continuousPlus : ContinuousAt raw (1 / 4 : ℝ))
    (continuousMinus : ContinuousAt raw (-(1 / 4 : ℝ))) :
    Tendsto (burnolEvenProjectionRaw value raw)
      (nhdsWithin (1 / 4 : ℝ) (Ioi (1 / 4 : ℝ)))
      (nhds (burnolEvenProjectionQuarterOuterRaw value raw)) := by
  have reflected : ContinuousAt (fun x : ℝ => raw (-x)) (1 / 4 : ℝ) := by
    have negAt : ContinuousAt (fun x : ℝ => -x) (1 / 4 : ℝ) := continuousAt_neg
    have source : ContinuousAt (raw ∘ fun x : ℝ => -x) (1 / 4 : ℝ) :=
      ContinuousAt.comp_of_eq (f := fun x : ℝ => -x) (g := raw)
        (y := -(1 / 4 : ℝ)) continuousMinus negAt rfl
    exact source
  have outerContinuous : ContinuousAt
      (burnolEvenProjectionPositiveOuterRaw value raw) (1 / 4 : ℝ) := by
    unfold burnolEvenProjectionPositiveOuterRaw burnolEvenRaw
    have second : Continuous
        (burnolRadiusTruncatedFourierRaw (1 / 4 : ℝ)
          (burnolAmbientMeanZeroSecondCorrection value : BurnolQuarterIntervalL2)) :=
      burnolRadiusTruncatedFourierRaw_continuous _
    fun_prop
  have outerLimit : Tendsto (burnolEvenProjectionPositiveOuterRaw value raw)
      (nhdsWithin (1 / 4 : ℝ) (Ioi (1 / 4 : ℝ)))
      (nhds (burnolEvenProjectionQuarterOuterRaw value raw)) := by
    change Tendsto (burnolEvenProjectionPositiveOuterRaw value raw)
      (nhdsWithin (1 / 4 : ℝ) (Ioi (1 / 4 : ℝ)))
      (nhds (burnolEvenProjectionPositiveOuterRaw value raw (1 / 4 : ℝ)))
    exact outerContinuous.tendsto.mono_left inf_le_left
  apply outerLimit.congr'
  filter_upwards [self_mem_nhdsWithin] with x hx
  exact (burnolEvenProjectionRaw_eq_positiveOuter value raw hx).symm

def burnolPairedBoundaryQuarterOuterRaw
    (coordinate : BurnolCompletedMellinCoordinate) (shift : ℝ) : ℂ :=
  pairedMellinTranslationCharacter coordinate.value shift *
      burnolRieszStatePositiveOuterRaw coordinate (1 / 4 : ℝ) -
    burnolEvenProjectionQuarterOuterRaw
      (pairedBurnolMultiplicativeDilation shift
        (burnolCompletedMellinRieszVector coordinate : BurnolL2))
      (burnolRieszPairedDilationRaw coordinate shift)

/-- The displayed outer value is the genuine right trace of the canonical
unclamped boundary whenever the paired displacement is nontrivial. -/
theorem burnolPairedBoundaryUnclampedRaw_tendsto_quarter_right
    (coordinate : BurnolCompletedMellinCoordinate) {shift : ℝ}
    (positiveShift : 0 < shift) :
    Tendsto (burnolPairedBoundaryUnclampedRaw coordinate shift)
      (nhdsWithin (1 / 4 : ℝ) (Ioi (1 / 4 : ℝ)))
      (nhds (burnolPairedBoundaryQuarterOuterRaw coordinate shift)) := by
  let value := pairedBurnolMultiplicativeDilation shift
    (burnolCompletedMellinRieszVector coordinate : BurnolL2)
  let raw := burnolRieszPairedDilationRaw coordinate shift
  have riesz := burnolRieszStateRaw_tendsto_quarter_right coordinate
  have projected := burnolEvenProjectionRaw_tendsto_quarter_right value raw
    (burnolRieszPairedDilationRaw_continuousAt_quarter coordinate positiveShift)
    (burnolRieszPairedDilationRaw_continuousAt_neg_quarter coordinate positiveShift)
  have scalar : Tendsto
      (fun _x : ℝ => pairedMellinTranslationCharacter coordinate.value shift)
      (nhdsWithin (1 / 4 : ℝ) (Ioi (1 / 4 : ℝ)))
      (nhds (pairedMellinTranslationCharacter coordinate.value shift)) :=
    tendsto_const_nhds
  have scaled : Tendsto
      (fun x : ℝ => pairedMellinTranslationCharacter coordinate.value shift *
        burnolRieszStateRaw coordinate x)
      (nhdsWithin (1 / 4 : ℝ) (Ioi (1 / 4 : ℝ)))
      (nhds (pairedMellinTranslationCharacter coordinate.value shift *
        burnolRieszStatePositiveOuterRaw coordinate (1 / 4 : ℝ))) :=
    scalar.mul riesz
  have assembled := scaled.sub projected
  change Tendsto
    (fun x : ℝ => pairedMellinTranslationCharacter coordinate.value shift *
        burnolRieszStateRaw coordinate x -
      burnolEvenProjectionRaw value raw x)
    (nhdsWithin (1 / 4 : ℝ) (Ioi (1 / 4 : ℝ)))
    (nhds (pairedMellinTranslationCharacter coordinate.value shift *
        burnolRieszStatePositiveOuterRaw coordinate (1 / 4 : ℝ) -
      burnolEvenProjectionQuarterOuterRaw value raw))
  exact assembled

theorem burnolPairedBoundaryRaw_tendsto_quarter_right
    (coordinate : BurnolCompletedMellinCoordinate)
    (zero : riemannZeta coordinate.value = 0) {shift : ℝ}
    (positiveShift : 0 < shift) :
    Tendsto (burnolPairedBoundaryRaw coordinate zero shift)
      (nhdsWithin (1 / 4 : ℝ) (Ioi (1 / 4 : ℝ)))
      (nhds (burnolPairedBoundaryQuarterOuterRaw coordinate shift)) := by
  have source := burnolPairedBoundaryUnclampedRaw_tendsto_quarter_right
    coordinate positiveShift
  apply source.congr'
  filter_upwards [self_mem_nhdsWithin] with x hx
  have positiveX : 0 < x := (by norm_num : (0 : ℝ) < 1 / 4) |>.trans hx
  have outside : ¬ |x| ≤ (1 / 4 : ℝ) := by
    rw [abs_of_pos positiveX]
    exact not_le_of_gt hx
  simp only [burnolPairedBoundaryRaw, outside, if_false]

end
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
