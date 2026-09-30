import H0mework.NavierStokes.Accumulation.ConcretePhaseRichRecursiveInvariant

set_option autoImplicit false

open scoped BigOperators Matrix

namespace SaturationMonoid
namespace NavierStokes
namespace RationalVorticityEvaluator
namespace PhaseRichTriple

open Matrix
open ThreeDimensionalVorticityCoefficientStretchingPairTable
open ThreeDimensionalVorticityCoefficientGeneratedShellSerrinGeometry
open ThreeDimensionalVorticityCoefficientGeneratedShellViscousParseval

set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

def sourceGeneratedActionWaveFinset : Finset Wave :=
  (((sourceWaveModes ×ˢ sourceWaveModes).image fun pair =>
      pair.1.add pair.2) ∪ sourceWaveModes).erase (w 0 0 0)

theorem actionWaveCarrier_nodup : actionWaveCarrier.Nodup := by decide

theorem actionWaveCarrier_toFinset_eq_sourceGenerated :
    actionWaveCarrier.toFinset = sourceGeneratedActionWaveFinset := by
  decide

theorem generatedActionWaveList_length_eq :
    generatedActionWaveList.length = 104 := by
  norm_num [generatedActionWaveList, sourceEntries,
    actionWaveCarrier, Wave.add, w]

theorem generatedSourceWork_eq :
    generatedSourceWork = 15934 / 125 := by
  simp (config := { maxSteps := 50000000 })
    [generatedSourceWork, entriesRealInner, sourceEntries,
    generatedActionState, generatedActionEntries,
    generatedActionWaveList, actionWaveCarrier,
    sourceGeneratorAt, sourceNonlinearAt,
    sourceWaveModes, pairContribution,
    rationalVorticityPairContribution, Wave.toIntegerWavevector,
    Wave.add, Wave.sub, lookup, vectorRealInner,
    GaussianRatVector.add, GaussianRatVector.sub,
    GaussianRatVector.complexScale, GaussianRatVector.ratScale,
    GaussianRatVector.waveDot, GaussianRatVector.waveCross,
    GaussianRatVector.tripleWaveCrossDot,
    GaussianRat.add, GaussianRat.neg, GaussianRat.sub,
    GaussianRat.mul, GaussianRat.ratScale,
    GaussianRat.intScale, GaussianRat.ratDiv,
    rationalIntegerWaveNormSq, waveNormSq, scaledViscosity,
    state, rowP₁, rowQ₁, rowR₁, rowL₁,
    rowP₂, rowQ₂, rowR₂, rowL₂,
    vectorConj, gConj, g, w,
    Fin.sum_univ_succ, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two]
  norm_num

theorem generatedActionMass_eq :
    entriesMass generatedActionEntries =
      59947184987 / 1000000 := by
  simp (config := { maxSteps := 100000000 })
    [entriesMass, generatedActionEntries,
    generatedActionWaveList, actionWaveCarrier,
    sourceGeneratorAt, sourceNonlinearAt, sourceWaveModes,
    pairContribution, rationalVorticityPairContribution,
    Wave.toIntegerWavevector, Wave.sub, lookup,
    vectorNormSq, GaussianRat.normSq,
    GaussianRatVector.add, GaussianRatVector.sub,
    GaussianRatVector.complexScale, GaussianRatVector.ratScale,
    GaussianRatVector.waveDot, GaussianRatVector.waveCross,
    GaussianRatVector.tripleWaveCrossDot,
    GaussianRat.add, GaussianRat.neg, GaussianRat.sub,
    GaussianRat.mul, GaussianRat.ratScale,
    GaussianRat.intScale, GaussianRat.ratDiv,
    rationalIntegerWaveNormSq, waveNormSq, scaledViscosity,
    state, sourceEntries,
    rowP₁, rowQ₁, rowR₁, rowL₁,
    rowP₂, rowQ₂, rowR₂, rowL₂,
    vectorConj, gConj, g, w,
    Fin.sum_univ_succ, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two]
  norm_num

theorem generatedSourceWorkDerivative_eq :
    generatedSourceWorkDerivative =
      1040972355479 / 58500000 := by
  rw [generatedSourceWorkDerivative, generatedActionMass_eq]
  simp (config := { maxSteps := 150000000 })
    [entriesRealInner, sourceEntries, generatedLinearizedAction,
    generatedActionOnLeftAt, generatedActionOnRightAt,
    generatedActionState, generatedActionEntries,
    generatedActionWaveList,
    actionWaveCarrier, sourceGeneratorAt, sourceNonlinearAt,
    sourceWaveModes, pairContribution,
    rationalVorticityPairContribution,
    Wave.toIntegerWavevector, Wave.sub, lookup,
    vectorRealInner,
    GaussianRatVector.add, GaussianRatVector.sub,
    GaussianRatVector.complexScale, GaussianRatVector.ratScale,
    GaussianRatVector.waveDot, GaussianRatVector.waveCross,
    GaussianRatVector.tripleWaveCrossDot,
    GaussianRat.add, GaussianRat.neg, GaussianRat.sub,
    GaussianRat.mul, GaussianRat.ratScale,
    GaussianRat.intScale, GaussianRat.ratDiv,
    rationalIntegerWaveNormSq, waveNormSq, scaledViscosity,
    state, rowP₁, rowQ₁, rowR₁, rowL₁,
    rowP₂, rowQ₂, rowR₂, rowL₂,
    vectorConj, gConj, g, w,
    Fin.sum_univ_succ, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two]
  norm_num

theorem generatedNormalizedWorkInwardNumerator_eq :
    generatedNormalizedWorkInwardNumerator =
      3103113462669 / 406250 := by
  rw [generatedNormalizedWorkInwardNumerator,
    sourceMass_eq, generatedSourceWorkDerivative_eq,
    generatedSourceWork_eq]
  norm_num

theorem generatedNormalizedWorkInwardNumerator_pos :
    0 < generatedNormalizedWorkInwardNumerator := by
  rw [generatedNormalizedWorkInwardNumerator_eq]
  norm_num

/-- Inward numerator for the weaker, still superlinear work ratio
`W / M^(5/4)`.  This is the source seed matched by the variable-exponent
clock fold with potential exponent `27/4`. -/
def generatedFiveQuarterWorkInwardNumerator : ℚ :=
  sourceMass * generatedSourceWorkDerivative -
    (5 / 2) * generatedSourceWork ^ 2

theorem generatedFiveQuarterWorkInwardNumerator_eq :
    generatedFiveQuarterWorkInwardNumerator =
      3106414063297 / 406250 := by
  rw [generatedFiveQuarterWorkInwardNumerator,
    sourceMass_eq, generatedSourceWorkDerivative_eq,
    generatedSourceWork_eq]
  norm_num

theorem generatedFiveQuarterWorkInwardNumerator_pos :
    0 < generatedFiveQuarterWorkInwardNumerator := by
  rw [generatedFiveQuarterWorkInwardNumerator_eq]
  norm_num

/-- Inward numerator for the augmented mass coordinate `M + 1` used by the
general-current normalized-work face. -/
def generatedAugmentedFiveQuarterWorkInwardNumerator : ℚ :=
  (sourceMass + 1) * generatedSourceWorkDerivative -
    (5 / 2) * generatedSourceWork ^ 2

theorem generatedAugmentedFiveQuarterWorkInwardNumerator_eq :
    generatedAugmentedFiveQuarterWorkInwardNumerator =
      generatedFiveQuarterWorkInwardNumerator +
        generatedSourceWorkDerivative := by
  unfold generatedAugmentedFiveQuarterWorkInwardNumerator
    generatedFiveQuarterWorkInwardNumerator
  ring

theorem generatedAugmentedFiveQuarterWorkInwardNumerator_pos :
    0 < generatedAugmentedFiveQuarterWorkInwardNumerator := by
  rw [generatedAugmentedFiveQuarterWorkInwardNumerator_eq]
  have derivativePos : 0 < generatedSourceWorkDerivative := by
    rw [generatedSourceWorkDerivative_eq]
    norm_num
  linarith [generatedFiveQuarterWorkInwardNumerator_pos]

/-! ## Exact materialization readouts -/

/-- Squared Gaussian-rational amplitude commutes with the physical complex
row.  This is the scalar seam from the executable source material to the
actual Fourier carrier. -/
theorem GaussianRat.normSq_toComplex (value : GaussianRat) :
    ((GaussianRat.normSq value : ℚ) : ℝ) =
      Complex.normSq (GaussianRat.toComplex value) := by
  simp [GaussianRat.normSq, GaussianRat.toComplex,
    Complex.normSq_apply, Complex.mul_re, Complex.mul_im]
  ring

theorem vectorNormSq_toComplex (value : GaussianRatVector) :
    ((vectorNormSq value : ℚ) : ℝ) =
      complexCoordinateAmplitudeSq (GaussianRatVector.toComplex value) := by
  unfold vectorNormSq complexCoordinateAmplitudeSq
  rw [Rat.cast_sum]
  apply Finset.sum_congr rfl
  intro coordinate _
  exact GaussianRat.normSq_toComplex (value coordinate)

theorem vectorRealInner_toComplex
    (left right : GaussianRatVector) :
    ((vectorRealInner left right : ℚ) : ℝ) =
      complexCoordinateRealInner
        (GaussianRatVector.toComplex left)
        (GaussianRatVector.toComplex right) := by
  unfold vectorRealInner complexCoordinateRealInner
  rw [Rat.cast_sum]
  apply Finset.sum_congr rfl
  intro coordinate _
  simp [GaussianRatVector.toComplex, GaussianRat.toComplex,
    Complex.mul_re, Complex.mul_im]

theorem lookup_map_self_of_mem
    (keys : List Wave)
    (right : Wave → GaussianRatVector)
    (keysNodup : keys.Nodup)
    {wave : Wave}
    (waveMem : wave ∈ keys) :
    lookup (keys.map fun key => (key, right key)) wave = right wave := by
  induction keys with
  | nil => simp at waveMem
  | cons head tail induction =>
      simp only [List.nodup_cons] at keysNodup
      simp only [List.mem_cons] at waveMem
      rw [List.map_cons, lookup]
      rcases waveMem with rfl | waveTail
      · rw [if_pos rfl]
      · rw [if_neg (fun (equality : head = wave) =>
          keysNodup.1 (equality.symm ▸ waveTail))]
        exact induction keysNodup.2 waveTail

theorem sourceEntryKeys_nodup :
    (sourceEntries.map Prod.fst).Nodup := by decide

theorem sourceEntry_value_eq_state
    (entry : Entry)
    (entryMem : entry ∈ sourceEntries) :
    entry.2 = state entry.1 := by
  simp only [sourceEntries, List.mem_cons, List.mem_nil_iff,
    or_false] at entryMem
  rcases entryMem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [state, lookup, sourceEntries, w]

theorem sourceWaveModes_subset_actionWaveCarrier :
    sourceWaveModes ⊆ actionWaveCarrier.toFinset := by decide

/-- Every source wave reads the action generated by the actual incidence
compiler.  The cached action table is not used in this theorem. -/
theorem generatedActionState_eq_sourceGeneratorAt
    {wave : Wave}
    (waveMem : wave ∈ sourceWaveModes) :
    generatedActionState wave = sourceGeneratorAt wave := by
  apply lookup_map_self_of_mem actionWaveCarrier sourceGeneratorAt
    actionWaveCarrier_nodup
  exact sourceWaveModes_subset_actionWaveCarrier waveMem

/-- The source/action pairing is the same finite material row already
computed by `generatedSourceWork`; no hand-entered action coefficient is
accepted. -/
theorem sourceWaveGeneratorWork_eq_generatedSourceWork :
    (∑ wave ∈ sourceWaveModes,
      vectorRealInner (state wave) (sourceGeneratorAt wave)) =
      generatedSourceWork := by
  rw [sourceWaveModes]
  rw [List.sum_toFinset
    (fun wave => vectorRealInner (state wave) (sourceGeneratorAt wave))
    sourceEntryKeys_nodup]
  unfold generatedSourceWork entriesRealInner
  rw [List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro entry entryMem
  simp only [Function.comp_apply]
  rw [sourceEntry_value_eq_state entry entryMem]
  rw [generatedActionState_eq_sourceGeneratorAt]
  rw [sourceWaveModes, List.mem_toFinset]
  exact List.mem_map.mpr ⟨entry, entryMem, rfl⟩

end PhaseRichTriple
end RationalVorticityEvaluator
end NavierStokes
end SaturationMonoid
