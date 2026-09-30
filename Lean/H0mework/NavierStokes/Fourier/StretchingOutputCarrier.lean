import H0mework.NavierStokes.Fourier.StretchingPairTable

/-!
# Source-generated stretching-output carrier

The ordered-pair table is the provenance-preserving nonlinear carrier.  This
module forms its first downstream quotient: pairs with the same output
frequency are summed, while the complete output inventory and every active
output are still generated internally from the source table.

Zero output is proved silent from source-generated transversality.  Hence an
active aggregate output automatically carries a nonzero frequency, its own
coordinate observer, and a positive squared-norm quantum.  The aggregation
does not claim that every active pair survives: cancellation inside one
output fiber remains an explicit projection kernel.
-/

namespace SaturationMonoid
namespace NavierStokes
namespace ThreeDimensionalVorticityCoefficientStretchingOutputCarrier

open scoped BigOperators Matrix

open Matrix
open ThreeDimensionalPeriodicCoarseFilterCore
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientStretchingPairTable

noncomputable section

/-! ## The zero output is source-forced silent -/

theorem pairSecond_eq_waveNeg_first_of_output_eq_zero
    (pair : StretchingPair)
    (outputZero : stretchingPairOutput pair = 0) :
    pair.2 = waveNeg pair.1 := by
  change pair.1 + pair.2 = 0 at outputZero
  have reversed : pair.2 + pair.1 = 0 := by
    simpa [add_comm] using outputZero
  exact add_eq_zero_iff_eq_neg.mp reversed

theorem generatedStretchingPairContribution_eq_zero_of_output_eq_zero
    (source : RawVorticityFourierSource)
    (pair : StretchingPair)
    (outputZero : stretchingPairOutput pair = 0) :
    generatedStretchingPairContribution source pair = 0 := by
  have secondWave :=
    pairSecond_eq_waveNeg_first_of_output_eq_zero pair outputZero
  have transverse :=
    generatedVorticityCoefficient_transverse source pair.1
  have dotZero :
      complexWavevector pair.2 ⬝ᵥ
          generatedVorticityCoefficient source pair.1 = 0 := by
    rw [secondWave, complexWavevector_waveNeg]
    simpa using congrArg Neg.neg transverse
  simp [generatedStretchingPairContribution, dotZero]

@[simp] theorem generatedStretchingCoefficientAt_zero
    (source : RawVorticityFourierSource) :
    generatedStretchingCoefficientAt source 0 = 0 := by
  rw [generatedStretchingCoefficientAt]
  apply Finset.sum_eq_zero
  intro pair membership
  exact generatedStretchingPairContribution_eq_zero_of_output_eq_zero
    source pair
      ((mem_generatedStretchingPairFiber_iff source 0 pair).mp
        membership).2

/-! ## Complete and active output inventories -/

/-- Every output frequency appearing in the one complete pair table. -/
def generatedStretchingOutputInventory
    (source : RawVorticityFourierSource) : Finset IntegerWavevector :=
  (generatedStretchingPairTable source).image stretchingPairOutput

@[simp] theorem mem_generatedStretchingOutputInventory_iff
    (source : RawVorticityFourierSource)
    (output : IntegerWavevector) :
    output ∈ generatedStretchingOutputInventory source ↔
      ∃ pair ∈ generatedStretchingPairTable source,
        stretchingPairOutput pair = output := by
  simp [generatedStretchingOutputInventory]

@[simp] theorem mem_generatedStretchingOutputInventory_waveNeg_iff
    (source : RawVorticityFourierSource)
    (output : IntegerWavevector) :
    waveNeg output ∈ generatedStretchingOutputInventory source ↔
      output ∈ generatedStretchingOutputInventory source := by
  rw [mem_generatedStretchingOutputInventory_iff,
    mem_generatedStretchingOutputInventory_iff]
  constructor
  · rintro ⟨pair, pairMembership, pairOutput⟩
    refine ⟨stretchingPairNeg pair,
      (mem_generatedStretchingPairTable_pairNeg_iff source pair).mpr
        pairMembership,
      ?_⟩
    rw [stretchingPairOutput_pairNeg, pairOutput,
      waveNeg_involutive]
  · rintro ⟨pair, pairMembership, pairOutput⟩
    refine ⟨stretchingPairNeg pair,
      (mem_generatedStretchingPairTable_pairNeg_iff source pair).mpr
        pairMembership,
      ?_⟩
    rw [stretchingPairOutput_pairNeg, pairOutput]

/-- Aggregate outputs are filtered for nonvanishing only after generation. -/
def activeStretchingOutputInventory
    (source : RawVorticityFourierSource) : Finset IntegerWavevector :=
  (generatedStretchingOutputInventory source).filter
    (fun output => generatedStretchingCoefficientAt source output ≠ 0)

@[simp] theorem mem_activeStretchingOutputInventory_iff
    (source : RawVorticityFourierSource)
    (output : IntegerWavevector) :
    output ∈ activeStretchingOutputInventory source ↔
      output ∈ generatedStretchingOutputInventory source ∧
        generatedStretchingCoefficientAt source output ≠ 0 := by
  simp [activeStretchingOutputInventory]

theorem activeStretchingOutput_ne_zero
    (source : RawVorticityFourierSource)
    {output : IntegerWavevector}
    (membership : output ∈ activeStretchingOutputInventory source) :
    output ≠ 0 := by
  intro outputZero
  subst output
  exact
    (mem_activeStretchingOutputInventory_iff source 0).mp membership |>.2
      (generatedStretchingCoefficientAt_zero source)

@[simp] theorem mem_activeStretchingOutputInventory_waveNeg_iff
    (source : RawVorticityFourierSource)
    (output : IntegerWavevector) :
    waveNeg output ∈ activeStretchingOutputInventory source ↔
      output ∈ activeStretchingOutputInventory source := by
  rw [mem_activeStretchingOutputInventory_iff,
    mem_activeStretchingOutputInventory_iff,
    mem_generatedStretchingOutputInventory_waveNeg_iff,
    generatedStretchingCoefficientAt_waveNeg]
  constructor
  · rintro ⟨outputMembership, conjugateNonzero⟩
    refine ⟨outputMembership, ?_⟩
    intro coefficientZero
    apply conjugateNonzero
    rw [coefficientZero, vectorConj_zero]
  · rintro ⟨outputMembership, coefficientNonzero⟩
    refine ⟨outputMembership, ?_⟩
    intro conjugateZero
    apply coefficientNonzero
    have := congrArg vectorConj conjugateZero
    simpa using this

/-! ## Whole aggregate frame, coordinate observers, and quantum -/

/-- A source-generated output occurrence before the active filter. -/
abbrev GeneratedStretchingOutputOccurrence
    (source : RawVorticityFourierSource) :=
  {output : IntegerWavevector //
    output ∈ generatedStretchingOutputInventory source}

/-- Whole output-coordinate carrier after pair-fiber aggregation. -/
abbrev StretchingOutputCarrier
    (source : RawVorticityFourierSource) :=
  GeneratedStretchingOutputOccurrence source → ComplexCoordinateVector

/-- Complete aggregate coefficient frame on the generated output inventory. -/
def generatedStretchingOutputFrame
    (source : RawVorticityFourierSource) :
    StretchingOutputCarrier source :=
  fun occurrence =>
    generatedStretchingCoefficientAt source occurrence.1

/-- One output coordinate readout on the whole aggregate frame. -/
def stretchingOutputCoordinateObserver
    (source : RawVorticityFourierSource)
    (occurrence : GeneratedStretchingOutputOccurrence source) :
    StretchingOutputCarrier source →ₗ[ℂ] ComplexCoordinateVector where
  toFun := fun frame => frame occurrence
  map_add' := by intro left right; rfl
  map_smul' := by intro scalar frame; rfl

/-- An active aggregate output generated by the source-owned nonzero filter. -/
abbrev ActiveStretchingOutputOccurrence
    (source : RawVorticityFourierSource) :=
  {output : IntegerWavevector //
    output ∈ activeStretchingOutputInventory source}

/-- Squared vector norm of one active aggregate output. -/
def activeStretchingOutputQuantum
    (source : RawVorticityFourierSource)
    (occurrence : ActiveStretchingOutputOccurrence source) : ℝ :=
  complexCoordinateVectorNormSq
    (generatedStretchingCoefficientAt source occurrence.1)

theorem activeStretchingOutputQuantum_pos
    (source : RawVorticityFourierSource)
    (occurrence : ActiveStretchingOutputOccurrence source) :
    0 < activeStretchingOutputQuantum source occurrence := by
  rw [activeStretchingOutputQuantum,
    complexCoordinateVectorNormSq_pos_iff]
  exact
    (mem_activeStretchingOutputInventory_iff source occurrence.1).mp
      occurrence.2 |>.2

/-! ## Empty-source negative controls -/

@[simp] theorem zeroRawVorticitySource_generatedStretchingOutputInventory :
    generatedStretchingOutputInventory zeroRawVorticitySource = ∅ := by
  simp [generatedStretchingOutputInventory]

@[simp] theorem zeroRawVorticitySource_activeStretchingOutputInventory :
    activeStretchingOutputInventory zeroRawVorticitySource = ∅ := by
  simp [activeStretchingOutputInventory]

end

end ThreeDimensionalVorticityCoefficientStretchingOutputCarrier
end NavierStokes
end SaturationMonoid
