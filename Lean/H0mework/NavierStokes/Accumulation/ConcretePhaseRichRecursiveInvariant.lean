import H0mework.NavierStokes.Accumulation.RationalVorticityEvaluator

set_option autoImplicit false

open scoped BigOperators Matrix

namespace SaturationMonoid
namespace NavierStokes
namespace RationalVorticityEvaluator

open Matrix
open ThreeDimensionalPeriodicCoarseFilterCore
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientStretchingPairTable
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFixedOutputNonlinearContinuity
open ThreeDimensionalVorticityCoefficientCanonicalExhaustiveGalerkinTarget
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow

noncomputable section

namespace PhaseRichTriple

open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartConcreteTwoScaleLiftSource

/-- Source-side integer wave carrier.  Unlike the analytic Pi type, equality
and subtraction reduce directly on the three actual coordinates. -/
@[ext]
structure Wave where
  x : ℤ
  y : ℤ
  z : ℤ
deriving DecidableEq, Repr

def w (x y z : ℤ) : Wave := ⟨x, y, z⟩

def Wave.toIntegerWavevector (wave : Wave) : IntegerWavevector :=
  ![wave.x, wave.y, wave.z]

def Wave.ofIntegerWavevector (wave : IntegerWavevector) : Wave :=
  w (wave 0) (wave 1) (wave 2)

@[simp] theorem Wave.ofIntegerWavevector_toIntegerWavevector
    (wave : Wave) :
    Wave.ofIntegerWavevector wave.toIntegerWavevector = wave := by
  cases wave
  rfl

@[simp] theorem Wave.toIntegerWavevector_ofIntegerWavevector
    (wave : IntegerWavevector) :
    (Wave.ofIntegerWavevector wave).toIntegerWavevector = wave := by
  funext coordinate
  fin_cases coordinate <;> rfl

theorem Wave.toIntegerWavevector_injective :
    Function.Injective Wave.toIntegerWavevector := by
  intro left right equality
  rw [← left.ofIntegerWavevector_toIntegerWavevector,
    equality, right.ofIntegerWavevector_toIntegerWavevector]

def Wave.sub (left right : Wave) : Wave :=
  w (left.x - right.x) (left.y - right.y) (left.z - right.z)

def Wave.add (left right : Wave) : Wave :=
  w (left.x + right.x) (left.y + right.y) (left.z + right.z)

@[simp] theorem Wave.toIntegerWavevector_add (left right : Wave) :
    (left.add right).toIntegerWavevector =
      left.toIntegerWavevector + right.toIntegerWavevector := by
  funext coordinate
  fin_cases coordinate <;> rfl

@[simp] theorem Wave.toIntegerWavevector_sub (left right : Wave) :
    (left.sub right).toIntegerWavevector =
      left.toIntegerWavevector - right.toIntegerWavevector := by
  funext coordinate
  fin_cases coordinate <;> rfl

def g (real imaginary : ℚ) : GaussianRat := ⟨real, imaginary⟩

def gConj (value : GaussianRat) : GaussianRat :=
  ⟨value.re, -value.im⟩

def vectorConj (value : GaussianRatVector) : GaussianRatVector :=
  fun coordinate => gConj (value coordinate)

def rowP₁ : GaussianRatVector := ![g 0 0, g (-3) (-4), g (-1) 3]
def rowQ₁ : GaussianRatVector := ![g (-3) 1, g 0 0, g 3 (-4)]
def rowR₁ : GaussianRatVector := ![g 0 (-4), g 0 4, g (-6) (-1)]
def rowL₁ : GaussianRatVector := ![g (-1) (-1), g 1 3, g 0 0]
def rowP₂ : GaussianRatVector := ![g 0 0, g (-2) 3, g 2 2]
def rowQ₂ : GaussianRatVector := ![g 2 2, g 0 0, g 3 1]
def rowR₂ : GaussianRatVector := ![g 1 1, g (-1) (-1), g 2 (-2)]
def rowL₂ : GaussianRatVector := ![g 2 0, g 1 (-3), g 0 0]

abbrev Entry := Wave × GaussianRatVector

def sourceEntries : List Entry :=
  [ (w 1 0 0, rowP₁), (w 0 1 0, rowQ₁), (w (-1) (-1) 0, rowR₁),
    (w 0 0 1, rowL₁), (w 2 0 0, rowP₂), (w 0 2 0, rowQ₂),
    (w (-2) (-2) 0, rowR₂), (w 0 0 2, rowL₂),
    (w (-1) 0 0, vectorConj rowP₁),
    (w 0 (-1) 0, vectorConj rowQ₁),
    (w 1 1 0, vectorConj rowR₁),
    (w 0 0 (-1), vectorConj rowL₁),
    (w (-2) 0 0, vectorConj rowP₂),
    (w 0 (-2) 0, vectorConj rowQ₂),
    (w 2 2 0, vectorConj rowR₂),
    (w 0 0 (-2), vectorConj rowL₂) ]

def lookup (entries : List Entry) (wave : Wave) : GaussianRatVector :=
  match entries with
  | [] => 0
  | entry :: tail =>
      if entry.1 = wave then entry.2 else lookup tail wave

theorem lookup_eq_zero_of_not_mem_keys
    (entries : List Entry)
    (wave : Wave)
    (waveNotMem : wave ∉ entries.map Prod.fst) :
    lookup entries wave = 0 := by
  induction entries with
  | nil => rfl
  | cons head tail induction =>
      simp only [List.map_cons, List.mem_cons, not_or] at waveNotMem
      rw [lookup, if_neg (Ne.symm waveNotMem.1)]
      exact induction waveNotMem.2

def state : Wave → GaussianRatVector := lookup sourceEntries

def sourceIntegerModes : Finset IntegerWavevector :=
  (sourceEntries.map fun entry => entry.1.toIntegerWavevector).toFinset

def sourceWaveModes : Finset Wave :=
  (sourceEntries.map Prod.fst).toFinset

theorem sourceIntegerModes_eq_sourceWaveModes_image :
    sourceIntegerModes =
      sourceWaveModes.image Wave.toIntegerWavevector := by
  ext wave
  simp [sourceIntegerModes, sourceWaveModes, Function.comp_def]

theorem sourceWave_mem_iff_integer_mem (wave : Wave) :
    wave ∈ sourceWaveModes ↔
      wave.toIntegerWavevector ∈ sourceIntegerModes := by
  rw [sourceIntegerModes_eq_sourceWaveModes_image]
  constructor
  · intro waveMem
    exact Finset.mem_image.mpr ⟨wave, waveMem, rfl⟩
  · intro imageMem
    obtain ⟨preimage, preimageMem, equality⟩ :=
      Finset.mem_image.mp imageMem
    have : preimage = wave :=
      Wave.toIntegerWavevector_injective equality
    simpa [this] using preimageMem

theorem sourceWaveModes_zero_not_mem :
    w 0 0 0 ∉ sourceWaveModes := by decide

theorem sourceIntegerModes_eq_repositoryModes :
    sourceIntegerModes = modes := by decide

def complexSourceState : ComplexVorticityHilbertState :=
  finiteComplexVorticityState sourceIntegerModes fun wave =>
    GaussianRatVector.toComplex (state (Wave.ofIntegerWavevector wave))

theorem complexSourceState_faithful
    (wave : IntegerWavevector) :
    complexSourceState wave =
      GaussianRatVector.toComplex
        (state (Wave.ofIntegerWavevector wave)) := by
  rw [complexSourceState, finiteComplexVorticityState_apply]
  by_cases waveMem : wave ∈ sourceIntegerModes
  · rw [if_pos waveMem]
  · rw [if_neg waveMem]
    have sourceWaveNotMem :
        Wave.ofIntegerWavevector wave ∉ sourceEntries.map Prod.fst := by
      intro sourceWaveMem
      apply waveMem
      rw [sourceIntegerModes, List.mem_toFinset]
      apply List.mem_map.mpr
      obtain ⟨entry, entryMem, entryKey⟩ :=
        List.mem_map.mp sourceWaveMem
      refine ⟨entry, entryMem, ?_⟩
      change entry.1.toIntegerWavevector = wave
      rw [entryKey, Wave.toIntegerWavevector_ofIntegerWavevector]
    rw [state, lookup_eq_zero_of_not_mem_keys
      sourceEntries (Wave.ofIntegerWavevector wave) sourceWaveNotMem]
    exact GaussianRatVector.toComplex_zero_instance.symm

theorem complexSourceState_supported
    (wave : IntegerWavevector)
    (waveNotMem : wave ∉ sourceIntegerModes) :
    complexSourceState wave = 0 := by
  rw [complexSourceState_faithful]
  have sourceWaveNotMem :
      Wave.ofIntegerWavevector wave ∉ sourceEntries.map Prod.fst := by
    intro sourceWaveMem
    apply waveNotMem
    rw [sourceIntegerModes, List.mem_toFinset]
    apply List.mem_map.mpr
    obtain ⟨entry, entryMem, entryKey⟩ :=
      List.mem_map.mp sourceWaveMem
    refine ⟨entry, entryMem, ?_⟩
    change entry.1.toIntegerWavevector = wave
    rw [entryKey, Wave.toIntegerWavevector_ofIntegerWavevector]
  rw [state, lookup_eq_zero_of_not_mem_keys
    sourceEntries (Wave.ofIntegerWavevector wave) sourceWaveNotMem]
  exact GaussianRatVector.toComplex_zero_instance


def scaledViscosity : ℚ := 1 / 2000

def pairContribution
    (first second : Wave)
    (firstRow secondRow : GaussianRatVector) : GaussianRatVector :=
  rationalVorticityPairContribution
    first.toIntegerWavevector second.toIntegerWavevector
    firstRow secondRow

theorem pairContribution_toComplex
    (leftState rightState : ComplexVorticityHilbertState)
    (first second : Wave)
    (firstRow secondRow : GaussianRatVector)
    (firstNonzero : first ≠ w 0 0 0)
    (secondNonzero : second ≠ w 0 0 0)
    (firstFaithful :
      GaussianRatVector.toComplex firstRow =
        leftState first.toIntegerWavevector)
    (secondFaithful :
      GaussianRatVector.toComplex secondRow =
        rightState second.toIntegerWavevector) :
    GaussianRatVector.toComplex
        (pairContribution first second firstRow secondRow) =
      finiteStateVorticityBilinearPairContribution
        leftState rightState
        (first.toIntegerWavevector, second.toIntegerWavevector) := by
  apply rationalVorticityPairContribution_toComplex
  · intro firstZero
    apply firstNonzero
    apply Wave.toIntegerWavevector_injective
    simpa [Wave.toIntegerWavevector, w] using firstZero
  · intro secondZero
    apply secondNonzero
    apply Wave.toIntegerWavevector_injective
    simpa [Wave.toIntegerWavevector, w] using secondZero
  · exact firstFaithful
  · exact secondFaithful

theorem finiteStateVorticityBilinearCoefficientAt_eq_single_sum
    (modes : Finset IntegerWavevector)
    (left right : ComplexVorticityHilbertState)
    (output : IntegerWavevector) :
    finiteStateVorticityBilinearCoefficientAt
        modes left right output =
      ∑ first ∈ modes,
        if output - first ∈ modes then
          finiteStateVorticityBilinearPairContribution
            left right (first, output - first)
        else 0 := by
  unfold finiteStateVorticityBilinearCoefficientAt
  apply Finset.sum_congr rfl
  intro first firstMem
  have condition :
      ∀ second : IntegerWavevector,
        first + second = output ↔ second = output - first := by
    intro second
    constructor <;> intro equality
    · rw [← equality]
      abel
    · rw [equality]
      abel
  simp_rw [condition]
  by_cases translatedMem : output - first ∈ modes
  · simp [translatedMem]
  · simp [translatedMem]

theorem finiteStateVorticityNonlinearCoefficientAt_eq_single_sum
    (modes : Finset IntegerWavevector)
    (state : ComplexVorticityHilbertState)
    (output : IntegerWavevector) :
    finiteStateVorticityNonlinearCoefficientAt modes state output =
      ∑ first ∈ modes,
        if output - first ∈ modes then
          finiteStateVorticityNonlinearPairContribution
            state (first, output - first)
        else 0 := by
  simpa only [finiteStateVorticityBilinearCoefficientAt,
    finiteStateVorticityNonlinearCoefficientAt,
    finiteStateVorticityBilinearPairContribution,
    finiteStateVorticityNonlinearPairContribution] using
    finiteStateVorticityBilinearCoefficientAt_eq_single_sum
      modes state state output

def waveNormSq (wave : Wave) : ℚ :=
  wave.x ^ 2 + wave.y ^ 2 + wave.z ^ 2

theorem waveNormSq_cast (wave : Wave) :
    (waveNormSq wave : ℝ) =
      integerWaveNormSq wave.toIntegerWavevector := by
  cases wave
  simp [waveNormSq, Wave.toIntegerWavevector,
    integerWaveNormSq, Fin.sum_univ_succ,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]
  ring

def sourceNonlinearAt (output : Wave) : GaussianRatVector :=
  ∑ first ∈ sourceWaveModes,
    let second := output.sub first
    if second ∈ sourceWaveModes then
      pairContribution first second (state first) (state second)
    else 0

def sourceGeneratorAt (output : Wave) : GaussianRatVector :=
  GaussianRatVector.sub
    (sourceNonlinearAt output)
    (GaussianRatVector.ratScale
      (scaledViscosity * waveNormSq output) (state output))

theorem sourceNonlinearAt_toComplex (output : Wave) :
    GaussianRatVector.toComplex (sourceNonlinearAt output) =
      finiteStateVorticityNonlinearCoefficientAt
        sourceIntegerModes complexSourceState
        output.toIntegerWavevector := by
  rw [finiteStateVorticityNonlinearCoefficientAt_eq_single_sum,
    sourceIntegerModes_eq_sourceWaveModes_image,
    Finset.sum_image Wave.toIntegerWavevector_injective.injOn]
  rw [sourceNonlinearAt,
    GaussianRatVector.toComplex_finsetSum]
  apply Finset.sum_congr rfl
  intro first firstMem
  let second := output.sub first
  have secondIntegerEq :
      output.toIntegerWavevector - first.toIntegerWavevector =
        second.toIntegerWavevector := by
    exact (Wave.toIntegerWavevector_sub output first).symm
  rw [secondIntegerEq]
  by_cases secondMem : second ∈ sourceWaveModes
  · have secondImageMem :
        second.toIntegerWavevector ∈
          sourceWaveModes.image Wave.toIntegerWavevector :=
      Finset.mem_image.mpr ⟨second, secondMem, rfl⟩
    rw [if_pos secondMem, if_pos secondImageMem]
    apply pairContribution_toComplex
    · exact fun firstZero => sourceWaveModes_zero_not_mem
        (firstZero ▸ firstMem)
    · exact fun secondZero => sourceWaveModes_zero_not_mem
        (secondZero ▸ secondMem)
    · simpa using
        (complexSourceState_faithful
          first.toIntegerWavevector).symm
    · have faithful :
          GaussianRatVector.toComplex (state (output.sub first)) =
            complexSourceState (output.sub first).toIntegerWavevector := by
        simpa only [Wave.ofIntegerWavevector_toIntegerWavevector] using
          (complexSourceState_faithful
            (output.sub first).toIntegerWavevector).symm
      exact faithful
  · have secondImageNotMem :
        second.toIntegerWavevector ∉
          sourceWaveModes.image Wave.toIntegerWavevector := by
      intro imageMem
      obtain ⟨preimage, preimageMem, equality⟩ :=
        Finset.mem_image.mp imageMem
      have preimageEq : preimage = second :=
        Wave.toIntegerWavevector_injective equality
      exact secondMem (preimageEq ▸ preimageMem)
    rw [if_neg secondMem, if_neg secondImageNotMem]
    exact GaussianRatVector.toComplex_zero_instance

def viscosity : Viscosity where
  coeff := 1 / (2000 * (2 * Real.pi) ^ 2)
  coeff_pos := by positivity

theorem viscosity_scaled :
    viscosity.coeff * (2 * Real.pi) ^ 2 = (scaledViscosity : ℝ) := by
  unfold viscosity scaledViscosity
  field_simp [Real.pi_ne_zero]
  norm_num

theorem sourceGeneratorAt_toComplex (output : Wave) :
    GaussianRatVector.toComplex (sourceGeneratorAt output) =
      wholeLatticeVorticityFourierTangentAt
        viscosity.coeff complexSourceState output.toIntegerWavevector := by
  rw [sourceGeneratorAt, GaussianRatVector.toComplex_sub,
    GaussianRatVector.toComplex_ratScale,
    sourceNonlinearAt_toComplex]
  unfold wholeLatticeVorticityFourierTangentAt
  rw [wholeStateVorticityNonlinearCoefficientAt_eq_finite_of_supported
    sourceIntegerModes complexSourceState complexSourceState_supported]
  have sourceFaithful :=
    (complexSourceState_faithful output.toIntegerWavevector).symm
  simp only [Wave.ofIntegerWavevector_toIntegerWavevector] at sourceFaithful
  rw [← sourceFaithful]
  congr 1
  have scalarEq :
      (((scaledViscosity * waveNormSq output : ℚ) : ℝ) : ℂ) =
        ((viscosity.coeff *
          integerWaveViscousMultiplier output.toIntegerWavevector : ℝ) : ℂ) := by
    congr 1
    rw [Rat.cast_mul, waveNormSq_cast,
      integerWaveViscousMultiplier]
    calc
      (scaledViscosity : ℝ) *
          integerWaveNormSq output.toIntegerWavevector =
        (viscosity.coeff * (2 * Real.pi) ^ 2) *
          integerWaveNormSq output.toIntegerWavevector := by
            rw [viscosity_scaled]
      _ = viscosity.coeff *
          ((2 * Real.pi) ^ 2 *
            integerWaveNormSq output.toIntegerWavevector) := by ring
  rw [scalarEq]
  rfl

def GaussianRat.normSq (value : GaussianRat) : ℚ :=
  value.re ^ 2 + value.im ^ 2

def vectorNormSq (value : GaussianRatVector) : ℚ :=
  ∑ coordinate : Fin 3, GaussianRat.normSq (value coordinate)

def vectorRealInner
    (left right : GaussianRatVector) : ℚ :=
  ∑ coordinate : Fin 3, (
    (left coordinate).re * (right coordinate).re +
      (left coordinate).im * (right coordinate).im)

def entriesMass (entries : List Entry) : ℚ :=
  (entries.map fun entry => vectorNormSq entry.2).sum

def entriesRealInner
    (leftEntries : List Entry)
    (right : Wave → GaussianRatVector) : ℚ :=
  (leftEntries.map fun entry =>
    vectorRealInner entry.2 (right entry.1)).sum

def sourceMass : ℚ := entriesMass sourceEntries

def actionWaveCarrier : List Wave :=
  [ w (-4) (-4) 0,
    w (-4) (-2) 0,
    w (-4) 0 0,
    w (-3) (-3) 0,
    w (-3) (-2) 0,
    w (-3) (-1) 0,
    w (-3) 0 0,
    w (-2) (-4) 0,
    w (-2) (-3) 0,
    w (-2) (-2) (-2),
    w (-2) (-2) (-1),
    w (-2) (-2) 0,
    w (-2) (-2) 1,
    w (-2) (-2) 2,
    w (-2) (-1) 0,
    w (-2) 0 (-2),
    w (-2) 0 (-1),
    w (-2) 0 0,
    w (-2) 0 1,
    w (-2) 0 2,
    w (-2) 1 0,
    w (-2) 2 0,
    w (-1) (-3) 0,
    w (-1) (-2) 0,
    w (-1) (-1) (-2),
    w (-1) (-1) (-1),
    w (-1) (-1) 0,
    w (-1) (-1) 1,
    w (-1) (-1) 2,
    w (-1) 0 (-2),
    w (-1) 0 (-1),
    w (-1) 0 0,
    w (-1) 0 1,
    w (-1) 0 2,
    w (-1) 1 0,
    w (-1) 2 0,
    w 0 (-4) 0,
    w 0 (-3) 0,
    w 0 (-2) (-2),
    w 0 (-2) (-1),
    w 0 (-2) 0,
    w 0 (-2) 1,
    w 0 (-2) 2,
    w 0 (-1) (-2),
    w 0 (-1) (-1),
    w 0 (-1) 0,
    w 0 (-1) 1,
    w 0 (-1) 2,
    w 0 0 (-4),
    w 0 0 (-3),
    w 0 0 (-2),
    w 0 0 (-1),
    w 0 0 1,
    w 0 0 2,
    w 0 0 3,
    w 0 0 4,
    w 0 1 (-2),
    w 0 1 (-1),
    w 0 1 0,
    w 0 1 1,
    w 0 1 2,
    w 0 2 (-2),
    w 0 2 (-1),
    w 0 2 0,
    w 0 2 1,
    w 0 2 2,
    w 0 3 0,
    w 0 4 0,
    w 1 (-2) 0,
    w 1 (-1) 0,
    w 1 0 (-2),
    w 1 0 (-1),
    w 1 0 0,
    w 1 0 1,
    w 1 0 2,
    w 1 1 (-2),
    w 1 1 (-1),
    w 1 1 0,
    w 1 1 1,
    w 1 1 2,
    w 1 2 0,
    w 1 3 0,
    w 2 (-2) 0,
    w 2 (-1) 0,
    w 2 0 (-2),
    w 2 0 (-1),
    w 2 0 0,
    w 2 0 1,
    w 2 0 2,
    w 2 1 0,
    w 2 2 (-2),
    w 2 2 (-1),
    w 2 2 0,
    w 2 2 1,
    w 2 2 2,
    w 2 3 0,
    w 2 4 0,
    w 3 0 0,
    w 3 1 0,
    w 3 2 0,
    w 3 3 0,
    w 4 0 0,
    w 4 2 0,
    w 4 4 0 ]

def generatedActionIncidenceWaves : List Wave :=
  (((sourceEntries.flatMap fun first =>
      sourceEntries.map fun second => first.1.add second.1) ++
    sourceEntries.map Prod.fst).filter fun wave => wave ≠ w 0 0 0).eraseDups

def generatedActionWaveList : List Wave := actionWaveCarrier

def generatedActionEntries : List Entry :=
  generatedActionWaveList.map fun wave => (wave, sourceGeneratorAt wave)

def generatedActionState : Wave → GaussianRatVector :=
  lookup generatedActionEntries

def generatedActionOnLeftAt (output : Wave) : GaussianRatVector :=
  (generatedActionEntries.map fun entry =>
    let second := output.sub entry.1
    pairContribution entry.1 second entry.2 (state second)).sum

def generatedActionOnRightAt (output : Wave) : GaussianRatVector :=
  (generatedActionEntries.map fun entry =>
    let first := output.sub entry.1
    pairContribution first entry.1 (state first) entry.2).sum

def generatedLinearizedAction : Wave → GaussianRatVector := fun output =>
  GaussianRatVector.sub
    (GaussianRatVector.add
      (generatedActionOnLeftAt output)
      (generatedActionOnRightAt output))
    (GaussianRatVector.ratScale
      (scaledViscosity * waveNormSq output)
      (generatedActionState output))

def generatedSourceWork : ℚ :=
  entriesRealInner sourceEntries generatedActionState

def generatedSourceWorkDerivative : ℚ :=
  entriesMass generatedActionEntries +
    entriesRealInner sourceEntries generatedLinearizedAction

def generatedNormalizedWorkInwardNumerator : ℚ :=
  sourceMass * generatedSourceWorkDerivative -
    3 * generatedSourceWork ^ 2

set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

theorem sourceMass_eq : sourceMass = 432 := by
  simp [sourceMass, entriesMass, sourceEntries,
    vectorNormSq, GaussianRat.normSq,
    rowP₁, rowQ₁, rowR₁, rowL₁, rowP₂, rowQ₂, rowR₂, rowL₂,
    vectorConj, gConj, g, Fin.sum_univ_succ,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]
  norm_num


end PhaseRichTriple

end

end RationalVorticityEvaluator
end NavierStokes
end SaturationMonoid
