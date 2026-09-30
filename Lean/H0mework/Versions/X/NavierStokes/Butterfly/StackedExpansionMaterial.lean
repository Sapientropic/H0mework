import H0mework.Versions.X.NavierStokes.Butterfly.CompleteNormalizedWorkJet

/-!
# Stacked butterfly expansion material

The next butterfly face is not used as a replacement state.  It is installed
on top of the retained source face and the complete old/new convolution is
evaluated on that stacked material.  The fresh-row mass and work are exact
polynomials in the child amplitude; this is a finite source law, not a Taylor
coefficient or a post-hoc level readout.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

open scoped BigOperators Matrix

namespace SaturationMonoid
namespace NavierStokes
namespace RationalVorticityEvaluator
namespace ButterflyStackedExpansionMaterial

open ThreeDimensionalPeriodicCoarseFilterCore
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFiniteSupportRealityTrajectory
open ThreeDimensionalVorticityCoefficientFiniteGalerkinEnstrophyBalance
open ThreeDimensionalVorticityCoefficientGeneratedShellSerrinGeometry
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientCanonicalExhaustiveGalerkinTarget
open ThreeDimensionalVorticityCoefficientGeneratedPathInfiniteNonlinearNegativeOneTimeBudget
open ThreeDimensionalVorticityCoefficientFiniteGalerkinKineticEnergyLedger
open ThreeDimensionalVorticityCoefficientGeneratedShellViscousParseval
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientInstantaneousWholeNetPowerCapture

noncomputable section

def butterflyFirstYFaceModes : Finset IntegerWavevector :=
  {axisWave 4, -axisWave 4, pumpY, -pumpY,
    axisWave 4 + pumpY, axisWave 4 - pumpY,
    -(axisWave 4 + pumpY), -(axisWave 4 - pumpY),
    pumpZ, -pumpZ}

def butterflyFirstYFaceRow
    (amplitude : Rat) (wave : IntegerWavevector) : GaussianRatVector :=
  if wave = pumpZ ∨ wave = -pumpZ then realRow 1 1 0
  else if wave = axisWave 4 ∨ wave = -axisWave 4 then
    realRow 0 0 amplitude
  else if wave = pumpY ∨ wave = -pumpY then realRow 1 0 1
  else if wave = axisWave 4 + pumpY ∨
      wave = -(axisWave 4 + pumpY) then sidebandPlusY 4 amplitude
  else if wave = axisWave 4 - pumpY ∨
      wave = -(axisWave 4 - pumpY) then sidebandMinusY 4 amplitude
  else 0

/-- Retain the complete original cell while installing the first oriented
child face.  The two pump rows agree on the overlap. -/
def butterflyFirstStackModes : Finset IntegerWavevector :=
  butterflySeedModes ∪ butterflyFirstYFaceModes

def butterflyFirstStackRow
    (amplitude : Rat) (wave : IntegerWavevector) : GaussianRatVector :=
  if wave ∈ butterflyFirstYFaceModes then
    butterflyFirstYFaceRow amplitude wave
  else butterflySeedRow 1 wave

def butterflyFirstStackRationalState
    (amplitude : Rat) : GaussianRatState := fun wave =>
  if wave ∈ butterflyFirstStackModes then
    butterflyFirstStackRow amplitude wave
  else 0

def butterflyFirstStackRationalTangent
    (amplitude : Rat) : GaussianRatState :=
  rationalVorticityGeneratorCoefficientAt butterflyFirstStackModes
    (1 / 100) (butterflyFirstStackRationalState amplitude)

def butterflyFirstStackFreshModes : Finset IntegerWavevector :=
  {axisWave 4, -axisWave 4,
    axisWave 4 + pumpY, axisWave 4 - pumpY,
    -(axisWave 4 + pumpY), -(axisWave 4 - pumpY)}

theorem butterflyFirstStackFreshModes_eq_sdiff :
    butterflyFirstStackFreshModes =
      butterflyFirstStackModes \ butterflySeedModes := by decide

def butterflyFirstStackFreshMass (amplitude : Rat) : Rat :=
  ∑ wave ∈ butterflyFirstStackFreshModes,
    gaussianRatVectorRealInner
      (butterflyFirstStackRationalState amplitude wave)
      (butterflyFirstStackRationalState amplitude wave)

def butterflyFirstStackFreshWork (amplitude : Rat) : Rat :=
  ∑ wave ∈ butterflyFirstStackFreshModes,
    gaussianRatVectorRealInner
      (butterflyFirstStackRationalState amplitude wave)
      (butterflyFirstStackRationalTangent amplitude wave)

/-- Complete signed work of the same finite stacked source.  Unlike the
fresh-face projection, this quantity sees every retained and installed row
of the actual source material. -/
def butterflyFirstStackWholeWork (amplitude : Rat) : Rat :=
  ∑ wave ∈ butterflyFirstStackModes,
    gaussianRatVectorRealInner
      (butterflyFirstStackRationalState amplitude wave)
      (butterflyFirstStackRationalTangent amplitude wave)

theorem butterflyFirstStackFreshMass_eq (amplitude : Rat) :
    butterflyFirstStackFreshMass amplitude =
      (125 / 2) * amplitude ^ 2 := by
  simp (config := { maxSteps := 1000000 })
    [butterflyFirstStackFreshMass, butterflyFirstStackFreshModes,
      butterflyFirstStackModes, butterflyFirstStackRationalState,
      butterflyFirstStackRow, butterflyFirstYFaceModes,
      butterflyFirstYFaceRow, butterflySeedModes, butterflySeedRow,
      butterflyZTwoModes, butterflyZTwoRow,
      sidebandPlusY_eq, sidebandMinusY_eq,
      sidebandPlusZ_eq, sidebandMinusZ_eq,
      gaussianRatVectorRealInner, axisWave, pumpY, pumpZ,
      realRow, realGaussian, Fin.sum_univ_succ,
      Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two] <;> ring

theorem butterflyFirstStackFreshWork_eq (amplitude : Rat) :
    butterflyFirstStackFreshWork amplitude =
      -(48 / 5) * amplitude - (22357 / 3400) * amplitude ^ 2 := by
  have axisPos : (0 : IntegerWavevector) ≠ ![4, 0, 0] := by decide
  have axisNeg : (0 : IntegerWavevector) ≠ ![-4, 0, 0] := by decide
  have plusPos : (0 : IntegerWavevector) ≠ ![4, 1, 0] := by decide
  have plusNeg : (0 : IntegerWavevector) ≠ ![-4, -1, 0] := by decide
  have minusPos : (0 : IntegerWavevector) ≠
      Matrix.vecCons 4 (Matrix.vecCons (-1) 0) := by decide
  have minusNeg : (0 : IntegerWavevector) ≠
      Matrix.vecCons (-4) (Matrix.vecCons 1 0) := by decide
  simp (config := { maxSteps := 10000000 })
    [butterflyFirstStackFreshWork, butterflyFirstStackFreshModes,
      butterflyFirstStackModes, butterflyFirstStackRationalState,
      butterflyFirstStackRationalTangent, butterflyFirstStackRow,
      butterflyFirstYFaceModes, butterflyFirstYFaceRow,
      butterflySeedModes, butterflySeedRow, butterflyZTwoModes,
      butterflyZTwoRow, rationalVorticityGeneratorCoefficientAt,
      rationalVorticityNonlinearCoefficientAt,
      rationalVorticityBilinearCoefficientAt,
      rationalVorticityPairContribution, rationalIntegerWaveNormSq,
      sidebandPlusY_eq, sidebandMinusY_eq,
      sidebandPlusZ_eq, sidebandMinusZ_eq,
      gaussianRatVectorRealInner, axisWave, pumpY, pumpZ,
      realRow, realGaussian, GaussianRatVector.add,
      GaussianRatVector.sub, GaussianRatVector.ratScale,
      GaussianRatVector.waveDot, GaussianRatVector.waveCross,
      GaussianRatVector.tripleWaveCrossDot,
      GaussianRatVector.complexScale, GaussianRat.add,
      GaussianRat.sub, GaussianRat.neg, GaussianRat.mul,
      GaussianRat.ratScale, GaussianRat.intScale,
      GaussianRat.ratDiv, Fin.sum_univ_succ,
      Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, axisPos, axisNeg, plusPos, plusNeg,
      minusPos, minusNeg] <;>
    norm_num [Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two] <;> ring

/-- The complete stacked seed, not only its two paying sidebands or fresh
rows, has a strictly positive exact action valuation. -/
theorem butterflyFirstStackWholeWork_negOne_eq :
    butterflyFirstStackWholeWork (-1) = 627 / 200 := by
  simp (config := { maxSteps := 50000000 }) +decide
    [butterflyFirstStackWholeWork, butterflyFirstStackModes,
      butterflyFirstStackRationalState,
      butterflyFirstStackRationalTangent, butterflyFirstStackRow,
      butterflyFirstYFaceModes, butterflyFirstYFaceRow,
      butterflySeedModes, butterflySeedRow, butterflyZTwoModes,
      butterflyZTwoRow, rationalVorticityGeneratorCoefficientAt,
      rationalVorticityNonlinearCoefficientAt,
      rationalVorticityBilinearCoefficientAt,
      rationalVorticityPairContribution, rationalIntegerWaveNormSq,
      sidebandPlusY_eq, sidebandMinusY_eq,
      sidebandPlusZ_eq, sidebandMinusZ_eq,
      gaussianRatVectorRealInner, axisWave, pumpY, pumpZ,
      realRow, realGaussian, GaussianRatVector.add,
      GaussianRatVector.sub, GaussianRatVector.ratScale,
      GaussianRatVector.waveDot, GaussianRatVector.waveCross,
      GaussianRatVector.tripleWaveCrossDot,
      GaussianRatVector.complexScale, GaussianRat.add,
      GaussianRat.sub, GaussianRat.neg, GaussianRat.mul,
      GaussianRat.ratScale, GaussianRat.intScale,
      GaussianRat.ratDiv, Fin.sum_univ_succ,
      Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two] <;>
    norm_num [Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two]

/-- The actual orientation emitted by the source action gives a strictly
positive fresh-row valuation on an explicit open amplitude cell. -/
theorem butterflyFirstStackFreshWork_pos
    {amplitude : Rat}
    (amplitudeNeg : amplitude < 0)
    (lower : -(32640 / 22357 : Rat) < amplitude) :
    0 < butterflyFirstStackFreshWork amplitude := by
  rw [butterflyFirstStackFreshWork_eq]
  have factorPos :
      0 < (48 / 5 : Rat) + (22357 / 3400) * amplitude := by
    norm_num at lower ⊢
    linarith
  nlinarith

/-! ## Physical valuation of the same stacked material -/

def butterflyFirstStackPhysicalState
    (amplitude : Rat) : ComplexVorticityHilbertState :=
  finiteComplexVorticityState butterflyFirstStackModes fun wave =>
    GaussianRatVector.toComplex (butterflyFirstStackRow amplitude wave)

theorem butterflyFirstStackModes_zeroNotMem :
    (0 : IntegerWavevector) ∉ butterflyFirstStackModes := by decide

theorem butterflyFirstStackPhysicalState_supported
    (amplitude : Rat) (wave : IntegerWavevector)
    (waveNotMem : wave ∉ butterflyFirstStackModes) :
    butterflyFirstStackPhysicalState amplitude wave = 0 := by
  simp [butterflyFirstStackPhysicalState,
    finiteComplexVorticityState_apply, waveNotMem]

theorem butterflyFirstYFaceRow_waveDot_zero
    (amplitude : Rat) (wave : IntegerWavevector)
    (waveMem : wave ∈ butterflyFirstYFaceModes) :
    GaussianRatVector.waveDot wave
      (butterflyFirstYFaceRow amplitude wave) = 0 := by
  simp only [butterflyFirstYFaceModes, Finset.mem_insert,
    Finset.mem_singleton] at waveMem
  rcases waveMem with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    apply GaussianRat.ext <;>
    simp [butterflyFirstYFaceRow, sidebandPlusY_eq,
      sidebandMinusY_eq, axisWave, pumpY, pumpZ, realRow,
      realGaussian, GaussianRatVector.waveDot, GaussianRat.add,
      GaussianRat.ratScale, GaussianRat.intScale,
      Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two] <;>
    ring

theorem butterflyFirstYFaceModes_waveNeg_mem
    (wave : IntegerWavevector)
    (waveMem : wave ∈ butterflyFirstYFaceModes) :
    waveNeg wave ∈ butterflyFirstYFaceModes := by
  simp only [butterflyFirstYFaceModes, Finset.mem_insert,
    Finset.mem_singleton] at waveMem ⊢
  rcases waveMem with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp [axisWave, pumpY, pumpZ, waveNeg]

theorem butterflyFirstYFaceModes_waveNeg_mem_iff
    (wave : IntegerWavevector) :
    waveNeg wave ∈ butterflyFirstYFaceModes ↔
      wave ∈ butterflyFirstYFaceModes := by
  constructor
  · intro negMem
    have generated := butterflyFirstYFaceModes_waveNeg_mem
      (waveNeg wave) negMem
    simpa only [waveNeg_involutive] using generated
  · exact butterflyFirstYFaceModes_waveNeg_mem wave

theorem butterflyFirstYFaceRow_neg_eq
    (amplitude : Rat) (wave : IntegerWavevector)
    (waveMem : wave ∈ butterflyFirstYFaceModes) :
    butterflyFirstYFaceRow amplitude (waveNeg wave) =
      butterflyFirstYFaceRow amplitude wave := by
  simp only [butterflyFirstYFaceModes, Finset.mem_insert,
    Finset.mem_singleton] at waveMem
  rcases waveMem with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    funext coordinate
    fin_cases coordinate <;>
    apply GaussianRat.ext <;>
    simp [butterflyFirstYFaceRow, sidebandPlusY_eq,
      sidebandMinusY_eq, axisWave, pumpY, pumpZ, waveNeg,
      realRow, realGaussian, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two]

theorem butterflyFirstYFaceRow_im_zero
    (amplitude : Rat) (wave : IntegerWavevector)
    (coordinate : Coordinate) :
    (butterflyFirstYFaceRow amplitude wave coordinate).im = 0 := by
  unfold butterflyFirstYFaceRow
  split_ifs <;>
    fin_cases coordinate <;>
    simp [sidebandPlusY_eq, sidebandMinusY_eq,
      realRow, realGaussian, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two]

theorem butterflyFirstStackModes_waveNeg_mem_iff
    (wave : IntegerWavevector) :
    waveNeg wave ∈ butterflyFirstStackModes ↔
      wave ∈ butterflyFirstStackModes := by
  unfold butterflyFirstStackModes
  rw [Finset.mem_union, Finset.mem_union,
    butterflySeedModes_waveNeg_mem_iff,
    butterflyFirstYFaceModes_waveNeg_mem_iff]

theorem butterflyFirstStackRow_waveDot_zero
    (amplitude : Rat) (wave : IntegerWavevector)
    (waveMem : wave ∈ butterflyFirstStackModes) :
    GaussianRatVector.waveDot wave
      (butterflyFirstStackRow amplitude wave) = 0 := by
  by_cases faceMem : wave ∈ butterflyFirstYFaceModes
  · rw [butterflyFirstStackRow, if_pos faceMem]
    exact butterflyFirstYFaceRow_waveDot_zero amplitude wave faceMem
  · have seedMem : wave ∈ butterflySeedModes :=
      (Finset.mem_union.mp waveMem).resolve_right faceMem
    rw [butterflyFirstStackRow, if_neg faceMem]
    exact butterflySeedRow_waveDot_zero 1 wave seedMem

theorem butterflyFirstStackRow_neg_eq
    (amplitude : Rat) (wave : IntegerWavevector)
    (waveMem : wave ∈ butterflyFirstStackModes) :
    butterflyFirstStackRow amplitude (waveNeg wave) =
      butterflyFirstStackRow amplitude wave := by
  by_cases faceMem : wave ∈ butterflyFirstYFaceModes
  · have negFaceMem :=
      (butterflyFirstYFaceModes_waveNeg_mem_iff wave).2 faceMem
    rw [butterflyFirstStackRow, if_pos negFaceMem,
      butterflyFirstStackRow, if_pos faceMem]
    exact butterflyFirstYFaceRow_neg_eq amplitude wave faceMem
  · have seedMem : wave ∈ butterflySeedModes :=
      (Finset.mem_union.mp waveMem).resolve_right faceMem
    have negFaceNotMem : waveNeg wave ∉ butterflyFirstYFaceModes := by
      simpa only [butterflyFirstYFaceModes_waveNeg_mem_iff] using faceMem
    rw [butterflyFirstStackRow, if_neg negFaceNotMem,
      butterflyFirstStackRow, if_neg faceMem]
    exact butterflySeedRow_neg_eq 1 wave seedMem

theorem butterflyFirstStackRow_im_zero
    (amplitude : Rat) (wave : IntegerWavevector)
    (coordinate : Coordinate) :
    (butterflyFirstStackRow amplitude wave coordinate).im = 0 := by
  by_cases faceMem : wave ∈ butterflyFirstYFaceModes
  · rw [butterflyFirstStackRow, if_pos faceMem]
    exact butterflyFirstYFaceRow_im_zero amplitude wave coordinate
  · rw [butterflyFirstStackRow, if_neg faceMem]
    exact butterflySeedRow_im_zero 1 wave coordinate

theorem butterflyFirstStackPhysicalState_zero
    (amplitude : Rat) :
    butterflyFirstStackPhysicalState amplitude 0 = 0 :=
  butterflyFirstStackPhysicalState_supported amplitude 0
    butterflyFirstStackModes_zeroNotMem

theorem butterflyFirstStackPhysicalState_transverse
    (amplitude : Rat) :
    WholeStateTransverse (butterflyFirstStackPhysicalState amplitude) := by
  intro wave
  by_cases waveMem : wave ∈ butterflyFirstStackModes
  · unfold butterflyFirstStackPhysicalState
    rw [finiteComplexVorticityState_apply, if_pos waveMem]
    rw [← GaussianRatVector.toComplex_waveDot,
      butterflyFirstStackRow_waveDot_zero amplitude wave waveMem]
    exact GaussianRat.toComplex_zero
  · rw [butterflyFirstStackPhysicalState_supported amplitude wave waveMem,
      dotProduct_zero]

theorem butterflyFirstStackPhysicalState_reality
    (amplitude : Rat) :
    FiniteStateFourierReality
      (butterflyFirstStackPhysicalState amplitude) := by
  intro wave
  by_cases waveMem : wave ∈ butterflyFirstStackModes
  · have negMem :=
      (butterflyFirstStackModes_waveNeg_mem_iff wave).2 waveMem
    unfold butterflyFirstStackPhysicalState
    rw [finiteComplexVorticityState_apply, if_pos negMem,
      finiteComplexVorticityState_apply, if_pos waveMem,
      butterflyFirstStackRow_neg_eq amplitude wave waveMem]
    funext coordinate
    change GaussianRat.toComplex
        (butterflyFirstStackRow amplitude wave coordinate) =
      star (GaussianRat.toComplex
        (butterflyFirstStackRow amplitude wave coordinate))
    unfold GaussianRat.toComplex
    rw [butterflyFirstStackRow_im_zero amplitude wave coordinate]
    simp
  · have negNotMem : waveNeg wave ∉ butterflyFirstStackModes := by
      simpa only [butterflyFirstStackModes_waveNeg_mem_iff] using waveMem
    rw [butterflyFirstStackPhysicalState_supported amplitude _ negNotMem,
      butterflyFirstStackPhysicalState_supported amplitude _ waveMem]
    exact vectorConj_zero.symm

/-- The first stacked source is a literal half-integral mass cell.  Its raw
restart ceiling is therefore separated from the next integer wall. -/
theorem butterflyFirstStackPhysicalState_negOne_mass_eq :
    wholeVorticityEuclideanMass
      (butterflyFirstStackPhysicalState (-1)) = 173 / 2 := by
  rw [wholeVorticityEuclideanMass_eq_finite_of_supported
    butterflyFirstStackModes
    (butterflyFirstStackPhysicalState (-1))
    (butterflyFirstStackPhysicalState_supported (-1))]
  unfold finiteStateVorticityCoefficientEnstrophy
  simp (config := { maxSteps := 2000000 })
    [butterflyFirstStackPhysicalState,
      finiteComplexVorticityState_apply, butterflyFirstStackModes,
      butterflyFirstStackRow, butterflyFirstYFaceModes,
      butterflyFirstYFaceRow, butterflySeedModes, butterflySeedRow,
      butterflyZTwoModes, butterflyZTwoRow, sidebandPlusY_eq,
      sidebandMinusY_eq, sidebandPlusZ_eq, sidebandMinusZ_eq,
      complexCoordinateAmplitudeSq, axisWave, pumpY, pumpZ,
      realRow, realGaussian, GaussianRatVector.toComplex,
      GaussianRat.toComplex, Fin.sum_univ_succ,
      Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two] <;>
    norm_num [Complex.normSq_apply] <;> ring

theorem butterflyFirstStackPhysicalState_negOne_sideband_mass_eq
    (wave : IntegerWavevector)
    (waveEq : wave = axisWave 4 + pumpY ∨
      wave = axisWave 4 - pumpY) :
    complexCoordinateAmplitudeSq
        (butterflyFirstStackPhysicalState (-1) wave) = 121 / 8 := by
  rcases waveEq with rfl | rfl <;>
    simp (config := { maxSteps := 100000 })
      [butterflyFirstStackPhysicalState,
        finiteComplexVorticityState_apply, butterflyFirstStackModes,
        butterflyFirstStackRow, butterflyFirstYFaceModes,
        butterflyFirstYFaceRow, sidebandPlusY_eq,
        sidebandMinusY_eq, butterflySeedModes, butterflyZTwoModes,
        axisWave, pumpY, pumpZ, complexCoordinateAmplitudeSq,
        realRow, realGaussian, GaussianRatVector.toComplex,
        GaussianRat.toComplex, Fin.sum_univ_succ,
        Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, Complex.normSq_apply] <;>
    norm_num <;> ring

theorem butterflyFirstStackRationalState_toComplex
    (amplitude : Rat) (wave : IntegerWavevector) :
    GaussianRatVector.toComplex
        (butterflyFirstStackRationalState amplitude wave) =
      butterflyFirstStackPhysicalState amplitude wave := by
  by_cases waveMem : wave ∈ butterflyFirstStackModes
  · simp [butterflyFirstStackRationalState,
      butterflyFirstStackPhysicalState,
      finiteComplexVorticityState_apply, waveMem]
  · simp [butterflyFirstStackRationalState,
      butterflyFirstStackPhysicalState,
      finiteComplexVorticityState_apply, waveMem]

theorem butterflyFirstStackRationalTangent_toComplex
    (amplitude : Rat) (wave : IntegerWavevector) :
    GaussianRatVector.toComplex
        (butterflyFirstStackRationalTangent amplitude wave) =
      finiteStateVorticityNonlinearCoefficientAt
          butterflyFirstStackModes
          (butterflyFirstStackPhysicalState amplitude) wave -
        (butterflyGainViscosity.coeff *
          integerWaveViscousMultiplier wave) •
            butterflyFirstStackPhysicalState amplitude wave := by
  apply rationalVorticityGeneratorCoefficientAt_toComplex
    butterflyFirstStackModes (1 / 100)
      (butterflyFirstStackRationalState amplitude)
      (butterflyFirstStackPhysicalState amplitude) wave
      butterflyGainViscosity.coeff
      butterflyFirstStackModes_zeroNotMem
  · intro actual _actualMem
    exact butterflyFirstStackRationalState_toComplex amplitude actual
  · exact butterflyFirstStackRationalState_toComplex amplitude wave
  · exact butterflyGainViscosity_scaled

/-- Each oriented top sideband, not merely their sum, has strict positive
whole-NS work on the exact stacked source. -/
theorem butterflyFirstStackPhysicalState_negOne_sideband_work_eq
    (wave : IntegerWavevector)
    (waveEq : wave = axisWave 4 + pumpY ∨
      wave = axisWave 4 - pumpY) :
    complexCoordinateRealInner
        (butterflyFirstStackPhysicalState (-1) wave)
        (wholeLatticeVorticityFourierTangentAt
          butterflyGainViscosity.coeff
          (butterflyFirstStackPhysicalState (-1)) wave) =
      10043 / 800 := by
  have tangentEq :
      wholeLatticeVorticityFourierTangentAt
          butterflyGainViscosity.coeff
          (butterflyFirstStackPhysicalState (-1)) wave =
        GaussianRatVector.toComplex
          (butterflyFirstStackRationalTangent (-1) wave) := by
    unfold wholeLatticeVorticityFourierTangentAt
    rw [wholeStateVorticityNonlinearCoefficientAt_eq_finite_of_supported
      butterflyFirstStackModes
      (butterflyFirstStackPhysicalState (-1))
      (butterflyFirstStackPhysicalState_supported (-1)) wave]
    exact (butterflyFirstStackRationalTangent_toComplex (-1) wave).symm
  rw [tangentEq, ← butterflyFirstStackRationalState_toComplex,
    complexCoordinateRealInner_gaussianRat_toComplex]
  rcases waveEq with rfl | rfl <;>
    simp (config := { maxSteps := 1000000 })
      [butterflyFirstStackRationalState,
        butterflyFirstStackRationalTangent,
        butterflyFirstStackModes, butterflyFirstStackRow,
        butterflyFirstYFaceModes, butterflyFirstYFaceRow,
        butterflySeedModes, butterflySeedRow, butterflyZTwoModes,
        butterflyZTwoRow, rationalVorticityGeneratorCoefficientAt,
        rationalVorticityNonlinearCoefficientAt,
        rationalVorticityBilinearCoefficientAt,
        rationalVorticityPairContribution, rationalIntegerWaveNormSq,
        sidebandPlusY_eq, sidebandMinusY_eq,
        sidebandPlusZ_eq, sidebandMinusZ_eq,
        gaussianRatVectorRealInner, axisWave, pumpY, pumpZ,
        realRow, realGaussian, GaussianRatVector.add,
        GaussianRatVector.sub, GaussianRatVector.ratScale,
        GaussianRatVector.waveDot, GaussianRatVector.waveCross,
        GaussianRatVector.tripleWaveCrossDot,
        GaussianRatVector.complexScale, GaussianRat.add,
        GaussianRat.sub, GaussianRat.neg, GaussianRat.mul,
        GaussianRat.ratScale, GaussianRat.intScale,
        GaussianRat.ratDiv, Fin.sum_univ_succ,
        Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two] <;>
    norm_num <;> ring

/-- The rational fresh-row polynomial is exactly the finite physical work
of the same stacked state and viscosity. -/
theorem butterflyFirstStackFreshPhysicalWork_eq
    (amplitude : Rat) :
    (∑ wave ∈ butterflyFirstStackFreshModes,
      complexCoordinateRealInner
        (butterflyFirstStackPhysicalState amplitude wave)
        (finiteStateVorticityNonlinearCoefficientAt
              butterflyFirstStackModes
              (butterflyFirstStackPhysicalState amplitude) wave -
          (butterflyGainViscosity.coeff *
            integerWaveViscousMultiplier wave) •
              butterflyFirstStackPhysicalState amplitude wave)) =
      (butterflyFirstStackFreshWork amplitude : Real) := by
  unfold butterflyFirstStackFreshWork
  rw [Rat.cast_sum]
  apply Finset.sum_congr rfl
  intro wave _waveMem
  rw [← butterflyFirstStackRationalTangent_toComplex amplitude wave,
    ← butterflyFirstStackRationalState_toComplex amplitude wave,
    complexCoordinateRealInner_gaussianRat_toComplex]

/-- Exact physical realization of the complete rational work row. -/
theorem butterflyFirstStackPhysicalWholeWork_eq
    (amplitude : Rat) :
    (∑ wave ∈ butterflyFirstStackModes,
      complexCoordinateRealInner
        (butterflyFirstStackPhysicalState amplitude wave)
        (wholeLatticeVorticityFourierTangentAt
          butterflyGainViscosity.coeff
          (butterflyFirstStackPhysicalState amplitude) wave)) =
      (butterflyFirstStackWholeWork amplitude : Real) := by
  rw [butterflyFirstStackWholeWork, Rat.cast_sum]
  apply Finset.sum_congr rfl
  intro wave _waveMem
  unfold wholeLatticeVorticityFourierTangentAt
  rw [wholeStateVorticityNonlinearCoefficientAt_eq_finite_of_supported
    butterflyFirstStackModes
    (butterflyFirstStackPhysicalState amplitude)
    (butterflyFirstStackPhysicalState_supported amplitude) wave]
  rw [← butterflyFirstStackRationalTangent_toComplex amplitude wave,
    ← butterflyFirstStackRationalState_toComplex amplitude wave,
    complexCoordinateRealInner_gaussianRat_toComplex]

/-- Complete instantaneous projected net power of the exact stacked seed.
This rules out cancellation by retained rows at the source occurrence. -/
theorem butterflyFirstStackPhysicalWholeNetPower_negOne_eq :
    (∑ wave ∈ butterflyFirstStackModes,
      instantaneousWholeNetPowerRow butterflyGainViscosity
        (butterflyFirstStackPhysicalState (-1)) wave) = 627 / 100 := by
  have finiteEq := butterflyFirstStackPhysicalWholeWork_eq (-1)
  rw [butterflyFirstStackWholeWork_negOne_eq] at finiteEq
  have rowEq : ∀ wave ∈ butterflyFirstStackModes,
      instantaneousWholeNetPowerRow butterflyGainViscosity
          (butterflyFirstStackPhysicalState (-1)) wave =
        2 * complexCoordinateRealInner
          (butterflyFirstStackPhysicalState (-1) wave)
          (wholeLatticeVorticityFourierTangentAt
            butterflyGainViscosity.coeff
            (butterflyFirstStackPhysicalState (-1)) wave) := by
    intro wave _waveMem
    unfold instantaneousWholeNetPowerRow
      wholeLatticeVorticityFourierTangentAt
    rw [complexCoordinateRealInner_sub_right]
    ring
  rw [Finset.sum_congr rfl rowEq, ← Finset.mul_sum, finiteEq]
  norm_num

/-- Hence the source-oriented amplitude cell gives positive *actual
physical* fresh-row net power.  This is the valuation required by the
inventory-expansion seam. -/
theorem butterflyFirstStackFreshPhysicalNetPower_pos
    {amplitude : Rat}
    (amplitudeNeg : amplitude < 0)
    (lower : -(32640 / 22357 : Rat) < amplitude) :
    0 < ∑ wave ∈ butterflyFirstStackFreshModes,
      instantaneousWholeNetPowerRow butterflyGainViscosity
        (butterflyFirstStackPhysicalState amplitude) wave := by
  have finitePositive :
      0 < (butterflyFirstStackFreshWork amplitude : Real) := by
    exact_mod_cast butterflyFirstStackFreshWork_pos amplitudeNeg lower
  have finiteEq := butterflyFirstStackFreshPhysicalWork_eq amplitude
  have rowEq : ∀ wave ∈ butterflyFirstStackFreshModes,
      instantaneousWholeNetPowerRow butterflyGainViscosity
          (butterflyFirstStackPhysicalState amplitude) wave =
        2 * complexCoordinateRealInner
          (butterflyFirstStackPhysicalState amplitude wave)
          (finiteStateVorticityNonlinearCoefficientAt
                butterflyFirstStackModes
                (butterflyFirstStackPhysicalState amplitude) wave -
            (butterflyGainViscosity.coeff *
              integerWaveViscousMultiplier wave) •
                butterflyFirstStackPhysicalState amplitude wave) := by
    intro wave _waveMem
    unfold instantaneousWholeNetPowerRow
    rw [wholeStateVorticityNonlinearCoefficientAt_eq_finite_of_supported
      butterflyFirstStackModes
      (butterflyFirstStackPhysicalState amplitude)
      (butterflyFirstStackPhysicalState_supported amplitude) wave]
    rw [complexCoordinateRealInner_sub_right]
    ring
  rw [Finset.sum_congr rfl rowEq]
  rw [← Finset.mul_sum, finiteEq]
  linarith

/-! ## First source-generated dyadic output -/

def butterflyFirstStackAxisEight : IntegerWavevector := axisWave 8

theorem butterflyFirstStackAxisEight_not_mem :
    butterflyFirstStackAxisEight ∉ butterflyFirstStackModes := by
  decide

@[simp] theorem butterflyFirstStackPhysicalState_negOne_axisEight_zero :
    butterflyFirstStackPhysicalState (-1) butterflyFirstStackAxisEight = 0 :=
  butterflyFirstStackPhysicalState_supported (-1)
    butterflyFirstStackAxisEight butterflyFirstStackAxisEight_not_mem

theorem butterflyFirstStackRationalTangent_negOne_axisEight_eq :
    butterflyFirstStackRationalTangent (-1) butterflyFirstStackAxisEight =
      realRow 0 (120 / 17) 0 := by
  have outputNe : (0 : IntegerWavevector) ≠ ![8, 0, 0] := by decide
  funext coordinate
  fin_cases coordinate
  all_goals apply GaussianRat.ext
  all_goals
    simp (config := { maxSteps := 10000000 })
      [butterflyFirstStackRationalTangent, butterflyFirstStackAxisEight,
        butterflyFirstStackModes, butterflyFirstStackRationalState,
        butterflyFirstStackRow, butterflyFirstYFaceModes,
        butterflyFirstYFaceRow, butterflySeedModes, butterflySeedRow,
        butterflyZTwoModes, butterflyZTwoRow,
        rationalVorticityGeneratorCoefficientAt,
        rationalVorticityNonlinearCoefficientAt,
        rationalVorticityBilinearCoefficientAt,
        rationalVorticityPairContribution, rationalIntegerWaveNormSq,
        sidebandPlusY_eq, sidebandMinusY_eq,
        sidebandPlusZ_eq, sidebandMinusZ_eq,
        axisWave, pumpY, pumpZ, realRow, realGaussian,
        GaussianRatVector.add, GaussianRatVector.sub,
        GaussianRatVector.ratScale, GaussianRatVector.waveDot,
        GaussianRatVector.waveCross,
        GaussianRatVector.tripleWaveCrossDot,
        GaussianRatVector.complexScale, GaussianRat.add,
        GaussianRat.sub, GaussianRat.neg, GaussianRat.mul,
        GaussianRat.ratScale, GaussianRat.intScale,
        GaussianRat.ratDiv, Fin.sum_univ_succ,
        Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, outputNe] <;>
      norm_num [Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two] <;> ring

theorem butterflyFirstStackPhysicalTangent_negOne_axisEight_eq :
    wholeLatticeVorticityFourierTangentAt
        butterflyGainViscosity.coeff
        (butterflyFirstStackPhysicalState (-1))
        butterflyFirstStackAxisEight =
      GaussianRatVector.toComplex (realRow 0 (120 / 17) 0) := by
  unfold wholeLatticeVorticityFourierTangentAt
  rw [wholeStateVorticityNonlinearCoefficientAt_eq_finite_of_supported
    butterflyFirstStackModes
    (butterflyFirstStackPhysicalState (-1))
    (butterflyFirstStackPhysicalState_supported (-1))
    butterflyFirstStackAxisEight]
  rw [← butterflyFirstStackRationalTangent_toComplex (-1)
      butterflyFirstStackAxisEight,
    butterflyFirstStackRationalTangent_negOne_axisEight_eq]

theorem butterflyFirstStackPhysicalTangent_negOne_axisEight_norm_ge :
    (120 / 17 : Real) ≤
      ‖wholeLatticeVorticityFourierTangentAt
        butterflyGainViscosity.coeff
        (butterflyFirstStackPhysicalState (-1))
        butterflyFirstStackAxisEight‖ := by
  rw [butterflyFirstStackPhysicalTangent_negOne_axisEight_eq]
  have coordinateLe := norm_le_pi_norm
    (GaussianRatVector.toComplex (realRow 0 (120 / 17) 0)) 1
  norm_num [realRow, realGaussian, GaussianRatVector.toComplex,
    GaussianRat.toComplex, Matrix.cons_val_one] at coordinateLe ⊢
  exact coordinateLe

def butterflyFirstStackAxisEightPlusY : IntegerWavevector :=
  axisWave 8 + pumpY

def butterflyFirstStackAxisEightMinusY : IntegerWavevector :=
  axisWave 8 - pumpY

/-- The complete first renewal face emitted by the same stacked action. -/
def butterflyFirstStackChildFaceModes : Finset IntegerWavevector :=
  {butterflyFirstStackAxisEight,
    butterflyFirstStackAxisEightPlusY,
    butterflyFirstStackAxisEightMinusY}

theorem butterflyFirstStackAxisEightPlusY_not_mem :
    butterflyFirstStackAxisEightPlusY ∉ butterflyFirstStackModes := by
  decide

theorem butterflyFirstStackAxisEightMinusY_not_mem :
    butterflyFirstStackAxisEightMinusY ∉ butterflyFirstStackModes := by
  decide

@[simp] theorem butterflyFirstStackPhysicalState_negOne_axisEightPlusY_zero :
    butterflyFirstStackPhysicalState (-1)
        butterflyFirstStackAxisEightPlusY = 0 :=
  butterflyFirstStackPhysicalState_supported (-1)
    butterflyFirstStackAxisEightPlusY
    butterflyFirstStackAxisEightPlusY_not_mem

@[simp] theorem butterflyFirstStackPhysicalState_negOne_axisEightMinusY_zero :
    butterflyFirstStackPhysicalState (-1)
        butterflyFirstStackAxisEightMinusY = 0 :=
  butterflyFirstStackPhysicalState_supported (-1)
    butterflyFirstStackAxisEightMinusY
    butterflyFirstStackAxisEightMinusY_not_mem

/-- The same finite parent action emits the positive child sideband; this is
an exact row of the complete stacked convolution, not a pair-only proxy. -/
theorem butterflyFirstStackRationalTangent_negOne_axisEightPlusY_eq :
    butterflyFirstStackRationalTangent (-1)
        butterflyFirstStackAxisEightPlusY =
      realRow (1 / 16) (-1 / 2) (-15 / 272) := by
  have outputNe : (0 : IntegerWavevector) ≠ ![8, 1, 0] := by decide
  funext coordinate
  fin_cases coordinate
  all_goals apply GaussianRat.ext
  all_goals
    simp (config := { maxSteps := 10000000 })
      [butterflyFirstStackRationalTangent,
        butterflyFirstStackAxisEightPlusY,
        butterflyFirstStackModes, butterflyFirstStackRationalState,
        butterflyFirstStackRow, butterflyFirstYFaceModes,
        butterflyFirstYFaceRow, butterflySeedModes, butterflySeedRow,
        butterflyZTwoModes, butterflyZTwoRow,
        rationalVorticityGeneratorCoefficientAt,
        rationalVorticityNonlinearCoefficientAt,
        rationalVorticityBilinearCoefficientAt,
        rationalVorticityPairContribution, rationalIntegerWaveNormSq,
        sidebandPlusY_eq, sidebandMinusY_eq,
        sidebandPlusZ_eq, sidebandMinusZ_eq,
        axisWave, pumpY, pumpZ, realRow, realGaussian,
        GaussianRatVector.add, GaussianRatVector.sub,
        GaussianRatVector.ratScale, GaussianRatVector.waveDot,
        GaussianRatVector.waveCross,
        GaussianRatVector.tripleWaveCrossDot,
        GaussianRatVector.complexScale, GaussianRat.add,
        GaussianRat.sub, GaussianRat.neg, GaussianRat.mul,
        GaussianRat.ratScale, GaussianRat.intScale,
        GaussianRat.ratDiv, Fin.sum_univ_succ,
        Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, outputNe] <;>
      norm_num [Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two] <;> ring

/-- The reflected child sideband is emitted on the same complete action. -/
theorem butterflyFirstStackRationalTangent_negOne_axisEightMinusY_eq :
    butterflyFirstStackRationalTangent (-1)
        butterflyFirstStackAxisEightMinusY =
      realRow (1 / 16) (1 / 2) (-15 / 272) := by
  have outputNe : (0 : IntegerWavevector) ≠ ![8, -1, 0] := by decide
  funext coordinate
  fin_cases coordinate
  all_goals apply GaussianRat.ext
  all_goals
    simp (config := { maxSteps := 10000000 })
      [butterflyFirstStackRationalTangent,
        butterflyFirstStackAxisEightMinusY,
        butterflyFirstStackModes, butterflyFirstStackRationalState,
        butterflyFirstStackRow, butterflyFirstYFaceModes,
        butterflyFirstYFaceRow, butterflySeedModes, butterflySeedRow,
        butterflyZTwoModes, butterflyZTwoRow,
        rationalVorticityGeneratorCoefficientAt,
        rationalVorticityNonlinearCoefficientAt,
        rationalVorticityBilinearCoefficientAt,
        rationalVorticityPairContribution, rationalIntegerWaveNormSq,
        sidebandPlusY_eq, sidebandMinusY_eq,
        sidebandPlusZ_eq, sidebandMinusZ_eq,
        axisWave, pumpY, pumpZ, realRow, realGaussian,
        GaussianRatVector.add, GaussianRatVector.sub,
        GaussianRatVector.ratScale, GaussianRatVector.waveDot,
        GaussianRatVector.waveCross,
        GaussianRatVector.tripleWaveCrossDot,
        GaussianRatVector.complexScale, GaussianRat.add,
        GaussianRat.sub, GaussianRat.neg, GaussianRat.mul,
        GaussianRat.ratScale, GaussianRat.intScale,
        GaussianRat.ratDiv, Fin.sum_univ_succ,
        Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, outputNe] <;>
      norm_num [Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two] <;> ring

theorem butterflyFirstStackPhysicalTangent_negOne_axisEightPlusY_eq :
    wholeLatticeVorticityFourierTangentAt
        butterflyGainViscosity.coeff
        (butterflyFirstStackPhysicalState (-1))
        butterflyFirstStackAxisEightPlusY =
      GaussianRatVector.toComplex
        (realRow (1 / 16) (-1 / 2) (-15 / 272)) := by
  unfold wholeLatticeVorticityFourierTangentAt
  rw [wholeStateVorticityNonlinearCoefficientAt_eq_finite_of_supported
    butterflyFirstStackModes
    (butterflyFirstStackPhysicalState (-1))
    (butterflyFirstStackPhysicalState_supported (-1))
    butterflyFirstStackAxisEightPlusY]
  rw [← butterflyFirstStackRationalTangent_toComplex (-1)
      butterflyFirstStackAxisEightPlusY,
    butterflyFirstStackRationalTangent_negOne_axisEightPlusY_eq]

theorem butterflyFirstStackPhysicalTangent_negOne_axisEightMinusY_eq :
    wholeLatticeVorticityFourierTangentAt
        butterflyGainViscosity.coeff
        (butterflyFirstStackPhysicalState (-1))
        butterflyFirstStackAxisEightMinusY =
      GaussianRatVector.toComplex
        (realRow (1 / 16) (1 / 2) (-15 / 272)) := by
  unfold wholeLatticeVorticityFourierTangentAt
  rw [wholeStateVorticityNonlinearCoefficientAt_eq_finite_of_supported
    butterflyFirstStackModes
    (butterflyFirstStackPhysicalState (-1))
    (butterflyFirstStackPhysicalState_supported (-1))
    butterflyFirstStackAxisEightMinusY]
  rw [← butterflyFirstStackRationalTangent_toComplex (-1)
      butterflyFirstStackAxisEightMinusY,
    butterflyFirstStackRationalTangent_negOne_axisEightMinusY_eq]

/-- First source-generated renewal face: the axis and both reflected
sidebands are emitted together by the complete parent action. -/
theorem butterflyFirstStackPhysicalTangent_childFace :
    wholeLatticeVorticityFourierTangentAt
          butterflyGainViscosity.coeff
          (butterflyFirstStackPhysicalState (-1))
          butterflyFirstStackAxisEight =
        GaussianRatVector.toComplex (realRow 0 (120 / 17) 0) ∧
      wholeLatticeVorticityFourierTangentAt
          butterflyGainViscosity.coeff
          (butterflyFirstStackPhysicalState (-1))
          butterflyFirstStackAxisEightPlusY =
        GaussianRatVector.toComplex
          (realRow (1 / 16) (-1 / 2) (-15 / 272)) ∧
      wholeLatticeVorticityFourierTangentAt
          butterflyGainViscosity.coeff
          (butterflyFirstStackPhysicalState (-1))
          butterflyFirstStackAxisEightMinusY =
        GaussianRatVector.toComplex
          (realRow (1 / 16) (1 / 2) (-15 / 272)) :=
  ⟨butterflyFirstStackPhysicalTangent_negOne_axisEight_eq,
    butterflyFirstStackPhysicalTangent_negOne_axisEightPlusY_eq,
    butterflyFirstStackPhysicalTangent_negOne_axisEightMinusY_eq⟩

end
end ButterflyStackedExpansionMaterial
end RationalVorticityEvaluator
end NavierStokes
end SaturationMonoid
