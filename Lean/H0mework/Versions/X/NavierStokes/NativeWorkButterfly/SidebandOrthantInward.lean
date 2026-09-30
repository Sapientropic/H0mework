import H0mework.Versions.X.NavierStokes.Butterfly.StackedExpansionMaterial

/-!
# Action-closed oriented butterfly sideband cell

The two source half-spaces alone are not recurrence-faithful.  On the
transverse four-coordinate sideband cell, however, the complete finite
Navier--Stokes action has four exact affine coordinate rows.  Every oriented
orthant wall is strictly inward and the desired doubled-axis pair is then
strictly positive.  These are parametric cell laws; transport from an actual
whole current still has to pay the complementary action residual.
-/

set_option autoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 100000

open scoped BigOperators Matrix

namespace SaturationMonoid
namespace NavierStokes
namespace RationalVorticityEvaluator
namespace ButterflySidebandOrthantInward

open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ButterflyStackedExpansionMaterial

def plusWave : IntegerWavevector := axisWave 4 + pumpY
def minusWave : IntegerWavevector := axisWave 4 - pumpY

def conePlusRow (x z : Rat) : GaussianRatVector :=
  realRow x (-4 * x) z

def coneMinusRow (y w : Rat) : GaussianRatVector :=
  realRow y (4 * y) w

/-- The entire old stacked carrier is retained; only the four real
transverse sideband coordinates vary. -/
def coneState (x z y w : Rat) : GaussianRatState := fun wave =>
  if wave = plusWave ∨ wave = -plusWave then conePlusRow x z
  else if wave = minusWave ∨ wave = -minusWave then coneMinusRow y w
  else butterflyFirstStackRationalState (-1) wave

/-- The rational source is the interior point of the oriented four-cell.
This equality is the source provenance for the affine action below. -/
theorem coneState_source_eq :
    coneState (1 / 4) (-(15 / 4)) (-(1 / 4)) (15 / 4) =
      butterflyFirstStackRationalState (-1) := by
  funext wave
  unfold coneState
  by_cases plus : wave = plusWave ∨ wave = -plusWave
  · rw [if_pos plus]
    rcases plus with rfl | rfl <;>
      simp [conePlusRow, plusWave, butterflyFirstStackRationalState,
        butterflyFirstStackModes, butterflyFirstStackRow,
        butterflyFirstYFaceModes, butterflyFirstYFaceRow,
        sidebandPlusY_eq, sidebandMinusY_eq, axisWave, pumpY, pumpZ,
        realRow, realGaussian, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_two] <;>
      norm_num
  · rw [if_neg plus]
    by_cases minus : wave = minusWave ∨ wave = -minusWave
    · rw [if_pos minus]
      rcases minus with rfl | rfl <;>
        simp [coneMinusRow, minusWave, butterflyFirstStackRationalState,
          butterflyFirstStackModes, butterflyFirstStackRow,
          butterflyFirstYFaceModes, butterflyFirstYFaceRow,
          sidebandPlusY_eq, sidebandMinusY_eq, axisWave, pumpY, pumpZ,
          realRow, realGaussian, Matrix.cons_val_zero,
          Matrix.cons_val_one, Matrix.cons_val_two] <;>
        norm_num
    · rw [if_neg minus]

def coneAction (x z y w : Rat) : GaussianRatState :=
  rationalVorticityGeneratorCoefficientAt butterflyFirstStackModes
    (1 / 100) (coneState x z y w)

def conePlusActionRow (x z : Rat) : GaussianRatVector :=
  conePlusRow (1 / 4 - (17 / 100) * x)
    (-(15 / 4) - (17 / 100) * z)

def coneMinusActionRow (y w : Rat) : GaussianRatVector :=
  coneMinusRow (-(1 / 4) - (17 / 100) * y)
    (15 / 4 - (17 / 100) * w)

private theorem coneAction_plus_eq_raw (x z y w : Rat) :
    coneAction x z y w plusWave = conePlusActionRow x z := by
  funext coordinate
  fin_cases coordinate <;>
    apply GaussianRat.ext <;>
    simp (config := { maxSteps := 50000000 })
      [coneAction, coneState, conePlusActionRow, conePlusRow, coneMinusRow,
        plusWave, minusWave, butterflyFirstStackModes,
        butterflyFirstStackRationalState, butterflyFirstStackRow,
        butterflyFirstYFaceModes, butterflyFirstYFaceRow,
        butterflySeedModes, butterflySeedRow, butterflyZTwoModes,
        butterflyZTwoRow, rationalVorticityGeneratorCoefficientAt,
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
        Matrix.cons_val_two] <;>
    ring

private theorem coneAction_minus_eq_raw (x z y w : Rat) :
    coneAction x z y w minusWave = coneMinusActionRow y w := by
  funext coordinate
  fin_cases coordinate <;>
    apply GaussianRat.ext <;>
    simp (config := { maxSteps := 50000000 })
      [coneAction, coneState, coneMinusActionRow, conePlusRow, coneMinusRow,
        plusWave, minusWave, butterflyFirstStackModes,
        butterflyFirstStackRationalState, butterflyFirstStackRow,
        butterflyFirstYFaceModes, butterflyFirstYFaceRow,
        butterflySeedModes, butterflySeedRow, butterflyZTwoModes,
        butterflyZTwoRow, rationalVorticityGeneratorCoefficientAt,
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
        Matrix.cons_val_two] <;>
    ring

/-- Complete finite action on the positive sideband is the source forcing
plus diagonal viscous relaxation; the opposite sideband coordinates do not
enter. -/
theorem coneAction_plus_eq (x z y w : Rat) :
    coneAction x z y w plusWave = conePlusActionRow x z :=
  coneAction_plus_eq_raw x z y w

/-- The negative sideband has the reflected affine law. -/
theorem coneAction_minus_eq (x z y w : Rat) :
    coneAction x z y w minusWave = coneMinusActionRow y w :=
  coneAction_minus_eq_raw x z y w

def exactPlusRow : GaussianRatVector :=
  butterflyFirstStackRationalState (-1) plusWave

def exactMinusRow : GaussianRatVector :=
  butterflyFirstStackRationalState (-1) minusWave

def plusReserve (x z : Rat) : Rat :=
  gaussianRatVectorRealInner exactPlusRow (conePlusRow x z)

def minusReserve (y w : Rat) : Rat :=
  gaussianRatVectorRealInner exactMinusRow (coneMinusRow y w)

def plusReserveJet (x z y w : Rat) : Rat :=
  gaussianRatVectorRealInner exactPlusRow
    (coneAction x z y w plusWave)

def minusReserveJet (x z y w : Rat) : Rat :=
  gaussianRatVectorRealInner exactMinusRow
    (coneAction x z y w minusWave)

theorem plusReserve_eq (x z : Rat) :
    plusReserve x z = (17 / 4) * x - (15 / 4) * z := by
  simp [plusReserve, exactPlusRow, plusWave, conePlusRow,
    butterflyFirstStackRationalState, butterflyFirstStackModes,
    butterflyFirstStackRow, butterflyFirstYFaceModes,
    butterflyFirstYFaceRow, butterflySeedModes, butterflySeedRow,
    butterflyZTwoModes, butterflyZTwoRow, sidebandPlusY_eq,
    sidebandMinusY_eq, sidebandPlusZ_eq, sidebandMinusZ_eq,
    gaussianRatVectorRealInner, axisWave, pumpY, pumpZ, realRow,
    realGaussian, GaussianRat.add, GaussianRat.sub, GaussianRat.neg,
    GaussianRat.mul, GaussianRat.ratScale, GaussianRat.intScale,
    GaussianRat.ratDiv, Fin.sum_univ_succ, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two] <;>
  ring

theorem minusReserve_eq (y w : Rat) :
    minusReserve y w = -(17 / 4) * y + (15 / 4) * w := by
  simp [minusReserve, exactMinusRow, minusWave, coneMinusRow,
    butterflyFirstStackRationalState, butterflyFirstStackModes,
    butterflyFirstStackRow, butterflyFirstYFaceModes,
    butterflyFirstYFaceRow, butterflySeedModes, butterflySeedRow,
    butterflyZTwoModes, butterflyZTwoRow, sidebandPlusY_eq,
    sidebandMinusY_eq, sidebandPlusZ_eq, sidebandMinusZ_eq,
    gaussianRatVectorRealInner, axisWave, pumpY, pumpZ, realRow,
    realGaussian, GaussianRat.add, GaussianRat.sub, GaussianRat.neg,
    GaussianRat.mul, GaussianRat.ratScale, GaussianRat.intScale,
    GaussianRat.ratDiv, Fin.sum_univ_succ, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two] <;>
  ring

theorem plusReserveJet_eq (x z y w : Rat) :
    plusReserveJet x z y w =
      121 / 8 - (289 / 400) * x + (51 / 80) * z := by
  rw [plusReserveJet, coneAction_plus_eq]
  simp [exactPlusRow, plusWave, conePlusActionRow, conePlusRow,
    butterflyFirstStackRationalState, butterflyFirstStackModes,
    butterflyFirstStackRow, butterflyFirstYFaceModes,
    butterflyFirstYFaceRow, butterflySeedModes, butterflySeedRow,
    butterflyZTwoModes, butterflyZTwoRow, sidebandPlusY_eq,
    sidebandMinusY_eq, sidebandPlusZ_eq, sidebandMinusZ_eq,
    gaussianRatVectorRealInner, axisWave, pumpY, pumpZ, realRow,
    realGaussian, GaussianRat.add, GaussianRat.sub, GaussianRat.neg,
    GaussianRat.mul, GaussianRat.ratScale, GaussianRat.intScale,
    GaussianRat.ratDiv, Fin.sum_univ_succ, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two] <;>
  ring

theorem minusReserveJet_eq (x z y w : Rat) :
    minusReserveJet x z y w =
      121 / 8 + (289 / 400) * y - (51 / 80) * w := by
  rw [minusReserveJet, coneAction_minus_eq]
  simp [exactMinusRow, minusWave, coneMinusActionRow, coneMinusRow,
    butterflyFirstStackRationalState, butterflyFirstStackModes,
    butterflyFirstStackRow, butterflyFirstYFaceModes,
    butterflyFirstYFaceRow, butterflySeedModes, butterflySeedRow,
    butterflyZTwoModes, butterflyZTwoRow, sidebandPlusY_eq,
    sidebandMinusY_eq, sidebandPlusZ_eq, sidebandMinusZ_eq,
    gaussianRatVectorRealInner, axisWave, pumpY, pumpZ, realRow,
    realGaussian, GaussianRat.add, GaussianRat.sub, GaussianRat.neg,
    GaussianRat.mul, GaussianRat.ratScale, GaussianRat.intScale,
    GaussianRat.ratDiv, Fin.sum_univ_succ, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two] <;>
  ring

def crossPair (x z y w : Rat) : GaussianRatVector :=
  symPair plusWave minusWave (conePlusRow x z) (coneMinusRow y w)

def crossPairJet (x z y w : Rat) : GaussianRatVector :=
  symPair plusWave minusWave
      (coneAction x z y w plusWave) (coneMinusRow y w) +
    symPair plusWave minusWave
      (conePlusRow x z) (coneAction x z y w minusWave)

def desiredAxis : GaussianRatVector := butterflyStepY 4 (-1)

def desiredPairing (x z y w : Rat) : Rat :=
  gaussianRatVectorRealInner desiredAxis (crossPair x z y w)

def desiredPairingJet (x z y w : Rat) : Rat :=
  gaussianRatVectorRealInner desiredAxis (crossPairJet x z y w)

theorem desiredPairing_eq (x z y w : Rat) :
    desiredPairing x z y w = (7680 / 289) * (x * w + z * y) := by
  simp (config := { maxSteps := 5000000 })
    [desiredPairing, desiredAxis, crossPair, plusWave, minusWave,
      conePlusRow, coneMinusRow, butterflyStepY, butterflyCoefficient,
      sidebandPlusY_eq, sidebandMinusY_eq,
      symPair, rationalVorticityPairContribution,
      rationalIntegerWaveNormSq, gaussianRatVectorRealInner,
      axisWave, pumpY, realRow, realGaussian, GaussianRatVector.add,
      GaussianRatVector.waveDot, GaussianRatVector.waveCross,
      GaussianRatVector.tripleWaveCrossDot,
      GaussianRatVector.complexScale, GaussianRat.add,
      GaussianRat.sub, GaussianRat.neg, GaussianRat.mul,
      GaussianRat.ratScale, GaussianRat.intScale,
      GaussianRat.ratDiv, Fin.sum_univ_succ,
      Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two] <;>
  ring

theorem desiredPairingJet_eq (x z y w : Rat) :
    desiredPairingJet x z y w =
      (28800 / 289) * (x - y) +
        (1920 / 289) * (w - z) -
          (768 / 85) * (x * w + z * y) := by
  unfold desiredPairingJet crossPairJet
  rw [coneAction_plus_eq, coneAction_minus_eq]
  simp (config := { maxSteps := 5000000 })
    [desiredAxis, crossPairJet, conePlusActionRow, coneMinusActionRow,
      plusWave, minusWave, conePlusRow, coneMinusRow,
      butterflyStepY, butterflyCoefficient, sidebandPlusY_eq,
      sidebandMinusY_eq, symPair,
      rationalVorticityPairContribution, rationalIntegerWaveNormSq,
      gaussianRatVectorRealInner, axisWave, pumpY, realRow,
      realGaussian, GaussianRatVector.add, GaussianRatVector.waveDot,
      GaussianRatVector.waveCross,
      GaussianRatVector.tripleWaveCrossDot,
      GaussianRatVector.complexScale, GaussianRat.add,
      GaussianRat.sub, GaussianRat.neg, GaussianRat.mul,
      GaussianRat.ratScale, GaussianRat.intScale,
      GaussianRat.ratDiv, Fin.sum_univ_succ,
      Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two] <;>
  ring

theorem orthant_walls_strictly_inward (x z y w : Rat) :
    0 < (conePlusActionRow 0 z 0).re ∧
      (conePlusActionRow x 0 2).re < 0 ∧
      (coneMinusActionRow 0 w 0).re < 0 ∧
      0 < (coneMinusActionRow y 0 2).re := by
  simp [conePlusActionRow, coneMinusActionRow, conePlusRow,
    coneMinusRow, realRow, realGaussian, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two]

/-- The missing cross-pair coordinate is automatic on the oriented cell;
the old two-half-space countermodel lies outside this orthant. -/
theorem desiredPairing_pos_of_orientedOrthant
    {x z y w : Rat}
    (xPos : 0 < x) (zNeg : z < 0)
    (yNeg : y < 0) (wPos : 0 < w) :
    0 < desiredPairing x z y w := by
  rw [desiredPairing_eq]
  have xwPos : 0 < x * w := mul_pos xPos wPos
  have zyPos : 0 < z * y := mul_pos_of_neg_of_neg zNeg yNeg
  positivity

end ButterflySidebandOrthantInward
end RationalVorticityEvaluator
end NavierStokes
end SaturationMonoid
