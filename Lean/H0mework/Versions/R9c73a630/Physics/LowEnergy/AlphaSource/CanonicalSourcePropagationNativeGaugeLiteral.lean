import H0mework.Versions.R9c73a630.Physics.LowEnergy.AlphaSource.CanonicalSourcePropagationNativeGaugeRay
import H0mework.Versions.R9c73a630.Physics.LowEnergy.AlphaSource.CanonicalSourcePropagationNativeGravityScalarReturn
import H0mework.Versions.R9c73a630.Physics.LowEnergy.AlphaSource.CanonicalSourcePropagationNativeHodgeFlat
import H0mework.Versions.R2.Physics.SpinPair.GaugeField

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 8192
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
noncomputable section
namespace LowEnergy.SourcePropagationNativeActionHessian
open SaturationMonoid.PhysicsCore
open ProofFreeRicherAnholonomicSource StageNineEnrichedProofFreeSource StageNineGlobalIntegratedAction
open StageNineHolonomicField Stage9C.Material.SpinPair Stage9C.Dynamics.Homogeneous
open SU7MotherLieAlgebra SU7MotherGaugeTheory StageNineP286GaugeAuxiliaryVariation
open PreparationVacuumMixedFieldReturn PreparationVacuumLowerClassical PreparationCoordinates
open SourceQuantumScalarChart SourceQuantumGaugeSliceCoordinates SourceQuantumNativeDimensions
open scoped BigOperators ContDiff Topology Matrix.Norms.Elementwise
attribute [local irreducible] Stage9C.Material.SpinPair.actual
def gaugeColorRaw : Fin 3 → Fin 12 → ℝ :=
  ![Pi.single 1 (1/2),Pi.single 0 (1/2),Pi.single 6 (1/2)-Pi.single 7 (1/2)]
open SourceQuantumNativeDimensions SourceQuantumGaugeSliceCoordinates SourceQuantumResidualGaugeSlice
private theorem gauge_lieval_smul (r : ℝ) (x : SU3BlockLieMatrix) :
    ((r • x : SU3BlockLieMatrix) : Matrix (Fin 3) (Fin 3) ℂ) =
      r • (x : Matrix (Fin 3) (Fin 3) ℂ) := rfl
private theorem gauge_lieval_sub (x y : SU3BlockLieMatrix) :
    ((x-y : SU3BlockLieMatrix) : Matrix (Fin 3) (Fin 3) ℂ) =
      (x : Matrix (Fin 3) (Fin 3) ℂ)-(y : Matrix (Fin 3) (Fin 3) ℂ) := rfl
theorem gaugeColor_source (g : Fin 3) :
    rawCoordinates (show NativeLie from p286CoordinateEquiv (sourceColorP286Generator g)) = gaugeColorRaw g := by
  change rawRead (show NativeLie from p286CoordinateEquiv (sourceColorP286Generator g)) = _
  unfold rawRead
  rw [nativeCoordinates_apply]
  funext i
  fin_cases g <;> fin_cases i <;>
    simp only [gaugeColorRaw, sourceColorP286Generator, p286LieBracket, suLieBracket,
      colorCartanGenerator, colorCartanRaw, colorMixingGenerator, colorMixingRaw]
  all_goals dsimp only [Matrix.vecCons, Matrix.vecHead, Matrix.vecTail, Fin.cons, Fin.cases,
    Fin.induction, Fin.induction.go, Prod.smul_fst, Prod.smul_snd]
  all_goals norm_num only [Matrix.mul_apply, Fin.sum_univ_three, Pi.single_apply]
  all_goals simp only [eq_mpr_eq_cast, cast_eq, gauge_lieval_smul, Matrix.smul_apply,
    gauge_lieval_sub, Matrix.sub_apply, Matrix.diagonal_apply]
  all_goals norm_num [colorMixingRaw, Pi.single_apply]
  all_goals norm_num [Fin.ext_iff]

def gaugeBackgroundRaw : Fin 4 → Fin 12 → ℝ :=
  ![0, gaugeScale • gaugeColorRaw 0, gaugeScale • gaugeColorRaw 1, gaugeScale • gaugeColorRaw 2]

theorem gaugeBackgroundRaw_source (mu : Fin 4) :
    rawCoordinates (show NativeLie from p286CoordinateEquiv (actual.gaugeConnection 0 mu)) =
      gaugeBackgroundRaw mu := by
  rw [actual_gaugeConnection]
  fin_cases mu <;> simp [gaugePotential, gaugeBackgroundRaw, map_smul, gaugeColor_source]

def gaugeMagneticRaw : Fin 6 → Fin 12 → ℝ :=
  ![0,0,0, -(gaugeScale^2) • gaugeColorRaw 0,
    -(gaugeScale^2) • gaugeColorRaw 1, -(gaugeScale^2) • gaugeColorRaw 2]

def gaugeAuxiliaryRaw : Fin 6 → Fin 12 → ℝ :=
  ![(gaugeScale^2/(sourceCoupling*lapse)) • gaugeColorRaw 0,
    (gaugeScale^2/(sourceCoupling*lapse)) • gaugeColorRaw 1,
    (gaugeScale^2/(sourceCoupling*lapse)) • gaugeColorRaw 2,0,0,0]

theorem sourceGaugeCurvature0_literal (pair : Fin 6) :
    sourceGaugeCurvature0 pair = gaugeMagneticRaw pair := by
  unfold sourceGaugeCurvature0
  rw [actual_gaugeCurvature]
  fin_cases pair <;> simp [magneticCurvature, gaugeMagneticRaw, map_smul, gaugeColor_source]

theorem sourceGaugeB0_literal (pair : Fin 6) : sourceGaugeB0 pair = gaugeAuxiliaryRaw pair := by
  unfold sourceGaugeB0
  rw [actual_gaugeAuxiliary]
  fin_cases pair <;> simp [electricAuxiliary, gaugeAuxiliaryRaw, map_smul, gaugeColor_source]

def gaugeOriginalBracket (x y : Fin 12 → ℝ) (i : Fin 12) : ℝ :=
  ∑ a : Fin 12, ∑ b : Fin 12, (originalAd a i b : ℝ) * x a * y b

theorem gaugeOriginalBracket_source (a b : P286LieBlockData) :
    rawCoordinates (show NativeLie from p286CoordinateEquiv (p286LieBracket a b)) =
      gaugeOriginalBracket (rawCoordinates (show NativeLie from p286CoordinateEquiv a))
        (rawCoordinates (show NativeLie from p286CoordinateEquiv b)) := by
  funext i
  have generated := original_bracket_expansion (show NativeLie from p286CoordinateEquiv a)
    (show NativeLie from p286CoordinateEquiv b) i
  simpa only [StageNineP286BracketCalculus.coordinateBracketBilinear_apply,
    StageNineP286BracketCalculus.coordinateBracket, LinearEquiv.symm_apply_apply,
    gaugeOriginalBracket] using generated

def gaugeFieldRaw (f : Field289) (mu : Fin 4) : Fin 12 → ℝ := fun a => f (gaugeSlot mu a)

theorem gaugeFieldRaw_source (f : Field289) (mu : Fin 4) :
    rawCoordinates (fieldGauge f mu) = gaugeFieldRaw f mu := by
  unfold fieldGauge
  simp only [map_sum, map_smul, originalUnit, LinearEquiv.apply_symm_apply]
  funext i
  simp [gaugeFieldRaw, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply]

def gaugeLinearRaw (jet : NativeFirstJet) (pair : Fin 6) : Fin 12 → ℝ :=
  gaugeFieldRaw (jet.2 (pairFirst pair)) (pairSecond pair) -
    gaugeFieldRaw (jet.2 (pairSecond pair)) (pairFirst pair) +
    gaugeOriginalBracket (gaugeBackgroundRaw (pairFirst pair)) (gaugeFieldRaw jet.1 (pairSecond pair)) +
    gaugeOriginalBracket (gaugeFieldRaw jet.1 (pairFirst pair)) (gaugeBackgroundRaw (pairSecond pair))

def gaugeQuadraticRaw (jet : NativeFirstJet) (pair : Fin 6) : Fin 12 → ℝ :=
  gaugeOriginalBracket (gaugeFieldRaw jet.1 (pairFirst pair)) (gaugeFieldRaw jet.1 (pairSecond pair))

theorem gaugeQuadraticRaw_source (jet : NativeFirstJet) (pair : Fin 6) :
    nativeGaugeQuadraticCurvature jet pair = gaugeQuadraticRaw jet pair := by
  unfold nativeGaugeQuadraticCurvature gaugeQuadraticRaw
  rw [gaugeOriginalBracket_source]
  simp only [LinearEquiv.apply_symm_apply, gaugeFieldRaw_source]

theorem gaugeLinearRaw_source (jet : NativeFirstJet) (pair : Fin 6) :
    nativeGaugeLinearCurvature jet pair = gaugeLinearRaw jet pair := by
  unfold nativeGaugeLinearCurvature nativeGaugeRawCurvature nativeGaugeCurvature sourceGaugeCurvature0
  simp only [map_add, map_sub, LinearEquiv.apply_symm_apply, gaugeFieldRaw_source,
    gaugeOriginalBracket_source, gaugeBackgroundRaw_source, gaugeQuadraticRaw_source]
  unfold gaugeQuadraticRaw gaugeLinearRaw
  abel

def gaugeFlatQuadratic (jet : NativeFirstJet) : ℝ :=
  let e := homogeneousCoframe lapse
  let h := fieldCoframe jet.1
  let B1 := fieldGaugeB jet.1
  let c := StageNineTopologicalFourFormPairing.twoFormComplement
  (∑ pair : Fin 6, (rawGaugePair (B1 pair) (gaugeLinearRaw jet (c pair)) +
    rawGaugePair (gaugeAuxiliaryRaw pair) (gaugeQuadraticRaw jet (c pair)))) -
    (positiveSmoothUnifiedSource.legacy.sigma / 2) * ∑ pair : Fin 6, ∑ input : Fin 6, (
      nativeHodgeMatrix e (c pair) input * rawGaugePair (B1 pair) (B1 input) +
      nativeHodgeFirst e h (c pair) input *
        (rawGaugePair (B1 pair) (gaugeAuxiliaryRaw input) +
          rawGaugePair (gaugeAuxiliaryRaw pair) (B1 input)) +
      nativeHodgeSecond e h (c pair) input * rawGaugePair (gaugeAuxiliaryRaw pair) (gaugeAuxiliaryRaw input))

theorem nativeGaugeQuadratic_flat (jet : NativeFirstJet) : nativeGaugeQuadratic jet = gaugeFlatQuadratic jet := by
  unfold nativeGaugeQuadratic gaugeFlatQuadratic
  simp only [gaugeLinearRaw_source, gaugeQuadraticRaw_source, sourceGaugeB0_literal, actual_coframe]


abbrev GaugeLiteralIndex := Option (Fin 4) × Fin 289

def gaugeLiteralRead (jet : NativeFirstJet) (i : GaugeLiteralIndex) : ℝ :=
  match i.1 with
  | none => jet.1 i.2
  | some mu => jet.2 mu i.2

def literalGaugeTerms : List (GaugeLiteralIndex × GaugeLiteralIndex × ℝ) :=
  [
    ((none, 57), (none, 62), -3/5), ((none, 57), (none, 67), -3/5), ((none, 57), (none, 72), -3/5), ((none, 57), (none, 218), (25*lapse/3)/5),
    ((none, 57), (none, 229), (25*lapse/3)/5), ((none, 57), (none, 247), (25*lapse/3)/10), ((none, 57), (none, 248), -(25*lapse/3)/10), ((none, 58), (none, 61), 3/5),
    ((none, 58), (none, 271), -(25*lapse/3)/10), ((none, 58), (none, 272), (25*lapse/3)/10), ((none, 58), (none, 277), (25*lapse/3)/5), ((none, 59), (none, 65), 3/5),
    ((none, 59), (none, 259), (25*lapse/3)/10), ((none, 59), (none, 260), -(25*lapse/3)/10), ((none, 59), (none, 278), -(25*lapse/3)/5), ((none, 60), (none, 69), 3/5),
    ((none, 60), (none, 253), -(25*lapse/3)/5), ((none, 60), (none, 266), (25*lapse/3)/5), ((none, 61), (none, 61), -(25*lapse/3)/3), ((none, 61), (none, 271), 5/6),
    ((none, 61), (none, 272), -5/6), ((none, 61), (none, 277), -5/3), ((none, 62), (none, 62), 18*(25*lapse/3)/125), ((none, 62), (none, 67), -9*(25*lapse/3)/125),
    ((none, 62), (none, 72), -9*(25*lapse/3)/125), ((none, 62), (none, 218), 18/25), ((none, 62), (none, 229), -18/25), ((none, 62), (none, 247), -9/25),
    ((none, 62), (none, 248), 9/25), ((none, 63), (none, 63), 9*(25*lapse/3)/125), ((none, 63), (none, 66), 27*(25*lapse/3)/125), ((none, 63), (none, 217), 18/25),
    ((none, 63), (none, 230), 18/25), ((none, 64), (none, 64), 9*(25*lapse/3)/125), ((none, 64), (none, 70), 27*(25*lapse/3)/125), ((none, 64), (none, 223), 9/25),
    ((none, 64), (none, 224), -9/25), ((none, 64), (none, 242), 18/25), ((none, 65), (none, 65), -(25*lapse/3)/3), ((none, 65), (none, 259), -5/6),
    ((none, 65), (none, 260), 5/6), ((none, 65), (none, 278), 5/3), ((none, 66), (none, 66), 9*(25*lapse/3)/125), ((none, 66), (none, 217), 18/25),
    ((none, 66), (none, 230), 18/25), ((none, 67), (none, 67), 18*(25*lapse/3)/125), ((none, 67), (none, 72), -9*(25*lapse/3)/125), ((none, 67), (none, 218), -18/25),
    ((none, 67), (none, 229), 18/25), ((none, 67), (none, 247), -9/25), ((none, 67), (none, 248), 9/25), ((none, 68), (none, 68), 9*(25*lapse/3)/125),
    ((none, 68), (none, 71), 27*(25*lapse/3)/125), ((none, 68), (none, 235), 9/25), ((none, 68), (none, 236), -9/25), ((none, 68), (none, 241), 18/25),
    ((none, 69), (none, 69), -(25*lapse/3)/3), ((none, 69), (none, 253), 5/3), ((none, 69), (none, 266), -5/3), ((none, 70), (none, 70), 9*(25*lapse/3)/125),
    ((none, 70), (none, 223), 9/25), ((none, 70), (none, 224), -9/25), ((none, 70), (none, 242), 18/25), ((none, 71), (none, 71), 9*(25*lapse/3)/125),
    ((none, 71), (none, 235), 9/25), ((none, 71), (none, 236), -9/25), ((none, 71), (none, 241), 18/25), ((none, 72), (none, 72), 18*(25*lapse/3)/125),
    ((none, 72), (none, 218), -18/25), ((none, 72), (none, 229), -18/25), ((none, 72), (none, 247), 9/25), ((none, 72), (none, 248), -9/25),
    ((none, 9), (none, 259), 3*spinScale/5), ((none, 9), (none, 260), -3*spinScale/5), ((none, 9), (none, 278), -6*spinScale/5), ((none, 10), (none, 271), -3*spinScale/5),
    ((none, 10), (none, 272), 3*spinScale/5), ((none, 10), (none, 277), 6*spinScale/5), ((none, 11), (none, 258), -3*spinScale/5), ((none, 11), (none, 269), 3*spinScale/5),
    ((none, 11), (none, 280), -3*spinScale/5), ((none, 12), (none, 257), 3*spinScale/5), ((none, 12), (none, 270), 3*spinScale/5), ((none, 12), (none, 279), 3*spinScale/5),
    ((none, 13), (none, 256), -3*spinScale/5), ((none, 13), (none, 267), -3*spinScale/5), ((none, 13), (none, 282), 3*spinScale/5), ((none, 14), (none, 255), 3*spinScale/5),
    ((none, 14), (none, 268), -3*spinScale/5), ((none, 14), (none, 281), -3*spinScale/5), ((none, 15), (none, 253), -3*spinScale/5), ((none, 15), (none, 266), 3*spinScale/5),
    ((none, 16), (none, 253), 3*spinScale/5), ((none, 16), (none, 266), -3*spinScale/5), ((none, 21), (none, 34), 4*(25*lapse/3)/5), ((none, 21), (none, 230), 6*spinScale/5),
    ((none, 22), (none, 33), -4*(25*lapse/3)/5), ((none, 22), (none, 51), -2*(25*lapse/3)/5), ((none, 22), (none, 52), 2*(25*lapse/3)/5), ((none, 22), (none, 229), -6*spinScale/5),
    ((none, 22), (none, 247), -3*spinScale/5), ((none, 22), (none, 248), 3*spinScale/5), ((none, 23), (none, 36), 2*(25*lapse/3)/5), ((none, 23), (none, 49), 2*(25*lapse/3)/5),
    ((none, 23), (none, 232), 3*spinScale/5), ((none, 23), (none, 245), 3*spinScale/5), ((none, 24), (none, 35), -2*(25*lapse/3)/5), ((none, 24), (none, 50), 2*(25*lapse/3)/5),
    ((none, 24), (none, 231), -3*spinScale/5), ((none, 24), (none, 246), 3*spinScale/5), ((none, 25), (none, 38), -2*(25*lapse/3)/5), ((none, 25), (none, 47), -2*(25*lapse/3)/5),
    ((none, 25), (none, 234), -3*spinScale/5), ((none, 25), (none, 243), -3*spinScale/5), ((none, 26), (none, 37), 2*(25*lapse/3)/5), ((none, 26), (none, 48), -2*(25*lapse/3)/5),
    ((none, 26), (none, 233), 3*spinScale/5), ((none, 26), (none, 244), -3*spinScale/5), ((none, 27), (none, 46), 2*(25*lapse/3)/5), ((none, 27), (none, 242), 3*spinScale/5),
    ((none, 28), (none, 46), -2*(25*lapse/3)/5), ((none, 28), (none, 242), -3*spinScale/5), ((none, 33), (none, 51), -2*(25*lapse/3)/5), ((none, 33), (none, 52), 2*(25*lapse/3)/5),
    ((none, 33), (none, 218), -6*spinScale/5), ((none, 33), (none, 247), -3*spinScale/5), ((none, 33), (none, 248), 3*spinScale/5), ((none, 34), (none, 217), 6*spinScale/5),
    ((none, 35), (none, 50), 2*(25*lapse/3)/5), ((none, 35), (none, 220), -3*spinScale/5), ((none, 35), (none, 246), 3*spinScale/5), ((none, 36), (none, 49), -2*(25*lapse/3)/5),
    ((none, 36), (none, 219), 3*spinScale/5), ((none, 36), (none, 245), -3*spinScale/5), ((none, 37), (none, 48), 2*(25*lapse/3)/5), ((none, 37), (none, 222), 3*spinScale/5),
    ((none, 37), (none, 244), 3*spinScale/5), ((none, 38), (none, 47), -2*(25*lapse/3)/5), ((none, 38), (none, 221), -3*spinScale/5), ((none, 38), (none, 243), -3*spinScale/5),
    ((none, 39), (none, 45), 2*(25*lapse/3)/5), ((none, 39), (none, 241), 3*spinScale/5), ((none, 40), (none, 45), -2*(25*lapse/3)/5), ((none, 40), (none, 241), -3*spinScale/5),
    ((none, 45), (none, 235), 3*spinScale/5), ((none, 45), (none, 236), -3*spinScale/5), ((none, 46), (none, 223), 3*spinScale/5), ((none, 46), (none, 224), -3*spinScale/5),
    ((none, 47), (none, 221), -3*spinScale/5), ((none, 47), (none, 234), -3*spinScale/5), ((none, 48), (none, 222), -3*spinScale/5), ((none, 48), (none, 233), 3*spinScale/5),
    ((none, 49), (none, 219), 3*spinScale/5), ((none, 49), (none, 232), -3*spinScale/5), ((none, 50), (none, 220), 3*spinScale/5), ((none, 50), (none, 231), 3*spinScale/5),
    ((none, 51), (none, 218), -3*spinScale/5), ((none, 51), (none, 229), -3*spinScale/5), ((none, 52), (none, 218), 3*spinScale/5), ((none, 52), (none, 229), 3*spinScale/5),
    ((some 0, 21), (none, 253), 2), ((some 1, 9), (none, 253), -2), ((some 0, 22), (none, 254), 2), ((some 1, 10), (none, 254), -2),
    ((some 0, 23), (none, 255), 2), ((some 1, 11), (none, 255), -2), ((some 0, 24), (none, 256), 2), ((some 1, 12), (none, 256), -2),
    ((some 0, 25), (none, 257), 2), ((some 1, 13), (none, 257), -2), ((some 0, 26), (none, 258), 2), ((some 1, 14), (none, 258), -2),
    ((some 0, 27), (none, 259), 2), ((some 0, 27), (none, 260), 1), ((some 1, 15), (none, 259), -2), ((some 1, 15), (none, 260), -1),
    ((some 0, 28), (none, 259), 1), ((some 0, 28), (none, 260), 2), ((some 1, 16), (none, 259), -1), ((some 1, 16), (none, 260), -2),
    ((some 0, 29), (none, 261), 2), ((some 1, 17), (none, 261), -2), ((some 0, 30), (none, 262), 2), ((some 1, 18), (none, 262), -2),
    ((some 0, 31), (none, 263), 2), ((some 1, 19), (none, 263), -2), ((some 0, 32), (none, 264), 1), ((some 1, 20), (none, 264), -1),
    ((some 0, 33), (none, 265), 2), ((some 2, 9), (none, 265), -2), ((some 0, 34), (none, 266), 2), ((some 2, 10), (none, 266), -2),
    ((some 0, 35), (none, 267), 2), ((some 2, 11), (none, 267), -2), ((some 0, 36), (none, 268), 2), ((some 2, 12), (none, 268), -2),
    ((some 0, 37), (none, 269), 2), ((some 2, 13), (none, 269), -2), ((some 0, 38), (none, 270), 2), ((some 2, 14), (none, 270), -2),
    ((some 0, 39), (none, 271), 2), ((some 0, 39), (none, 272), 1), ((some 2, 15), (none, 271), -2), ((some 2, 15), (none, 272), -1),
    ((some 0, 40), (none, 271), 1), ((some 0, 40), (none, 272), 2), ((some 2, 16), (none, 271), -1), ((some 2, 16), (none, 272), -2),
    ((some 0, 41), (none, 273), 2), ((some 2, 17), (none, 273), -2), ((some 0, 42), (none, 274), 2), ((some 2, 18), (none, 274), -2),
    ((some 0, 43), (none, 275), 2), ((some 2, 19), (none, 275), -2), ((some 0, 44), (none, 276), 1), ((some 2, 20), (none, 276), -1),
    ((some 0, 45), (none, 277), 2), ((some 3, 9), (none, 277), -2), ((some 0, 46), (none, 278), 2), ((some 3, 10), (none, 278), -2),
    ((some 0, 47), (none, 279), 2), ((some 3, 11), (none, 279), -2), ((some 0, 48), (none, 280), 2), ((some 3, 12), (none, 280), -2),
    ((some 0, 49), (none, 281), 2), ((some 3, 13), (none, 281), -2), ((some 0, 50), (none, 282), 2), ((some 3, 14), (none, 282), -2),
    ((some 0, 51), (none, 283), 2), ((some 0, 51), (none, 284), 1), ((some 3, 15), (none, 283), -2), ((some 3, 15), (none, 284), -1),
    ((some 0, 52), (none, 283), 1), ((some 0, 52), (none, 284), 2), ((some 3, 16), (none, 283), -1), ((some 3, 16), (none, 284), -2),
    ((some 0, 53), (none, 285), 2), ((some 3, 17), (none, 285), -2), ((some 0, 54), (none, 286), 2), ((some 3, 18), (none, 286), -2),
    ((some 0, 55), (none, 287), 2), ((some 3, 19), (none, 287), -2), ((some 0, 56), (none, 288), 1), ((some 3, 20), (none, 288), -1),
    ((some 2, 45), (none, 217), 2), ((some 3, 33), (none, 217), -2), ((some 2, 46), (none, 218), 2), ((some 3, 34), (none, 218), -2),
    ((some 2, 47), (none, 219), 2), ((some 3, 35), (none, 219), -2), ((some 2, 48), (none, 220), 2), ((some 3, 36), (none, 220), -2),
    ((some 2, 49), (none, 221), 2), ((some 3, 37), (none, 221), -2), ((some 2, 50), (none, 222), 2), ((some 3, 38), (none, 222), -2),
    ((some 2, 51), (none, 223), 2), ((some 2, 51), (none, 224), 1), ((some 3, 39), (none, 223), -2), ((some 3, 39), (none, 224), -1),
    ((some 2, 52), (none, 223), 1), ((some 2, 52), (none, 224), 2), ((some 3, 40), (none, 223), -1), ((some 3, 40), (none, 224), -2),
    ((some 2, 53), (none, 225), 2), ((some 3, 41), (none, 225), -2), ((some 2, 54), (none, 226), 2), ((some 3, 42), (none, 226), -2),
    ((some 2, 55), (none, 227), 2), ((some 3, 43), (none, 227), -2), ((some 2, 56), (none, 228), 1), ((some 3, 44), (none, 228), -1),
    ((some 3, 21), (none, 229), 2), ((some 1, 45), (none, 229), -2), ((some 3, 22), (none, 230), 2), ((some 1, 46), (none, 230), -2),
    ((some 3, 23), (none, 231), 2), ((some 1, 47), (none, 231), -2), ((some 3, 24), (none, 232), 2), ((some 1, 48), (none, 232), -2),
    ((some 3, 25), (none, 233), 2), ((some 1, 49), (none, 233), -2), ((some 3, 26), (none, 234), 2), ((some 1, 50), (none, 234), -2),
    ((some 3, 27), (none, 235), 2), ((some 3, 27), (none, 236), 1), ((some 1, 51), (none, 235), -2), ((some 1, 51), (none, 236), -1),
    ((some 3, 28), (none, 235), 1), ((some 3, 28), (none, 236), 2), ((some 1, 52), (none, 235), -1), ((some 1, 52), (none, 236), -2),
    ((some 3, 29), (none, 237), 2), ((some 1, 53), (none, 237), -2), ((some 3, 30), (none, 238), 2), ((some 1, 54), (none, 238), -2),
    ((some 3, 31), (none, 239), 2), ((some 1, 55), (none, 239), -2), ((some 3, 32), (none, 240), 1), ((some 1, 56), (none, 240), -1),
    ((some 1, 33), (none, 241), 2), ((some 2, 21), (none, 241), -2), ((some 1, 34), (none, 242), 2), ((some 2, 22), (none, 242), -2),
    ((some 1, 35), (none, 243), 2), ((some 2, 23), (none, 243), -2), ((some 1, 36), (none, 244), 2), ((some 2, 24), (none, 244), -2),
    ((some 1, 37), (none, 245), 2), ((some 2, 25), (none, 245), -2), ((some 1, 38), (none, 246), 2), ((some 2, 26), (none, 246), -2),
    ((some 1, 39), (none, 247), 2), ((some 1, 39), (none, 248), 1), ((some 2, 27), (none, 247), -2), ((some 2, 27), (none, 248), -1),
    ((some 1, 40), (none, 247), 1), ((some 1, 40), (none, 248), 2), ((some 2, 28), (none, 247), -1), ((some 2, 28), (none, 248), -2),
    ((some 1, 41), (none, 249), 2), ((some 2, 29), (none, 249), -2), ((some 1, 42), (none, 250), 2), ((some 2, 30), (none, 250), -2),
    ((some 1, 43), (none, 251), 2), ((some 2, 31), (none, 251), -2), ((some 1, 44), (none, 252), 1), ((some 2, 32), (none, 252), -1),
    ((none, 217), (none, 217), 3*(25*lapse/3)/50), ((none, 218), (none, 218), 3*(25*lapse/3)/50), ((none, 219), (none, 219), 3*(25*lapse/3)/50), ((none, 220), (none, 220), 3*(25*lapse/3)/50),
    ((none, 221), (none, 221), 3*(25*lapse/3)/50), ((none, 222), (none, 222), 3*(25*lapse/3)/50), ((none, 223), (none, 223), 3*(25*lapse/3)/50), ((none, 223), (none, 224), 3*(25*lapse/3)/50),
    ((none, 224), (none, 224), 3*(25*lapse/3)/50), ((none, 225), (none, 225), 3*(25*lapse/3)/50), ((none, 226), (none, 226), 3*(25*lapse/3)/50), ((none, 227), (none, 227), 3*(25*lapse/3)/50),
    ((none, 228), (none, 228), 3*(25*lapse/3)/100), ((none, 229), (none, 229), 3*(25*lapse/3)/50), ((none, 230), (none, 230), 3*(25*lapse/3)/50), ((none, 231), (none, 231), 3*(25*lapse/3)/50),
    ((none, 232), (none, 232), 3*(25*lapse/3)/50), ((none, 233), (none, 233), 3*(25*lapse/3)/50), ((none, 234), (none, 234), 3*(25*lapse/3)/50), ((none, 235), (none, 235), 3*(25*lapse/3)/50),
    ((none, 235), (none, 236), 3*(25*lapse/3)/50), ((none, 236), (none, 236), 3*(25*lapse/3)/50), ((none, 237), (none, 237), 3*(25*lapse/3)/50), ((none, 238), (none, 238), 3*(25*lapse/3)/50),
    ((none, 239), (none, 239), 3*(25*lapse/3)/50), ((none, 240), (none, 240), 3*(25*lapse/3)/100), ((none, 241), (none, 241), 3*(25*lapse/3)/50), ((none, 242), (none, 242), 3*(25*lapse/3)/50),
    ((none, 243), (none, 243), 3*(25*lapse/3)/50), ((none, 244), (none, 244), 3*(25*lapse/3)/50), ((none, 245), (none, 245), 3*(25*lapse/3)/50), ((none, 246), (none, 246), 3*(25*lapse/3)/50),
    ((none, 247), (none, 247), 3*(25*lapse/3)/50), ((none, 247), (none, 248), 3*(25*lapse/3)/50), ((none, 248), (none, 248), 3*(25*lapse/3)/50), ((none, 249), (none, 249), 3*(25*lapse/3)/50),
    ((none, 250), (none, 250), 3*(25*lapse/3)/50), ((none, 251), (none, 251), 3*(25*lapse/3)/50), ((none, 252), (none, 252), 3*(25*lapse/3)/100), ((none, 253), (none, 253), -5*(25*lapse/3)/36),
    ((none, 254), (none, 254), -5*(25*lapse/3)/36), ((none, 255), (none, 255), -5*(25*lapse/3)/36), ((none, 256), (none, 256), -5*(25*lapse/3)/36), ((none, 257), (none, 257), -5*(25*lapse/3)/36),
    ((none, 258), (none, 258), -5*(25*lapse/3)/36), ((none, 259), (none, 259), -5*(25*lapse/3)/36), ((none, 259), (none, 260), -5*(25*lapse/3)/36), ((none, 260), (none, 260), -5*(25*lapse/3)/36),
    ((none, 261), (none, 261), -5*(25*lapse/3)/36), ((none, 262), (none, 262), -5*(25*lapse/3)/36), ((none, 263), (none, 263), -5*(25*lapse/3)/36), ((none, 264), (none, 264), -5*(25*lapse/3)/72),
    ((none, 265), (none, 265), -5*(25*lapse/3)/36), ((none, 266), (none, 266), -5*(25*lapse/3)/36), ((none, 267), (none, 267), -5*(25*lapse/3)/36), ((none, 268), (none, 268), -5*(25*lapse/3)/36),
    ((none, 269), (none, 269), -5*(25*lapse/3)/36), ((none, 270), (none, 270), -5*(25*lapse/3)/36), ((none, 271), (none, 271), -5*(25*lapse/3)/36), ((none, 271), (none, 272), -5*(25*lapse/3)/36),
    ((none, 272), (none, 272), -5*(25*lapse/3)/36), ((none, 273), (none, 273), -5*(25*lapse/3)/36), ((none, 274), (none, 274), -5*(25*lapse/3)/36), ((none, 275), (none, 275), -5*(25*lapse/3)/36),
    ((none, 276), (none, 276), -5*(25*lapse/3)/72), ((none, 277), (none, 277), -5*(25*lapse/3)/36), ((none, 278), (none, 278), -5*(25*lapse/3)/36), ((none, 279), (none, 279), -5*(25*lapse/3)/36),
    ((none, 280), (none, 280), -5*(25*lapse/3)/36), ((none, 281), (none, 281), -5*(25*lapse/3)/36), ((none, 282), (none, 282), -5*(25*lapse/3)/36), ((none, 283), (none, 283), -5*(25*lapse/3)/36),
    ((none, 283), (none, 284), -5*(25*lapse/3)/36), ((none, 284), (none, 284), -5*(25*lapse/3)/36), ((none, 285), (none, 285), -5*(25*lapse/3)/36), ((none, 286), (none, 286), -5*(25*lapse/3)/36),
    ((none, 287), (none, 287), -5*(25*lapse/3)/36), ((none, 288), (none, 288), -5*(25*lapse/3)/72)
  ]

def literalGaugeQuadratic (jet : NativeFirstJet) : ℝ :=
  (literalGaugeTerms.map fun t => t.2.2 * gaugeLiteralRead jet t.1 * gaugeLiteralRead jet t.2.1).sum


def literalGaugeBBTerms : List (GaugeLiteralIndex × GaugeLiteralIndex × ℝ) :=
  [
    ((none, 217), (none, 217), 3*(25*lapse/3)/50), ((none, 218), (none, 218), 3*(25*lapse/3)/50), ((none, 219), (none, 219), 3*(25*lapse/3)/50), ((none, 220), (none, 220), 3*(25*lapse/3)/50),
    ((none, 221), (none, 221), 3*(25*lapse/3)/50), ((none, 222), (none, 222), 3*(25*lapse/3)/50), ((none, 223), (none, 223), 3*(25*lapse/3)/50), ((none, 223), (none, 224), 3*(25*lapse/3)/50),
    ((none, 224), (none, 224), 3*(25*lapse/3)/50), ((none, 225), (none, 225), 3*(25*lapse/3)/50), ((none, 226), (none, 226), 3*(25*lapse/3)/50), ((none, 227), (none, 227), 3*(25*lapse/3)/50),
    ((none, 228), (none, 228), 3*(25*lapse/3)/100), ((none, 229), (none, 229), 3*(25*lapse/3)/50), ((none, 230), (none, 230), 3*(25*lapse/3)/50), ((none, 231), (none, 231), 3*(25*lapse/3)/50),
    ((none, 232), (none, 232), 3*(25*lapse/3)/50), ((none, 233), (none, 233), 3*(25*lapse/3)/50), ((none, 234), (none, 234), 3*(25*lapse/3)/50), ((none, 235), (none, 235), 3*(25*lapse/3)/50),
    ((none, 235), (none, 236), 3*(25*lapse/3)/50), ((none, 236), (none, 236), 3*(25*lapse/3)/50), ((none, 237), (none, 237), 3*(25*lapse/3)/50), ((none, 238), (none, 238), 3*(25*lapse/3)/50),
    ((none, 239), (none, 239), 3*(25*lapse/3)/50), ((none, 240), (none, 240), 3*(25*lapse/3)/100), ((none, 241), (none, 241), 3*(25*lapse/3)/50), ((none, 242), (none, 242), 3*(25*lapse/3)/50),
    ((none, 243), (none, 243), 3*(25*lapse/3)/50), ((none, 244), (none, 244), 3*(25*lapse/3)/50), ((none, 245), (none, 245), 3*(25*lapse/3)/50), ((none, 246), (none, 246), 3*(25*lapse/3)/50),
    ((none, 247), (none, 247), 3*(25*lapse/3)/50), ((none, 247), (none, 248), 3*(25*lapse/3)/50), ((none, 248), (none, 248), 3*(25*lapse/3)/50), ((none, 249), (none, 249), 3*(25*lapse/3)/50),
    ((none, 250), (none, 250), 3*(25*lapse/3)/50), ((none, 251), (none, 251), 3*(25*lapse/3)/50), ((none, 252), (none, 252), 3*(25*lapse/3)/100), ((none, 253), (none, 253), -5*(25*lapse/3)/36),
    ((none, 254), (none, 254), -5*(25*lapse/3)/36), ((none, 255), (none, 255), -5*(25*lapse/3)/36), ((none, 256), (none, 256), -5*(25*lapse/3)/36), ((none, 257), (none, 257), -5*(25*lapse/3)/36),
    ((none, 258), (none, 258), -5*(25*lapse/3)/36), ((none, 259), (none, 259), -5*(25*lapse/3)/36), ((none, 259), (none, 260), -5*(25*lapse/3)/36), ((none, 260), (none, 260), -5*(25*lapse/3)/36),
    ((none, 261), (none, 261), -5*(25*lapse/3)/36), ((none, 262), (none, 262), -5*(25*lapse/3)/36), ((none, 263), (none, 263), -5*(25*lapse/3)/36), ((none, 264), (none, 264), -5*(25*lapse/3)/72),
    ((none, 265), (none, 265), -5*(25*lapse/3)/36), ((none, 266), (none, 266), -5*(25*lapse/3)/36), ((none, 267), (none, 267), -5*(25*lapse/3)/36), ((none, 268), (none, 268), -5*(25*lapse/3)/36),
    ((none, 269), (none, 269), -5*(25*lapse/3)/36), ((none, 270), (none, 270), -5*(25*lapse/3)/36), ((none, 271), (none, 271), -5*(25*lapse/3)/36), ((none, 271), (none, 272), -5*(25*lapse/3)/36),
    ((none, 272), (none, 272), -5*(25*lapse/3)/36), ((none, 273), (none, 273), -5*(25*lapse/3)/36), ((none, 274), (none, 274), -5*(25*lapse/3)/36), ((none, 275), (none, 275), -5*(25*lapse/3)/36),
    ((none, 276), (none, 276), -5*(25*lapse/3)/72), ((none, 277), (none, 277), -5*(25*lapse/3)/36), ((none, 278), (none, 278), -5*(25*lapse/3)/36), ((none, 279), (none, 279), -5*(25*lapse/3)/36),
    ((none, 280), (none, 280), -5*(25*lapse/3)/36), ((none, 281), (none, 281), -5*(25*lapse/3)/36), ((none, 282), (none, 282), -5*(25*lapse/3)/36), ((none, 283), (none, 283), -5*(25*lapse/3)/36),
    ((none, 283), (none, 284), -5*(25*lapse/3)/36), ((none, 284), (none, 284), -5*(25*lapse/3)/36), ((none, 285), (none, 285), -5*(25*lapse/3)/36), ((none, 286), (none, 286), -5*(25*lapse/3)/36),
    ((none, 287), (none, 287), -5*(25*lapse/3)/36), ((none, 288), (none, 288), -5*(25*lapse/3)/72)
  ]

def literalGaugeBBQuadratic (jet : NativeFirstJet) : ℝ :=
  (literalGaugeBBTerms.map fun t => t.2.2 * gaugeLiteralRead jet t.1 * gaugeLiteralRead jet t.2.1).sum

def gaugeBBQuadratic (jet : NativeFirstJet) : ℝ :=
  -(positiveSmoothUnifiedSource.legacy.sigma / 2) * ∑ pair : Fin 6, ∑ input : Fin 6,
    nativeHodgeMatrix (homogeneousCoframe lapse)
      (StageNineTopologicalFourFormPairing.twoFormComplement pair) input *
    rawGaugePair (fieldGaugeB jet.1 pair) (fieldGaugeB jet.1 input)

theorem lapseInv_source : lapse⁻¹ = (125/54 : ℝ)*lapse := by
  apply inv_eq_of_mul_eq_one_right
  nlinarith [lapse_sq]

theorem gaugeBBQuadratic_literal (jet : NativeFirstJet) : gaugeBBQuadratic jet = literalGaugeBBQuadratic jet := by
  have sigma : positiveSmoothUnifiedSource.legacy.sigma = (1/2 : ℝ) := sourceCoupling_eq
  unfold gaugeBBQuadratic
  rw [sigma]
  simp [gaugeBBQuadratic, nativeHodgeMatrix_original, gaugeOperatorCoefficient,
    homogeneousHodge, ne_of_gt lapse_pos, literalGaugeBBQuadratic,
    literalGaugeBBTerms, gaugeLiteralRead, fieldGaugeB, rawGaugePair,
    StageNineTopologicalFourFormPairing.twoFormComplement, Fin.sum_univ_six, gaugeBSlot]
  rw [lapseInv_source]
  ring


def literalGaugeBFTerms : List (GaugeLiteralIndex × GaugeLiteralIndex × ℝ) :=
  [
    ((none, 9), (none, 259), 3*spinScale/5), ((none, 9), (none, 260), -3*spinScale/5), ((none, 9), (none, 278), -6*spinScale/5), ((none, 10), (none, 271), -3*spinScale/5),
    ((none, 10), (none, 272), 3*spinScale/5), ((none, 10), (none, 277), 6*spinScale/5), ((none, 11), (none, 258), -3*spinScale/5), ((none, 11), (none, 269), 3*spinScale/5),
    ((none, 11), (none, 280), -3*spinScale/5), ((none, 12), (none, 257), 3*spinScale/5), ((none, 12), (none, 270), 3*spinScale/5), ((none, 12), (none, 279), 3*spinScale/5),
    ((none, 13), (none, 256), -3*spinScale/5), ((none, 13), (none, 267), -3*spinScale/5), ((none, 13), (none, 282), 3*spinScale/5), ((none, 14), (none, 255), 3*spinScale/5),
    ((none, 14), (none, 268), -3*spinScale/5), ((none, 14), (none, 281), -3*spinScale/5), ((none, 15), (none, 253), -3*spinScale/5), ((none, 15), (none, 266), 3*spinScale/5),
    ((none, 16), (none, 253), 3*spinScale/5), ((none, 16), (none, 266), -3*spinScale/5), ((none, 21), (none, 230), 6*spinScale/5), ((none, 22), (none, 229), -6*spinScale/5),
    ((none, 22), (none, 247), -3*spinScale/5), ((none, 22), (none, 248), 3*spinScale/5), ((none, 23), (none, 232), 3*spinScale/5), ((none, 23), (none, 245), 3*spinScale/5),
    ((none, 24), (none, 231), -3*spinScale/5), ((none, 24), (none, 246), 3*spinScale/5), ((none, 25), (none, 234), -3*spinScale/5), ((none, 25), (none, 243), -3*spinScale/5),
    ((none, 26), (none, 233), 3*spinScale/5), ((none, 26), (none, 244), -3*spinScale/5), ((none, 27), (none, 242), 3*spinScale/5), ((none, 28), (none, 242), -3*spinScale/5),
    ((none, 33), (none, 218), -6*spinScale/5), ((none, 33), (none, 247), -3*spinScale/5), ((none, 33), (none, 248), 3*spinScale/5), ((none, 34), (none, 217), 6*spinScale/5),
    ((none, 35), (none, 220), -3*spinScale/5), ((none, 35), (none, 246), 3*spinScale/5), ((none, 36), (none, 219), 3*spinScale/5), ((none, 36), (none, 245), -3*spinScale/5),
    ((none, 37), (none, 222), 3*spinScale/5), ((none, 37), (none, 244), 3*spinScale/5), ((none, 38), (none, 221), -3*spinScale/5), ((none, 38), (none, 243), -3*spinScale/5),
    ((none, 39), (none, 241), 3*spinScale/5), ((none, 40), (none, 241), -3*spinScale/5), ((none, 45), (none, 235), 3*spinScale/5), ((none, 45), (none, 236), -3*spinScale/5),
    ((none, 46), (none, 223), 3*spinScale/5), ((none, 46), (none, 224), -3*spinScale/5), ((none, 47), (none, 221), -3*spinScale/5), ((none, 47), (none, 234), -3*spinScale/5),
    ((none, 48), (none, 222), -3*spinScale/5), ((none, 48), (none, 233), 3*spinScale/5), ((none, 49), (none, 219), 3*spinScale/5), ((none, 49), (none, 232), -3*spinScale/5),
    ((none, 50), (none, 220), 3*spinScale/5), ((none, 50), (none, 231), 3*spinScale/5), ((none, 51), (none, 218), -3*spinScale/5), ((none, 51), (none, 229), -3*spinScale/5),
    ((none, 52), (none, 218), 3*spinScale/5), ((none, 52), (none, 229), 3*spinScale/5), ((some 0, 21), (none, 253), 2), ((some 1, 9), (none, 253), -2),
    ((some 0, 22), (none, 254), 2), ((some 1, 10), (none, 254), -2), ((some 0, 23), (none, 255), 2), ((some 1, 11), (none, 255), -2),
    ((some 0, 24), (none, 256), 2), ((some 1, 12), (none, 256), -2), ((some 0, 25), (none, 257), 2), ((some 1, 13), (none, 257), -2),
    ((some 0, 26), (none, 258), 2), ((some 1, 14), (none, 258), -2), ((some 0, 27), (none, 259), 2), ((some 0, 27), (none, 260), 1),
    ((some 1, 15), (none, 259), -2), ((some 1, 15), (none, 260), -1), ((some 0, 28), (none, 259), 1), ((some 0, 28), (none, 260), 2),
    ((some 1, 16), (none, 259), -1), ((some 1, 16), (none, 260), -2), ((some 0, 29), (none, 261), 2), ((some 1, 17), (none, 261), -2),
    ((some 0, 30), (none, 262), 2), ((some 1, 18), (none, 262), -2), ((some 0, 31), (none, 263), 2), ((some 1, 19), (none, 263), -2),
    ((some 0, 32), (none, 264), 1), ((some 1, 20), (none, 264), -1), ((some 0, 33), (none, 265), 2), ((some 2, 9), (none, 265), -2),
    ((some 0, 34), (none, 266), 2), ((some 2, 10), (none, 266), -2), ((some 0, 35), (none, 267), 2), ((some 2, 11), (none, 267), -2),
    ((some 0, 36), (none, 268), 2), ((some 2, 12), (none, 268), -2), ((some 0, 37), (none, 269), 2), ((some 2, 13), (none, 269), -2),
    ((some 0, 38), (none, 270), 2), ((some 2, 14), (none, 270), -2), ((some 0, 39), (none, 271), 2), ((some 0, 39), (none, 272), 1),
    ((some 2, 15), (none, 271), -2), ((some 2, 15), (none, 272), -1), ((some 0, 40), (none, 271), 1), ((some 0, 40), (none, 272), 2),
    ((some 2, 16), (none, 271), -1), ((some 2, 16), (none, 272), -2), ((some 0, 41), (none, 273), 2), ((some 2, 17), (none, 273), -2),
    ((some 0, 42), (none, 274), 2), ((some 2, 18), (none, 274), -2), ((some 0, 43), (none, 275), 2), ((some 2, 19), (none, 275), -2),
    ((some 0, 44), (none, 276), 1), ((some 2, 20), (none, 276), -1), ((some 0, 45), (none, 277), 2), ((some 3, 9), (none, 277), -2),
    ((some 0, 46), (none, 278), 2), ((some 3, 10), (none, 278), -2), ((some 0, 47), (none, 279), 2), ((some 3, 11), (none, 279), -2),
    ((some 0, 48), (none, 280), 2), ((some 3, 12), (none, 280), -2), ((some 0, 49), (none, 281), 2), ((some 3, 13), (none, 281), -2),
    ((some 0, 50), (none, 282), 2), ((some 3, 14), (none, 282), -2), ((some 0, 51), (none, 283), 2), ((some 0, 51), (none, 284), 1),
    ((some 3, 15), (none, 283), -2), ((some 3, 15), (none, 284), -1), ((some 0, 52), (none, 283), 1), ((some 0, 52), (none, 284), 2),
    ((some 3, 16), (none, 283), -1), ((some 3, 16), (none, 284), -2), ((some 0, 53), (none, 285), 2), ((some 3, 17), (none, 285), -2),
    ((some 0, 54), (none, 286), 2), ((some 3, 18), (none, 286), -2), ((some 0, 55), (none, 287), 2), ((some 3, 19), (none, 287), -2),
    ((some 0, 56), (none, 288), 1), ((some 3, 20), (none, 288), -1), ((some 2, 45), (none, 217), 2), ((some 3, 33), (none, 217), -2),
    ((some 2, 46), (none, 218), 2), ((some 3, 34), (none, 218), -2), ((some 2, 47), (none, 219), 2), ((some 3, 35), (none, 219), -2),
    ((some 2, 48), (none, 220), 2), ((some 3, 36), (none, 220), -2), ((some 2, 49), (none, 221), 2), ((some 3, 37), (none, 221), -2),
    ((some 2, 50), (none, 222), 2), ((some 3, 38), (none, 222), -2), ((some 2, 51), (none, 223), 2), ((some 2, 51), (none, 224), 1),
    ((some 3, 39), (none, 223), -2), ((some 3, 39), (none, 224), -1), ((some 2, 52), (none, 223), 1), ((some 2, 52), (none, 224), 2),
    ((some 3, 40), (none, 223), -1), ((some 3, 40), (none, 224), -2), ((some 2, 53), (none, 225), 2), ((some 3, 41), (none, 225), -2),
    ((some 2, 54), (none, 226), 2), ((some 3, 42), (none, 226), -2), ((some 2, 55), (none, 227), 2), ((some 3, 43), (none, 227), -2),
    ((some 2, 56), (none, 228), 1), ((some 3, 44), (none, 228), -1), ((some 3, 21), (none, 229), 2), ((some 1, 45), (none, 229), -2),
    ((some 3, 22), (none, 230), 2), ((some 1, 46), (none, 230), -2), ((some 3, 23), (none, 231), 2), ((some 1, 47), (none, 231), -2),
    ((some 3, 24), (none, 232), 2), ((some 1, 48), (none, 232), -2), ((some 3, 25), (none, 233), 2), ((some 1, 49), (none, 233), -2),
    ((some 3, 26), (none, 234), 2), ((some 1, 50), (none, 234), -2), ((some 3, 27), (none, 235), 2), ((some 3, 27), (none, 236), 1),
    ((some 1, 51), (none, 235), -2), ((some 1, 51), (none, 236), -1), ((some 3, 28), (none, 235), 1), ((some 3, 28), (none, 236), 2),
    ((some 1, 52), (none, 235), -1), ((some 1, 52), (none, 236), -2), ((some 3, 29), (none, 237), 2), ((some 1, 53), (none, 237), -2),
    ((some 3, 30), (none, 238), 2), ((some 1, 54), (none, 238), -2), ((some 3, 31), (none, 239), 2), ((some 1, 55), (none, 239), -2),
    ((some 3, 32), (none, 240), 1), ((some 1, 56), (none, 240), -1), ((some 1, 33), (none, 241), 2), ((some 2, 21), (none, 241), -2),
    ((some 1, 34), (none, 242), 2), ((some 2, 22), (none, 242), -2), ((some 1, 35), (none, 243), 2), ((some 2, 23), (none, 243), -2),
    ((some 1, 36), (none, 244), 2), ((some 2, 24), (none, 244), -2), ((some 1, 37), (none, 245), 2), ((some 2, 25), (none, 245), -2),
    ((some 1, 38), (none, 246), 2), ((some 2, 26), (none, 246), -2), ((some 1, 39), (none, 247), 2), ((some 1, 39), (none, 248), 1),
    ((some 2, 27), (none, 247), -2), ((some 2, 27), (none, 248), -1), ((some 1, 40), (none, 247), 1), ((some 1, 40), (none, 248), 2),
    ((some 2, 28), (none, 247), -1), ((some 2, 28), (none, 248), -2), ((some 1, 41), (none, 249), 2), ((some 2, 29), (none, 249), -2),
    ((some 1, 42), (none, 250), 2), ((some 2, 30), (none, 250), -2), ((some 1, 43), (none, 251), 2), ((some 2, 31), (none, 251), -2),
    ((some 1, 44), (none, 252), 1), ((some 2, 32), (none, 252), -1)
  ]

def literalGaugeBFQuadratic (jet : NativeFirstJet) : ℝ :=
  (literalGaugeBFTerms.map fun t => t.2.2 * gaugeLiteralRead jet t.1 * gaugeLiteralRead jet t.2.1).sum


def literalGaugeAATerms : List (GaugeLiteralIndex × GaugeLiteralIndex × ℝ) :=
  [
    ((none, 21), (none, 34), 4*(25*lapse/3)/5), ((none, 22), (none, 33), -4*(25*lapse/3)/5), ((none, 22), (none, 51), -2*(25*lapse/3)/5), ((none, 22), (none, 52), 2*(25*lapse/3)/5),
    ((none, 23), (none, 36), 2*(25*lapse/3)/5), ((none, 23), (none, 49), 2*(25*lapse/3)/5), ((none, 24), (none, 35), -2*(25*lapse/3)/5), ((none, 24), (none, 50), 2*(25*lapse/3)/5),
    ((none, 25), (none, 38), -2*(25*lapse/3)/5), ((none, 25), (none, 47), -2*(25*lapse/3)/5), ((none, 26), (none, 37), 2*(25*lapse/3)/5), ((none, 26), (none, 48), -2*(25*lapse/3)/5),
    ((none, 27), (none, 46), 2*(25*lapse/3)/5), ((none, 28), (none, 46), -2*(25*lapse/3)/5), ((none, 33), (none, 51), -2*(25*lapse/3)/5), ((none, 33), (none, 52), 2*(25*lapse/3)/5),
    ((none, 35), (none, 50), 2*(25*lapse/3)/5), ((none, 36), (none, 49), -2*(25*lapse/3)/5), ((none, 37), (none, 48), 2*(25*lapse/3)/5), ((none, 38), (none, 47), -2*(25*lapse/3)/5),
    ((none, 39), (none, 45), 2*(25*lapse/3)/5), ((none, 40), (none, 45), -2*(25*lapse/3)/5)
  ]

def literalGaugeAAQuadratic (jet : NativeFirstJet) : ℝ :=
  (literalGaugeAATerms.map fun t => t.2.2 * gaugeLiteralRead jet t.1 * gaugeLiteralRead jet t.2.1).sum


def literalGaugeEBTerms : List (GaugeLiteralIndex × GaugeLiteralIndex × ℝ) :=
  [
    ((none, 57), (none, 218), (25*lapse/3)/5), ((none, 57), (none, 229), (25*lapse/3)/5), ((none, 57), (none, 247), (25*lapse/3)/10), ((none, 57), (none, 248), -(25*lapse/3)/10),
    ((none, 58), (none, 271), -(25*lapse/3)/10), ((none, 58), (none, 272), (25*lapse/3)/10), ((none, 58), (none, 277), (25*lapse/3)/5), ((none, 59), (none, 259), (25*lapse/3)/10),
    ((none, 59), (none, 260), -(25*lapse/3)/10), ((none, 59), (none, 278), -(25*lapse/3)/5), ((none, 60), (none, 253), -(25*lapse/3)/5), ((none, 60), (none, 266), (25*lapse/3)/5),
    ((none, 61), (none, 271), 5/6), ((none, 61), (none, 272), -5/6), ((none, 61), (none, 277), -5/3), ((none, 62), (none, 218), 18/25),
    ((none, 62), (none, 229), -18/25), ((none, 62), (none, 247), -9/25), ((none, 62), (none, 248), 9/25), ((none, 63), (none, 217), 18/25),
    ((none, 63), (none, 230), 18/25), ((none, 64), (none, 223), 9/25), ((none, 64), (none, 224), -9/25), ((none, 64), (none, 242), 18/25),
    ((none, 65), (none, 259), -5/6), ((none, 65), (none, 260), 5/6), ((none, 65), (none, 278), 5/3), ((none, 66), (none, 217), 18/25),
    ((none, 66), (none, 230), 18/25), ((none, 67), (none, 218), -18/25), ((none, 67), (none, 229), 18/25), ((none, 67), (none, 247), -9/25),
    ((none, 67), (none, 248), 9/25), ((none, 68), (none, 235), 9/25), ((none, 68), (none, 236), -9/25), ((none, 68), (none, 241), 18/25),
    ((none, 69), (none, 253), 5/3), ((none, 69), (none, 266), -5/3), ((none, 70), (none, 223), 9/25), ((none, 70), (none, 224), -9/25),
    ((none, 70), (none, 242), 18/25), ((none, 71), (none, 235), 9/25), ((none, 71), (none, 236), -9/25), ((none, 71), (none, 241), 18/25),
    ((none, 72), (none, 218), -18/25), ((none, 72), (none, 229), -18/25), ((none, 72), (none, 247), 9/25), ((none, 72), (none, 248), -9/25)
  ]

def literalGaugeEBQuadratic (jet : NativeFirstJet) : ℝ :=
  (literalGaugeEBTerms.map fun t => t.2.2 * gaugeLiteralRead jet t.1 * gaugeLiteralRead jet t.2.1).sum


def literalGaugeEETerms : List (GaugeLiteralIndex × GaugeLiteralIndex × ℝ) :=
  [
    ((none, 57), (none, 62), -3/5), ((none, 57), (none, 67), -3/5), ((none, 57), (none, 72), -3/5), ((none, 58), (none, 61), 3/5),
    ((none, 59), (none, 65), 3/5), ((none, 60), (none, 69), 3/5), ((none, 61), (none, 61), -(25*lapse/3)/3), ((none, 62), (none, 62), 18*(25*lapse/3)/125),
    ((none, 62), (none, 67), -9*(25*lapse/3)/125), ((none, 62), (none, 72), -9*(25*lapse/3)/125), ((none, 63), (none, 63), 9*(25*lapse/3)/125), ((none, 63), (none, 66), 27*(25*lapse/3)/125),
    ((none, 64), (none, 64), 9*(25*lapse/3)/125), ((none, 64), (none, 70), 27*(25*lapse/3)/125), ((none, 65), (none, 65), -(25*lapse/3)/3), ((none, 66), (none, 66), 9*(25*lapse/3)/125),
    ((none, 67), (none, 67), 18*(25*lapse/3)/125), ((none, 67), (none, 72), -9*(25*lapse/3)/125), ((none, 68), (none, 68), 9*(25*lapse/3)/125), ((none, 68), (none, 71), 27*(25*lapse/3)/125),
    ((none, 69), (none, 69), -(25*lapse/3)/3), ((none, 70), (none, 70), 9*(25*lapse/3)/125), ((none, 71), (none, 71), 9*(25*lapse/3)/125), ((none, 72), (none, 72), 18*(25*lapse/3)/125)
  ]

def literalGaugeEEQuadratic (jet : NativeFirstJet) : ℝ :=
  (literalGaugeEETerms.map fun t => t.2.2 * gaugeLiteralRead jet t.1 * gaugeLiteralRead jet t.2.1).sum


def gaugeSparseAdTerms : List (Fin 12 × Fin 12 × Fin 12 × ℚ) :=
  [
    (0, 6, 1, 2), (0, 7, 1, -2), (0, 4, 2, -1), (0, 5, 3, -1), (0, 2, 4, 1), (0, 3, 5, 1),
    (0, 1, 6, -1), (0, 1, 7, 1), (1, 6, 0, -2), (1, 7, 0, 2), (1, 5, 2, 1), (1, 4, 3, -1),
    (1, 3, 4, 1), (1, 2, 5, -1), (1, 0, 6, 1), (1, 0, 7, -1), (2, 4, 0, 1), (2, 5, 1, -1),
    (2, 6, 3, 2), (2, 0, 4, -1), (2, 1, 5, 1), (2, 3, 6, -2), (2, 3, 7, -1), (3, 5, 0, 1),
    (3, 4, 1, 1), (3, 6, 2, -2), (3, 1, 4, -1), (3, 0, 5, -1), (3, 2, 6, 2), (3, 2, 7, 1),
    (4, 2, 0, -1), (4, 3, 1, -1), (4, 0, 2, 1), (4, 1, 3, 1), (4, 7, 5, 2), (4, 5, 6, -1),
    (4, 5, 7, -2), (5, 3, 0, -1), (5, 2, 1, 1), (5, 1, 2, -1), (5, 0, 3, 1), (5, 7, 4, -2),
    (5, 4, 6, 1), (5, 4, 7, 2), (6, 1, 0, 1), (6, 0, 1, -1), (6, 3, 2, 2), (6, 2, 3, -2),
    (6, 5, 4, 1), (6, 4, 5, -1), (7, 1, 0, -1), (7, 0, 1, 1), (7, 3, 2, 1), (7, 2, 3, -1),
    (7, 5, 4, 2), (7, 4, 5, -2), (8, 10, 9, 2), (8, 9, 10, -2), (9, 10, 8, -2), (9, 8, 10, 2),
    (10, 9, 8, 2), (10, 8, 9, -2)
  ]

def gaugeSparseAd (a i b : Fin 12) : ℚ :=
  (gaugeSparseAdTerms.map fun t => if t.1=a ∧ t.2.1=i ∧ t.2.2.1=b then t.2.2.2 else 0).sum

theorem gaugeSparseAd_source : ∀ a i b : Fin 12, originalAd a i b = gaugeSparseAd a i b := by
  decide +kernel

private theorem gaugeBracket_list_read (terms : List (Fin 12 × Fin 12 × Fin 12 × ℚ))
    (x y : Fin 12 → ℝ) (i : Fin 12) :
    (∑ a : Fin 12, ∑ b : Fin 12,
      ((terms.map fun t => if t.1=a ∧ t.2.1=i ∧ t.2.2.1=b then t.2.2.2 else 0).sum : ℚ) * x a * y b) =
      (terms.map fun t => if t.2.1=i then (t.2.2.2 : ℝ)*x t.1*y t.2.2.1 else 0).sum := by
  induction terms with
  | nil => simp
  | cons t rest ih =>
    simp only [List.map_cons, List.sum_cons, Rat.cast_add, add_mul, Finset.sum_add_distrib]
    rw [ih]
    congr 1
    by_cases hi : t.2.1=i
    · simp [hi, apply_ite, Rat.cast_zero, mul_ite, ite_mul, ite_and, eq_comm]
    · simp [hi]

theorem gaugeOriginalBracket_sparse (x y : Fin 12 → ℝ) (i : Fin 12) :
    gaugeOriginalBracket x y i =
      (gaugeSparseAdTerms.map fun t =>
        if t.2.1=i then (t.2.2.2 : ℝ)*x t.1*y t.2.2.1 else 0).sum := by
  unfold gaugeOriginalBracket
  simp_rw [gaugeSparseAd_source]
  exact gaugeBracket_list_read gaugeSparseAdTerms x y i

def gaugeEBQuadratic (jet : NativeFirstJet) : ℝ :=
  -(positiveSmoothUnifiedSource.legacy.sigma / 2) * ∑ pair : Fin 6, ∑ input : Fin 6,
    nativeHodgeFirst (homogeneousCoframe lapse) (fieldCoframe jet.1)
      (StageNineTopologicalFourFormPairing.twoFormComplement pair) input *
    (rawGaugePair (fieldGaugeB jet.1 pair) (gaugeAuxiliaryRaw input) +
      rawGaugePair (gaugeAuxiliaryRaw pair) (fieldGaugeB jet.1 input))

def gaugeBFQuadratic (jet : NativeFirstJet) : ℝ :=
  ∑ pair : Fin 6, rawGaugePair (fieldGaugeB jet.1 pair)
    (gaugeLinearRaw jet (StageNineTopologicalFourFormPairing.twoFormComplement pair))

theorem gaugeBFQuadratic_literal (jet : NativeFirstJet) : gaugeBFQuadratic jet = literalGaugeBFQuadratic jet := by
  unfold gaugeBFQuadratic gaugeLinearRaw
  simp [rawGaugePair, gaugeFieldRaw, fieldGaugeB, gaugeBSlot, gaugeSlot,
    gaugeBackgroundRaw, gaugeColorRaw, Pi.single_apply,
    StageNineTopologicalFourFormPairing.twoFormComplement, pairFirst, pairSecond,
    Fin.sum_univ_six, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
    literalGaugeBFQuadratic, literalGaugeBFTerms, gaugeLiteralRead]
  simp_rw [gaugeOriginalBracket_sparse]
  norm_num [gaugeSparseAdTerms, List.map_cons, List.sum_cons, List.map_nil, List.sum_nil,
    gaugeBackgroundRaw, gaugeColorRaw, gaugeFieldRaw, Pi.single_apply,
    gaugeScale, gaugeSlot]
  simp only [Fin.reduceSucc, Fin.reduceEq, Fin.isValue, Fin.reduceFinMk, if_true, if_false]
  ring_nf!

def gaugeAAQuadratic (jet : NativeFirstJet) : ℝ :=
  ∑ pair : Fin 6, rawGaugePair (gaugeAuxiliaryRaw pair)
    (gaugeQuadraticRaw jet (StageNineTopologicalFourFormPairing.twoFormComplement pair))

theorem gaugeAAQuadratic_literal (jet : NativeFirstJet) : gaugeAAQuadratic jet = literalGaugeAAQuadratic jet := by
  unfold gaugeAAQuadratic gaugeQuadraticRaw
  simp [gaugeOriginalBracket_sparse, gaugeSparseAdTerms, rawGaugePair, gaugeAuxiliaryRaw, gaugeColorRaw,
    sourceCoupling_eq, gaugeFieldRaw, gaugeSlot, Pi.single_apply,
    StageNineTopologicalFourFormPairing.twoFormComplement, pairFirst, pairSecond,
    Fin.sum_univ_six, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
    literalGaugeAAQuadratic, literalGaugeAATerms, gaugeLiteralRead]
  simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, lapseInv_source]
  norm_num [gaugeScale, div_pow, mul_pow, spinScale_sq]
  ring_nf!


theorem gaugeEBQuadratic_literal (jet : NativeFirstJet) : gaugeEBQuadratic jet = literalGaugeEBQuadratic jet := by
  have sigma : positiveSmoothUnifiedSource.legacy.sigma = (1/2 : ℝ) := sourceCoupling_eq
  unfold gaugeEBQuadratic
  simp_rw [nativeHodgeFirst_flat]
  norm_num [sigma, sourceCoupling_eq, gaugeAuxiliaryRaw, gaugeColorRaw, nativeHodgeFirstFlat,
    StageNineTopologicalFourFormPairing.twoFormComplement, Fin.sum_univ_six,
    rawGaugePair, fieldCoframe, coframeSlot, fieldGaugeB, gaugeBSlot, Pi.single_apply,
    Pi.smul_apply, smul_eq_mul, literalGaugeEBQuadratic, literalGaugeEBTerms, gaugeLiteralRead]
  simp only [Fin.reduceSucc, Fin.reduceEq, Fin.isValue, Fin.reduceFinMk, if_true, if_false]
  dsimp only [Matrix.vecCons, Fin.cons, Fin.cases, Fin.induction, Fin.induction.go]
  norm_num [Fin.val_ofNat, Fin.val_zero, Fin.coe_ofNat_eq_mod, Fin.val_natCast, nativeHodgeFirstFlat, nativeHodgeSecondFlat]
  simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, lapseInv_source]
  norm_num [gaugeScale, div_pow, mul_pow, spinScale_sq]
  ring_nf!
  simp only [lapse_sq]
  ring_nf!

def gaugeEEQuadratic (jet : NativeFirstJet) : ℝ :=
  -(positiveSmoothUnifiedSource.legacy.sigma / 2) * ∑ pair : Fin 6, ∑ input : Fin 6,
    nativeHodgeSecond (homogeneousCoframe lapse) (fieldCoframe jet.1)
      (StageNineTopologicalFourFormPairing.twoFormComplement pair) input *
    rawGaugePair (gaugeAuxiliaryRaw pair) (gaugeAuxiliaryRaw input)

theorem gaugeEEQuadratic_literal (jet : NativeFirstJet) : gaugeEEQuadratic jet = literalGaugeEEQuadratic jet := by
  have sigma : positiveSmoothUnifiedSource.legacy.sigma = (1/2 : ℝ) := sourceCoupling_eq
  unfold gaugeEEQuadratic
  simp_rw [nativeHodgeSecond_flat]
  norm_num [sigma, sourceCoupling_eq, gaugeAuxiliaryRaw, gaugeColorRaw, nativeHodgeSecondFlat,
    StageNineTopologicalFourFormPairing.twoFormComplement, Fin.sum_univ_six,
    rawGaugePair, fieldCoframe, coframeSlot, Pi.single_apply,
    Pi.smul_apply, smul_eq_mul, literalGaugeEEQuadratic, literalGaugeEETerms, gaugeLiteralRead]
  simp only [Fin.reduceSucc, Fin.reduceEq, Fin.isValue, Fin.reduceFinMk, if_true, if_false]
  dsimp only [Matrix.vecCons, Fin.cons, Fin.cases, Fin.induction, Fin.induction.go]
  norm_num [Fin.val_ofNat, Fin.val_zero, Fin.coe_ofNat_eq_mod, Fin.val_natCast, nativeHodgeFirstFlat, nativeHodgeSecondFlat]
  simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, lapseInv_source]
  norm_num [gaugeScale, div_pow, mul_pow, spinScale_sq]
  ring_nf!
  have cube : lapse^3 = (54/125 : ℝ)*lapse := by
    calc
      lapse^3 = lapse^2*lapse := by ring
      _ = (54/125 : ℝ)*lapse := by rw [lapse_sq]
  rw [cube]
  simp only [lapse_sq]
  ring_nf!

theorem gaugeFlatQuadratic_blocks (jet : NativeFirstJet) :
    gaugeFlatQuadratic jet = gaugeBFQuadratic jet + gaugeAAQuadratic jet +
      gaugeBBQuadratic jet + gaugeEBQuadratic jet + gaugeEEQuadratic jet := by
  unfold gaugeFlatQuadratic gaugeBFQuadratic gaugeAAQuadratic gaugeBBQuadratic gaugeEBQuadratic gaugeEEQuadratic
  simp only [Finset.sum_add_distrib]
  ring


theorem literalGaugeQuadratic_blocks (jet : NativeFirstJet) :
    literalGaugeQuadratic jet = literalGaugeBFQuadratic jet + literalGaugeAAQuadratic jet +
      literalGaugeBBQuadratic jet + literalGaugeEBQuadratic jet + literalGaugeEEQuadratic jet := by
  simp only [literalGaugeQuadratic, literalGaugeTerms, literalGaugeBFQuadratic, literalGaugeBFTerms,
    literalGaugeAAQuadratic, literalGaugeAATerms, literalGaugeBBQuadratic, literalGaugeBBTerms,
    literalGaugeEBQuadratic, literalGaugeEBTerms, literalGaugeEEQuadratic, literalGaugeEETerms,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  ring

theorem nativeGaugeQuadratic_literal (jet : NativeFirstJet) :
    nativeGaugeQuadratic jet = literalGaugeQuadratic jet := by
  rw [nativeGaugeQuadratic_flat, gaugeFlatQuadratic_blocks, gaugeBFQuadratic_literal,
    gaugeAAQuadratic_literal, gaugeBBQuadratic_literal, gaugeEBQuadratic_literal,
    gaugeEEQuadratic_literal, literalGaugeQuadratic_blocks]

def literalGaugeHessian : NativeFirstJet →L[ℝ] NativeFirstJet →L[ℝ] ℝ :=
  (literalGaugeTerms.map fun term => term.2.2 •
    ((nativeCoefficientCLM term.1).smulRight (nativeCoefficientCLM term.2.1) +
      (nativeCoefficientCLM term.2.1).smulRight (nativeCoefficientCLM term.1))).sum

theorem literalGaugeHessian_value (a b : NativeFirstJet) : literalGaugeHessian a b =
    (literalGaugeTerms.map fun term => term.2.2 *
      (nativeJetCoefficient a term.1 * nativeJetCoefficient b term.2.1 +
        nativeJetCoefficient a term.2.1 * nativeJetCoefficient b term.1)).sum := by
  unfold literalGaugeHessian
  generalize literalGaugeTerms=terms
  induction terms with
  | nil => simp
  | cons term terms ih =>
    simp only [List.map_cons, List.sum_cons, add_apply, ih, smul_apply, smul_eq_mul,
      ContinuousLinearMap.smulRight_apply]
    rfl

private theorem literalGaugeHessian_diagonal (jet : NativeFirstJet) :
    literalGaugeHessian jet jet = 2*literalGaugeQuadratic jet := by
  rw [literalGaugeHessian_value]
  unfold literalGaugeQuadratic
  change _ = 2 * (literalGaugeTerms.map fun term =>
    term.2.2 * nativeJetCoefficient jet term.1 * nativeJetCoefficient jet term.2.1).sum
  rw [←List.sum_map_mul_left]
  congr 1
  apply List.map_congr_left
  intro term _
  ring

private theorem literalGaugeHessian_symmetric (a b : NativeFirstJet) :
    literalGaugeHessian a b = literalGaugeHessian b a := by
  rw [literalGaugeHessian_value, literalGaugeHessian_value]
  congr 1
  apply List.map_congr_left
  intro term _
  ring

private theorem gauge_symmetric_diagonal_unique {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (B C : E →L[ℝ] E →L[ℝ] ℝ) (bSym : ∀ x y, B x y=B y x)
    (cSym : ∀ x y, C x y=C y x) (diag : ∀ x, B x x=C x x) (a b : E) :
    B a b = C a b := by
  have h := diag (a+b)
  simp only [map_add, add_apply] at h
  rw [bSym b a, cSym b a, diag a, diag b] at h
  linarith

theorem nativeGaugeHessian_literal (a b : NativeFirstJet) :
    nativeBlockHessian 1 a b = literalGaugeHessian a b := by
  apply gauge_symmetric_diagonal_unique _ _ (nativeBlockHessian_symmetric 1) literalGaugeHessian_symmetric
  intro jet
  change fderiv ℝ (fderiv ℝ nativeGaugeDensity) 0 jet jet = _
  rw [nativeGaugeHessian_generated, nativeGaugeQuadratic_literal, literalGaugeHessian_diagonal]

theorem nativeGaugeFourier_literal (p : Fin 4 → ℂ) :
    nativeBlockJacobi 1 p = nativeFourierHessian literalGaugeHessian p := by
  have H : nativeBlockHessian 1 = literalGaugeHessian := by
    apply ContinuousLinearMap.ext
    intro a
    apply ContinuousLinearMap.ext
    intro b
    exact nativeGaugeHessian_literal a b
  rw [nativeBlockJacobi, H]

end LowEnergy.SourcePropagationNativeActionHessian
