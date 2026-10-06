import H0mework.Versions.CAP.Physics.LowEnergy.Quantum.SourceQuantumResidualGaugeSlice
import Mathlib.LinearAlgebra.Matrix.Rank
import H0mework.Versions.R2.Physics.SpinPair.GaugeField

/-! The actual native bracket supplies a unit central direction. The same
SpinPair connection supplies a rank-three magnetic Gram, and hence a nonzero
minor of the original connection-curvature polynomial. -/

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
namespace LowEnergy.SourceQuantumGaugeCenterMagnetic
open SaturationMonoid.PhysicsCore
open ProofFreeRicherAnholonomicSource
open SU7MotherLieAlgebra SU7MotherGaugeTheory StageNineHolonomicField
open StageNineCoframeGravityGaugeRegularity Stage9C.Material.SpinPair
open StageNineP286GaugeAuxiliaryVariation StageNineGlobalIntegratedAction
open StageNineFormNativeP286GaugeGeometricKinematics
open SourceQuantumScalarChart SourceQuantumNativeDimensions SourceQuantumResidualGaugeSlice
open scoped RealInnerProductSpace

private def centerBlock : P286LieBlockData := (0, 0, ⟨Complex.I, by change star Complex.I = -Complex.I; simp⟩)
def sourceCenter : NativeLie := p286CoordinateEquiv centerBlock

theorem sourceCenter_bracket (a : NativeLie) :
    jointP286CoordinateLieBracket sourceCenter a = 0 := by
  unfold jointP286CoordinateLieBracket sourceCenter
  rw [p286CoordinateEquiv.symm_apply_apply]
  have h : p286LieBracket centerBlock (p286CoordinateEquiv.symm a) = 0 := by
    simp [centerBlock, p286LieBracket, suLieBracket]
  rw [h, map_zero]

theorem bracket_sourceCenter (a : NativeLie) :
    jointP286CoordinateLieBracket a sourceCenter = 0 := by
  unfold jointP286CoordinateLieBracket sourceCenter
  rw [p286CoordinateEquiv.symm_apply_apply]
  have h : p286LieBracket (p286CoordinateEquiv.symm a) centerBlock = 0 := by
    simp [centerBlock, p286LieBracket, suLieBracket]
  rw [h, map_zero]

theorem sourceCenter_inner : ⟪sourceCenter, sourceCenter⟫ = (1 : ℝ) := by
  change p286LiePairing (p286CoordinateEquiv.symm (p286CoordinateEquiv centerBlock))
    (p286CoordinateEquiv.symm (p286CoordinateEquiv centerBlock)) = 1
  simp [centerBlock, p286LiePairing, specialUnitaryLiePairing, hyperchargeLiePairing]

theorem sourceCenter_norm : ‖sourceCenter‖ = 1 := by
  have h := sourceCenter_inner
  rw [real_inner_self_eq_norm_sq] at h
  nlinarith [norm_nonneg sourceCenter]

theorem sourceCenter_nonzero : sourceCenter ≠ 0 := by
  intro h
  simpa [h] using sourceCenter_inner

theorem sourceCenter_norm_pos : 0 < ‖sourceCenter‖ := by rw [sourceCenter_norm]; norm_num

theorem sourceCenter_projection (a : NativeLie) :
    ⟪sourceCenter, a⟫ = (nativeCoordinates a).2.2 := by
  obtain ⟨b, rfl⟩ := p286CoordinateEquiv.surjective a
  rw [nativeCoordinates_apply]
  change p286LiePairing (p286CoordinateEquiv.symm (p286CoordinateEquiv centerBlock))
    (p286CoordinateEquiv.symm (p286CoordinateEquiv b)) = _
  simp [centerBlock, p286LiePairing, specialUnitaryLiePairing, hyperchargeLiePairing,
    Complex.mul_re]

theorem sourceCenter_bracket_projection (a b : NativeLie) :
    ⟪sourceCenter, (jointP286CoordinateLieBracket a b : NativeLie)⟫ = 0 := by
  erw [sourceCenter_projection]
  unfold jointP286CoordinateLieBracket
  rw [nativeCoordinates_apply]
  rfl

private theorem colorGenerator_pairing (i j : Fin 3) :
    ⟪colorGenerator i, colorGenerator j⟫ = if i = j then (1/2 : ℝ) else 0 := by
  change p286LiePairing (p286CoordinateEquiv.symm (p286CoordinateEquiv (sourceColorP286Generator i)))
    (p286CoordinateEquiv.symm (p286CoordinateEquiv (sourceColorP286Generator j))) = _
  simp only [p286CoordinateEquiv.symm_apply_apply]
  rw [sourceColorP286Generator_pairing, sourceColorP286Generator_color]
  fin_cases i <;> fin_cases j <;> norm_num [sourceColorRaw]

def actualMagnetic (point : BasePoint) (i : Fin 3) : NativeLie :=
  p286CoordinateEquiv (holonomicGaugeCurvature actual point ⟨i.val+3, by omega⟩)

theorem actualMagnetic_eq (point : BasePoint) (i : Fin 3) :
    actualMagnetic point i = -(gaugeScale^2) • colorGenerator i := by
  unfold actualMagnetic
  rw [actual_gaugeCurvature]
  fin_cases i <;> simp [magneticCurvature, colorGenerator, neg_smul]
  all_goals exact (neg_smul (gaugeScale^2) _).symm

def actualMagneticGram (point : BasePoint) : Matrix (Fin 3) (Fin 3) ℝ :=
  fun i j => ⟪actualMagnetic point i, actualMagnetic point j⟫

theorem actualMagneticGram_eq (point : BasePoint) :
    actualMagneticGram point = (162/625 : ℝ) • (1 : Matrix (Fin 3) (Fin 3) ℝ) := by
  ext i j
  simp only [actualMagneticGram, actualMagnetic_eq, inner_smul_left, inner_smul_right,
    RCLike.conj_to_real, colorGenerator_pairing]
  by_cases hij : i=j
  · subst j
    simp only [ite_true, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one]
    norm_num [gaugeScale, div_pow, mul_pow, spinScale_sq]
  · simp [hij]

theorem actualMagneticGram_minor (point : BasePoint) :
    ((actualMagneticGram point).submatrix (Fin.castAdd 1 : Fin 2 → Fin 3) (Fin.castAdd 1 : Fin 2 → Fin 3)).det =
      (26244/390625 : ℝ) := by
  rw [actualMagneticGram_eq]
  norm_num [Matrix.det_fin_two, Matrix.submatrix, Matrix.smul_apply, Matrix.one_apply]

theorem actualMagneticGram_minor_pos (point : BasePoint) :
    0 < ((actualMagneticGram point).submatrix (Fin.castAdd 1 : Fin 2 → Fin 3)
      (Fin.castAdd 1 : Fin 2 → Fin 3)).det := by
  rw [actualMagneticGram_minor]; norm_num

theorem actualMagneticGram_det (point : BasePoint) :
    (actualMagneticGram point).det = (4251528/244140625 : ℝ) := by
  rw [actualMagneticGram_eq, Matrix.det_smul]
  norm_num

theorem actualMagneticGram_rank (point : BasePoint) :
    (actualMagneticGram point).rank = 3 := by
  have h : (actualMagneticGram point).det ≠ 0 := by
    rw [actualMagneticGram_det]; norm_num
  simpa using Matrix.rank_mul_eq_left_of_det_ne_zero
    (actualMagneticGram point) (1 : Matrix (Fin 3) (Fin 3) ℝ) h

/-- The curvature polynomial uses the same bracket and original connection carrier. -/
def magneticOfConnection (A : Fin 3 → NativeLie) : Fin 3 → NativeLie :=
  ![jointP286CoordinateLieBracket (A 1) (A 2),
    jointP286CoordinateLieBracket (A 2) (A 0),
    jointP286CoordinateLieBracket (A 0) (A 1)]

def connectionMagneticGram (A : Fin 3 → NativeLie) : Matrix (Fin 3) (Fin 3) ℝ :=
  fun i j => ⟪magneticOfConnection A i, magneticOfConnection A j⟫

private theorem nativeBracket_smul (r s : ℝ) (a b : NativeLie) :
    (jointP286CoordinateLieBracket (r • a) (s • b) : NativeLie) =
      (r*s) • (jointP286CoordinateLieBracket a b : NativeLie) := by
  erw [jointP286CoordinateLieBracket_smul_left, jointP286CoordinateLieBracket_smul_right,
    smul_smul]

theorem magneticOfConnection_source (point : BasePoint) :
    magneticOfConnection (gaugeCoordinates SourceQuantumResidualGaugeSlice.sourceGauge) =
      actualMagnetic point := by
  funext i
  simp only [magneticOfConnection, sourceGauge_apply, nativeBracket_smul,
    colorGenerator_bracket, actualMagnetic_eq]
  fin_cases i <;> simp [neg_smul, pow_two]
  all_goals exact smul_neg _ _

theorem connectionMagneticGram_source (point : BasePoint) :
    connectionMagneticGram (gaugeCoordinates SourceQuantumResidualGaugeSlice.sourceGauge) =
      actualMagneticGram point := by
  ext i j
  simp only [connectionMagneticGram, actualMagneticGram, magneticOfConnection_source point]

/-- The two-row magnetic minor is not the zero function of the native connection. -/
theorem connectionMagneticGram_minor_not_zero :
    (fun A : Fin 3 → NativeLie =>
      ((connectionMagneticGram A).submatrix (Fin.castAdd 1 : Fin 2 → Fin 3)
        (Fin.castAdd 1 : Fin 2 → Fin 3)).det) ≠ 0 := by
  intro h
  have hs := congrFun h (gaugeCoordinates SourceQuantumResidualGaugeSlice.sourceGauge)
  rw [connectionMagneticGram_source (0 : BasePoint), actualMagneticGram_minor] at hs
  norm_num at hs

end LowEnergy.SourceQuantumGaugeCenterMagnetic
