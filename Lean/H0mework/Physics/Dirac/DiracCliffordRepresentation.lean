import Mathlib.LinearAlgebra.Matrix.Hermitian
import H0mework.Physics.Geometry.PointwiseLeviCivitaRecovery

/-!
# Explicit Dirac/Clifford representation for the generated Lorentz geometry

This module constructs four concrete complex `4 × 4` gamma matrices in the
same `(-,+,+,+)` convention used by the physics-core coframe geometry.  It
proves the Clifford anticommutator from the entries, derives `gammaFive` from
their product, and proves the left/right chirality projectors are complementary
idempotents.

No Clifford law, chirality Boolean, or left/right label is accepted as input.
This is a finite pointwise Dirac carrier; its coupling to the generated
`so(1,3)` connection and to the Stage-7 internal matter carrier is kept in
downstream modules.
-/

namespace SaturationMonoid.PhysicsCore.DiracCliffordRepresentation

open scoped Matrix

noncomputable section

attribute [local simp] Matrix.cons_val_two Matrix.cons_val_three

abbrev DiracSpinorIndex := Fin 4
abbrev DiracSpinorCarrier := DiracSpinorIndex → ℂ
abbrev DiracMatrix := Matrix DiracSpinorIndex DiracSpinorIndex ℂ

def diracGammaZero : DiracMatrix :=
  !![0, 0, 1, 0;
     0, 0, 0, 1;
     -1, 0, 0, 0;
     0, -1, 0, 0]

def diracGammaOne : DiracMatrix :=
  !![0, 0, 0, 1;
     0, 0, 1, 0;
     0, 1, 0, 0;
     1, 0, 0, 0]

def diracGammaTwo : DiracMatrix :=
  !![0, 0, 0, -Complex.I;
     0, 0, Complex.I, 0;
     0, -Complex.I, 0, 0;
     Complex.I, 0, 0, 0]

def diracGammaThree : DiracMatrix :=
  !![0, 0, 1, 0;
     0, 0, 0, -1;
     1, 0, 0, 0;
     0, -1, 0, 0]

def diracGamma : LorentzianIndex → DiracMatrix :=
  ![diracGammaZero, diracGammaOne, diracGammaTwo, diracGammaThree]

def complexMinkowskiEntry
    (first second : LorentzianIndex) : ℂ :=
  (minkowskiInternalMetric first second : ℂ)

@[simp] theorem diracGammaZero_sq :
    diracGammaZero * diracGammaZero = -(1 : DiracMatrix) := by
  ext row column
  fin_cases row <;> fin_cases column <;>
    norm_num [diracGammaZero, Matrix.mul_apply, Fin.sum_univ_four,
      Fin.coe_ofNat_eq_mod, Matrix.cons_val, Nat.reduceMod]

@[simp] theorem diracGammaOne_sq :
    diracGammaOne * diracGammaOne = (1 : DiracMatrix) := by
  ext row column
  fin_cases row <;> fin_cases column <;>
    norm_num [diracGammaOne, Matrix.mul_apply, Fin.sum_univ_four,
      Fin.coe_ofNat_eq_mod, Matrix.cons_val, Nat.reduceMod]

@[simp] theorem diracGammaTwo_sq :
    diracGammaTwo * diracGammaTwo = (1 : DiracMatrix) := by
  ext row column
  fin_cases row <;> fin_cases column <;>
    norm_num [diracGammaTwo, Matrix.mul_apply, Fin.sum_univ_four,
      Fin.coe_ofNat_eq_mod, Matrix.cons_val, Nat.reduceMod]

@[simp] theorem diracGammaThree_sq :
    diracGammaThree * diracGammaThree = (1 : DiracMatrix) := by
  ext row column
  fin_cases row <;> fin_cases column <;>
    norm_num [diracGammaThree, Matrix.mul_apply, Fin.sum_univ_four,
      Fin.coe_ofNat_eq_mod, Matrix.cons_val, Nat.reduceMod]

@[simp] theorem diracGammaZeroOne_anticommute :
    diracGammaZero * diracGammaOne +
        diracGammaOne * diracGammaZero = 0 := by
  ext row column
  fin_cases row <;> fin_cases column <;>
    norm_num [diracGammaZero, diracGammaOne,
      Matrix.mul_apply, Fin.sum_univ_four, Fin.coe_ofNat_eq_mod,
      Matrix.cons_val, Nat.reduceMod]

@[simp] theorem diracGammaZeroTwo_anticommute :
    diracGammaZero * diracGammaTwo +
        diracGammaTwo * diracGammaZero = 0 := by
  ext row column
  fin_cases row <;> fin_cases column <;>
    norm_num [diracGammaZero, diracGammaTwo,
      Matrix.mul_apply, Fin.sum_univ_four, Fin.coe_ofNat_eq_mod,
      Matrix.cons_val, Nat.reduceMod]

@[simp] theorem diracGammaZeroThree_anticommute :
    diracGammaZero * diracGammaThree +
        diracGammaThree * diracGammaZero = 0 := by
  ext row column
  fin_cases row <;> fin_cases column <;>
    norm_num [diracGammaZero, diracGammaThree,
      Matrix.mul_apply, Fin.sum_univ_four, Fin.coe_ofNat_eq_mod,
      Matrix.cons_val, Nat.reduceMod]

@[simp] theorem diracGammaOneTwo_anticommute :
    diracGammaOne * diracGammaTwo +
        diracGammaTwo * diracGammaOne = 0 := by
  ext row column
  fin_cases row <;> fin_cases column <;>
    norm_num [diracGammaOne, diracGammaTwo,
      Matrix.mul_apply, Fin.sum_univ_four, Fin.coe_ofNat_eq_mod,
      Matrix.cons_val, Nat.reduceMod]

@[simp] theorem diracGammaOneThree_anticommute :
    diracGammaOne * diracGammaThree +
        diracGammaThree * diracGammaOne = 0 := by
  ext row column
  fin_cases row <;> fin_cases column <;>
    norm_num [diracGammaOne, diracGammaThree,
      Matrix.mul_apply, Fin.sum_univ_four, Fin.coe_ofNat_eq_mod,
      Matrix.cons_val, Nat.reduceMod]

@[simp] theorem diracGammaTwoThree_anticommute :
    diracGammaTwo * diracGammaThree +
        diracGammaThree * diracGammaTwo = 0 := by
  ext row column
  fin_cases row <;> fin_cases column <;>
    norm_num [diracGammaTwo, diracGammaThree,
      Matrix.mul_apply, Fin.sum_univ_four, Fin.coe_ofNat_eq_mod,
      Matrix.cons_val, Nat.reduceMod]

@[simp] theorem diracGammaOneZero_anticommute :
    diracGammaOne * diracGammaZero +
        diracGammaZero * diracGammaOne = 0 := by
  simpa [add_comm] using diracGammaZeroOne_anticommute

@[simp] theorem diracGammaTwoZero_anticommute :
    diracGammaTwo * diracGammaZero +
        diracGammaZero * diracGammaTwo = 0 := by
  simpa [add_comm] using diracGammaZeroTwo_anticommute

@[simp] theorem diracGammaThreeZero_anticommute :
    diracGammaThree * diracGammaZero +
        diracGammaZero * diracGammaThree = 0 := by
  simpa [add_comm] using diracGammaZeroThree_anticommute

@[simp] theorem diracGammaThreeTwo_anticommute :
    diracGammaThree * diracGammaTwo +
        diracGammaTwo * diracGammaThree = 0 := by
  simpa [add_comm] using diracGammaTwoThree_anticommute

theorem diracGamma_clifford
    (first second : LorentzianIndex) :
    diracGamma first * diracGamma second +
        diracGamma second * diracGamma first =
      (2 * complexMinkowskiEntry first second) • (1 : DiracMatrix) := by
  fin_cases first <;> fin_cases second <;>
    simp [diracGamma, complexMinkowskiEntry,
      minkowskiInternalMetric, add_comm, two_smul]

/-! ## Frame-time evolution principal -/

/-- The three spatial Dirac evolution matrices are Hermitian in the concrete
`(-,+,+,+)` Clifford representation. -/
theorem diracGammaZero_mul_spatial_isHermitian
    (direction : Fin 3) :
    Matrix.IsHermitian
      (diracGammaZero * diracGamma direction.succ) := by
  apply Matrix.IsHermitian.ext
  intro row column
  fin_cases direction <;> fin_cases row <;> fin_cases column <;>
    norm_num [diracGamma, diracGammaZero, diracGammaOne,
      diracGammaTwo, diracGammaThree, Matrix.mul_apply,
      Fin.sum_univ_four, Fin.coe_ofNat_eq_mod, Matrix.cons_val,
      Nat.reduceMod]

/-- Internal-frame principal matrix of the Dirac kinetic operator. -/
def diracFramePrincipal (internal : LorentzianIndex) : DiracMatrix :=
  Complex.I • diracGamma internal

/-- Principal matrix after multiplying the frame equation by its temporal
principal. -/
def diracFrameEvolutionPrincipal
    (internal : LorentzianIndex) : DiracMatrix :=
  diracFramePrincipal 0 * diracFramePrincipal internal

/-- The transformed frame-time coefficient is the positive identity. -/
theorem diracFrameEvolutionPrincipal_time_eq_one :
    diracFrameEvolutionPrincipal 0 = 1 := by
  unfold diracFrameEvolutionPrincipal diracFramePrincipal
  rw [smul_mul_smul, Complex.I_mul_I]
  change (-1 : ℂ) • (diracGammaZero * diracGammaZero) = 1
  rw [diracGammaZero_sq]
  simp

/-- Every transformed frame-spatial coefficient is Hermitian. -/
theorem diracFrameEvolutionPrincipal_spatial_isHermitian
    (direction : Fin 3) :
    Matrix.IsHermitian
      (diracFrameEvolutionPrincipal direction.succ) := by
  rw [diracFrameEvolutionPrincipal, diracFramePrincipal,
    diracFramePrincipal, smul_mul_smul, Complex.I_mul_I]
  simpa [diracGamma] using
    (diracGammaZero_mul_spatial_isHermitian direction).neg

def loweredDiracGamma (internal : LorentzianIndex) : DiracMatrix :=
  (minkowskiInternalSign internal : ℂ) • diracGamma internal

theorem loweredDiracGamma_eq_metric_sum
    (internal : LorentzianIndex) :
    loweredDiracGamma internal =
      ∑ upper,
        complexMinkowskiEntry internal upper • diracGamma upper := by
  fin_cases internal <;>
    simp [loweredDiracGamma, complexMinkowskiEntry,
      minkowskiInternalMetric, minkowskiInternalSign,
      Fin.sum_univ_four]

def diracGammaFive : DiracMatrix :=
  Matrix.diagonal ![-1, -1, 1, 1]

theorem diracGammaFive_eq_gamma_product :
    diracGammaFive =
      Complex.I •
        (((diracGamma 0 * diracGamma 1) * diracGamma 2) *
          diracGamma 3) := by
  ext row column
  fin_cases row <;> fin_cases column <;>
    norm_num [diracGammaFive, diracGamma, diracGammaZero,
      diracGammaOne, diracGammaTwo, diracGammaThree,
      Matrix.mul_apply, Fin.sum_univ_four, Fin.coe_ofNat_eq_mod,
      Matrix.cons_val, Nat.reduceMod]

@[simp] theorem diracGammaFive_sq :
    diracGammaFive * diracGammaFive = (1 : DiracMatrix) := by
  ext row column
  fin_cases row <;> fin_cases column <;>
    norm_num [diracGammaFive, Matrix.diagonal_mul_diagonal,
      Matrix.diagonal_apply,
      Fin.coe_ofNat_eq_mod, Matrix.cons_val, Nat.reduceMod]

theorem diracGammaFive_anticommutes
    (internal : LorentzianIndex) :
    diracGammaFive * diracGamma internal +
        diracGamma internal * diracGammaFive = 0 := by
  fin_cases internal <;>
    ext row column <;>
    simp only [diracGammaFive, Matrix.add_apply,
      Matrix.diagonal_mul, Matrix.mul_diagonal] <;>
    fin_cases row <;> fin_cases column <;>
    norm_num [diracGamma, diracGammaZero, diracGammaOne,
      diracGammaTwo, diracGammaThree, Matrix.diagonal_apply,
      Fin.coe_ofNat_eq_mod, Matrix.cons_val, Nat.reduceMod]

def leftChiralityProjector : DiracMatrix :=
  (2 : ℂ)⁻¹ • ((1 : DiracMatrix) - diracGammaFive)

def rightChiralityProjector : DiracMatrix :=
  (2 : ℂ)⁻¹ • ((1 : DiracMatrix) + diracGammaFive)

@[simp] theorem leftChiralityProjector_sq :
    leftChiralityProjector * leftChiralityProjector =
      leftChiralityProjector := by
  have hsquare :
      ((1 : DiracMatrix) - diracGammaFive) *
          ((1 : DiracMatrix) - diracGammaFive) =
        (2 : ℂ) • ((1 : DiracMatrix) - diracGammaFive) := by
    simp only [sub_mul, mul_sub, one_mul, mul_one]
    rw [diracGammaFive_sq]
    module
  rw [leftChiralityProjector]
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    hsquare]
  module

@[simp] theorem rightChiralityProjector_sq :
    rightChiralityProjector * rightChiralityProjector =
      rightChiralityProjector := by
  have hsquare :
      ((1 : DiracMatrix) + diracGammaFive) *
          ((1 : DiracMatrix) + diracGammaFive) =
        (2 : ℂ) • ((1 : DiracMatrix) + diracGammaFive) := by
    simp only [add_mul, mul_add, one_mul, mul_one]
    rw [diracGammaFive_sq]
    module
  rw [rightChiralityProjector]
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    hsquare]
  module

theorem leftChiralityProjector_add_right :
    leftChiralityProjector + rightChiralityProjector =
      (1 : DiracMatrix) := by
  rw [leftChiralityProjector, rightChiralityProjector]
  norm_num
  module

@[simp] theorem leftChiralityProjector_mul_right :
    leftChiralityProjector * rightChiralityProjector = 0 := by
  have hzero :
      ((1 : DiracMatrix) - diracGammaFive) *
          ((1 : DiracMatrix) + diracGammaFive) = 0 := by
    simp only [sub_mul, mul_add, one_mul, mul_one]
    rw [diracGammaFive_sq]
    module
  rw [leftChiralityProjector, rightChiralityProjector]
  simp only [Matrix.smul_mul, Matrix.mul_smul,
    hzero, smul_zero]

theorem diracSpinorCarrier_finrank :
    Module.finrank ℂ DiracSpinorCarrier = 4 := by
  rw [Module.finrank_pi]
  norm_num

end
end SaturationMonoid.PhysicsCore.DiracCliffordRepresentation
