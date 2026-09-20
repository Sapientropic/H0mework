import H0mework.Physics.Helicity.Current
import H0mework.Physics.Helicity.Action

/-! This operator reads the same physical quantity as the mother gauge
trace Q, through the actual Yang--Mills/current equality. It is distinct
from the independent-dual response of the ordered B·DB matter action. -/

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.GaugeSpectrum.Helicity

open Matrix DiracCliffordRepresentation DiracExteriorMatterAction
open StageNineHolonomicField ProofFreeRicherAnholonomicSource
open StageNineP286GaugeAuxiliaryVariation StageNineP286GaugeConnectionVariation
open SU7MotherLieAlgebra SU7MotherGaugeTheory
open Stage9C.Material.SpinPair Stage9DEF Stage9DEF.Compatibility
open scoped Kronecker

noncomputable section

def currentScale : ℝ := -4 * sourceCoupling * lapse ^ 2 * spinScale

def physicalObservable (point : BasePoint) : State.Observable :=
  (currentScale : ℂ) • ∑ axis : Fin 3, physicalCurrent axis.succ (magnetic point axis)

theorem physicalObservable_value (point : BasePoint) :
    State.evaluation point (physicalObservable point) = value point := by
  rw [physicalObservable, map_smul, map_sum, value_from_actual_current]
  simp_rw [physicalCurrent_readout, current_spatial_pairing,
    currentRead, actual_spinPairCurrent_spatial]
  simp only [currentScale, Complex.ofReal_mul, Complex.ofReal_neg, Complex.ofReal_pow,
    Complex.ofReal_ofNat, Complex.ofReal_sum, smul_eq_mul]
  rw [Finset.mul_sum]
  simp only [Fin.sum_univ_three]
  ring

theorem physicalObservable_hermitian (point : BasePoint) : (physicalObservable point).IsHermitian := by
  change star (physicalObservable point) = _
  simp only [physicalObservable, star_smul, star_sum, Matrix.star_eq_conjTranspose]
  simp [(physicalCurrent_isHermitian _ _).eq]

def spatialSpinMatrix (axis : Fin 3) : Matrix DiracSpinorIndex DiracSpinorIndex ℂ :=
  fun row column => diracGamma axis.succ (spinFlip row) column

theorem currentObservable_generator_normal (axis generator : Fin 3) :
    currentObservable axis.succ (sourceColorP286Generator generator) =
      (-1 / 2 : ℂ) • (spatialSpinMatrix axis ⊗ₖ pauli generator) := by
  apply Matrix.ext
  intro row column
  rcases row with ⟨spin, color⟩
  rcases column with ⟨other, input⟩
  simp only [currentObservable, responseMatrix, compression, LinearMap.toMatrix'_apply,
    currentAction, LinearMap.comp_apply, LinearMap.smul_apply, coordinates, embed,
    LinearMap.coe_mk, AddHom.coe_mk, map_smul, sourceColorDoubletDual_matrixMotherAction,
    sourceColorP286Generator_topLeft, sourceColorP286Generator_hypercharge_zero]
  fin_cases input <;>
    simp [Pi.single_apply, Prod.mk.injEq, spatialSpinMatrix, Compatibility.flip, pauli,
      Matrix.kroneckerMap_apply] <;> ring

theorem spatialSpinMatrix_hermitian (axis : Fin 3) : (spatialSpinMatrix axis).IsHermitian := by
  ext row column
  fin_cases axis <;> fin_cases row <;> fin_cases column <;>
    simp [spatialSpinMatrix, spinFlip, diracGamma, diracGammaOne, diracGammaTwo, diracGammaThree,
      Matrix.conjTranspose_apply]

theorem currentObservable_generator_hermitian (axis generator : Fin 3) :
    (currentObservable axis.succ (sourceColorP286Generator generator)).IsHermitian := by
  rw [currentObservable_generator_normal]
  change _ᴴ = _
  simp [Matrix.conjTranspose_smul, Matrix.conjTranspose_kronecker,
    (spatialSpinMatrix_hermitian axis).eq, (pauli_hermitian generator).eq]

theorem physicalCurrent_generator (axis generator : Fin 3) :
    physicalCurrent axis.succ (sourceColorP286Generator generator) =
      currentObservable axis.succ (sourceColorP286Generator generator) := by
  simp only [physicalCurrent, hermitianPart, Matrix.star_eq_conjTranspose,
    (currentObservable_generator_hermitian axis generator).eq]
  module

theorem currentAction_smul (direction : LorentzianIndex) (scalar : ℝ) (data : P286LieBlockData) :
    currentAction direction (scalar • data) = (scalar : ℂ) • currentAction direction data := by
  simp only [currentAction, p286LieBlockEmbed_real_smul, diracExteriorMotherLieAction_real_smul,
    LinearMap.comp_smul, smul_smul]
  congr 1
  ring

theorem currentObservable_smul (direction : LorentzianIndex) (scalar : ℝ) (data : P286LieBlockData) :
    currentObservable direction (scalar • data) = (scalar : ℂ) • currentObservable direction data := by
  ext row column
  simp only [currentObservable, currentAction_smul, responseMatrix, compression_smul]
  rfl

theorem physicalCurrent_smul (direction : LorentzianIndex) (scalar : ℝ) (data : P286LieBlockData) :
    physicalCurrent direction (scalar • data) = (scalar : ℂ) • physicalCurrent direction data := by
  ext row column
  simp [physicalCurrent, hermitianPart, currentObservable_smul, star_smul,
    Matrix.smul_apply, Complex.real_smul]
  ring

theorem currentObservable_generator_eigenvector (point : BasePoint) (axis : Fin 3) :
    currentObservable axis.succ (sourceColorP286Generator axis) *ᵥ Source.vector point =
      (1 / 2 : ℂ) • Source.vector point := by
  rw [currentObservable_generator_normal, pauli_explicit]
  ext ⟨spin, color⟩
  fin_cases axis <;> fin_cases spin <;> fin_cases color <;>
    simp [spatialSpinMatrix, spinFlip, diracGamma, diracGammaOne, diracGammaTwo, diracGammaThree,
      Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Fin.sum_univ_four, Fin.sum_univ_two,
      Source.vector, Source.amplitude, spinPairCoefficients] <;> ring_nf

theorem physicalObservable_eigenvector (point : BasePoint) :
    physicalObservable point *ᵥ Source.vector point = value point • Source.vector point := by
  unfold physicalObservable
  simp_rw [magnetic_eq, physicalCurrent_smul, physicalCurrent_generator]
  simp only [Fin.sum_univ_three, Matrix.smul_mulVec, Matrix.add_mulVec,
    currentObservable_generator_eigenvector, smul_smul]
  rw [← add_smul, ← add_smul, smul_smul, value_eq]
  congr 1
  simp [currentScale]
  have balance : (gaugeScale : ℂ) ^ 3 = 2 * sourceCoupling * lapse ^ 2 * spinScale := by
    exact_mod_cast gauge_cubic_balance
  linear_combination -(3 : ℂ) * (gaugeScale : ℂ) ^ 2 * balance

end
end SaturationMonoid.PhysicsCore.Stage10.GaugeSpectrum.Helicity
