import H0mework.Versions.AB.Physics.MotherSource.ChargedPreparation.Dispersion
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

/-! The original negative-charge sector retains every spatial momentum direction. -/
set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 700000
namespace SaturationMonoid.PhysicsCore.Stage10.ChargedPreparation.SpatialSpectrum
open ProofFreeRicherAnholonomicSource DiracExteriorMatterAction DiracCliffordRepresentation
open Stage9C.Material.SpinPair Stage9DEF Stage9DEF.Compatibility
open LowEnergy.FullQuantum YangMills.FullPairing Stage10.ChargedPreparation.Dynamics
open scoped Matrix
noncomputable section

def lowerValues (values : Fin 4 → ℂ) : Source.Index → ℂ :=
  fun i => !![0,0; 0,0; values 0,values 1; values 2,values 3] i.1 i.2

def sourceMatrix (momentum : Fin 3 → ℝ) : Matrix (Fin 4) (Fin 4) ℂ :=
  let z := (lapse : ℂ)*(momentum 2 : ℂ)
  let a := (lapse : ℂ)*((momentum 0 : ℂ)-Complex.I*(momentum 1 : ℂ))
  let b := (lapse : ℂ)*((momentum 0 : ℂ)+Complex.I*(momentum 1 : ℂ))
  let w := (frequency : ℂ)
  !![3*w+z,0,a,0; 0,2*w+z,w,a; b,w,2*w-z,0; 0,b,0,3*w-z]

/-- Full mother-space invariance precedes the four-coordinate Hamiltonian readout. -/
theorem physical_matrix (point : BasePoint) (momentum : Fin 3 → ℝ) (values : Fin 4 → ℂ) :
    hamiltonian Stage10.Runtime.configuration point momentum (embed (lowerValues values)) =
      embed (lowerValues (sourceMatrix momentum *ᵥ values)) := by
  rw [Stage10.Runtime.configuration_eq, physical_hamiltonian_embed, physical_free_embed]
  congr 1
  funext i
  rcases i with ⟨spin,color⟩
  fin_cases spin <;> fin_cases color <;>
    simp [principalValues, spinValues, gaugeValues, lowerValues, sourceMatrix,
      Matrix.mulVec, dotProduct, sourceColorPauli,
      diracGamma, diracGammaZero, diracGammaOne, diracGammaTwo, diracGammaThree,
      diracGammaFive, Matrix.mul_apply, Fin.sum_univ_four, Fin.sum_univ_three,
      Fin.sum_univ_two, frequency, gaugeScale]
  all_goals ring_nf; simp [Complex.I_sq]
  all_goals ring

def spatialSquare (momentum : Fin 3 → ℝ) : ℝ := ∑ axis, (momentum axis)^2

theorem characteristic (momentum : Fin 3 → ℝ) (energy : ℂ) :
    (sourceMatrix momentum - energy • (1 : Matrix (Fin 4) (Fin 4) ℂ)).det =
      ((((3*frequency : ℝ) : ℂ)-energy)^2-(lapse : ℂ)^2*(spatialSquare momentum : ℂ)) *
        ((((2*frequency : ℝ) : ℂ)-energy)^2-(frequency : ℂ)^2-
          (lapse : ℂ)^2*(spatialSquare momentum : ℂ)) := by
  rw [Matrix.det_succ_row_zero]
  simp [Matrix.det_fin_three, Matrix.submatrix_apply, Matrix.sub_apply,
    Matrix.smul_apply, Matrix.one_apply, sourceMatrix, spatialSquare,
    Fin.sum_univ_four, Fin.sum_univ_three, Fin.succAbove]
  ring_nf
  simp [Complex.I_sq]
  ring

def lowerIndex (index : Fin 4) : Source.Index := ![(2,0),(2,1),(3,0),(3,1)] index

theorem lowerValues_read (values : Fin 4 → ℂ) (index : Fin 4) :
    lowerValues values (lowerIndex index) = values index := by fin_cases index <;> rfl

theorem lower_embed_nonzero (values : Fin 4 → ℂ) (nonzero : values ≠ 0) :
    embed (lowerValues values) ≠ 0 := by
  intro zero
  apply nonzero
  funext index
  have read := congrArg (fun matter => coordinates matter (lowerIndex index)) zero
  simpa only [coordinates_embed, lowerValues_read, map_zero, Pi.zero_apply] using read

theorem lowerValues_smul (coefficient : ℂ) (values : Fin 4 → ℂ) :
    lowerValues (coefficient • values) = coefficient • lowerValues values := by
  funext i
  rcases i with ⟨spin,color⟩
  fin_cases spin <;> fin_cases color <;> simp [lowerValues]

def rate (momentum : Fin 3 → ℝ) : ℝ := Real.sqrt (frequency^2+lapse^2*spatialSquare momentum)
def upperEnergy (momentum : Fin 3 → ℝ) : ℝ := 2*frequency+rate momentum

theorem spatialSquare_nonneg (momentum : Fin 3 → ℝ) : 0 ≤ spatialSquare momentum :=
  Finset.sum_nonneg (fun _ _ => sq_nonneg _)

theorem rate_sq (momentum : Fin 3 → ℝ) :
    (rate momentum)^2 = frequency^2+lapse^2*spatialSquare momentum :=
  Real.sq_sqrt (add_nonneg (sq_nonneg _) (mul_nonneg (sq_nonneg _) (spatialSquare_nonneg _)))

theorem upper_determinant_zero (momentum : Fin 3 → ℝ) :
    (sourceMatrix momentum - (upperEnergy momentum : ℂ) • (1 : Matrix (Fin 4) (Fin 4) ℂ)).det = 0 := by
  rw [characteristic]
  have square : (rate momentum : ℂ)^2 =
      (frequency : ℂ)^2+(lapse : ℂ)^2*(spatialSquare momentum : ℂ) := by
    exact_mod_cast rate_sq momentum
  have zero : ((((2*frequency : ℝ) : ℂ)-(upperEnergy momentum : ℂ))^2-(frequency : ℂ)^2-
      (lapse : ℂ)^2*(spatialSquare momentum : ℂ)) = 0 := by
    unfold upperEnergy
    push_cast
    linear_combination square
  rw [zero, mul_zero]

/-- Every three-dimensional momentum has the source-generated upper-band eigenvalue. -/
theorem upper_physical_eigen (point : BasePoint) (momentum : Fin 3 → ℝ) :
    ∃ matter : DiracExteriorMatterCarrier, matter ≠ 0 ∧
      hamiltonian Stage10.Runtime.configuration point momentum matter =
        (upperEnergy momentum : ℂ) • matter := by
  obtain ⟨values, nonzero, equation⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr
    (upper_determinant_zero momentum)
  refine ⟨embed (lowerValues values), lower_embed_nonzero values nonzero, ?_⟩
  rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec] at equation
  rw [physical_matrix, sub_eq_zero.mp equation, lowerValues_smul, map_smul]

theorem lower_values_charge (values : Fin 4 → ℂ) : charge *ᵥ lowerValues values = -lowerValues values := by
  funext i
  rw [charge_mulVec]
  rcases i with ⟨spin,color⟩
  fin_cases spin <;> fin_cases color <;> simp [lowerValues, sign]

theorem upper_zero : upperEnergy 0 = 3*frequency := by
  simp [upperEnergy, rate, spatialSquare, Real.sqrt_sq_eq_abs, abs_of_pos Dispersion.frequency_pos]
  ring

theorem rate_radial (momentum : Fin 3 → ℝ) :
    rate momentum = Dispersion.rate (Real.sqrt (spatialSquare momentum)) := by
  simp only [rate, Dispersion.rate, Real.sq_sqrt (spatialSquare_nonneg momentum)]

def excitation (momentum : Fin 3 → ℝ) : ℝ := upperEnergy momentum-upperEnergy 0

theorem excitation_radial (momentum : Fin 3 → ℝ) :
    excitation momentum = Dispersion.excitation (Real.sqrt (spatialSquare momentum)) := by
  simp only [excitation, upperEnergy, Dispersion.excitation, Dispersion.upperEnergy, rate_radial]
  simp [spatialSquare]

theorem excitation_exact (momentum : Fin 3 → ℝ) :
    excitation momentum = lapse^2*spatialSquare momentum/(rate momentum+frequency) := by
  rw [excitation_radial, Dispersion.excitation_exact, ← rate_radial,
    Real.sq_sqrt (spatialSquare_nonneg momentum)]

/-- Exact all-momentum remainder after the physical-time quadratic kinetic coefficient. -/
theorem excitation_quadratic_remainder (momentum : Fin 3 → ℝ) :
    excitation momentum = spatialSquare momentum/(2*Dispersion.inertia) -
      lapse^4*(spatialSquare momentum)^2/(2*frequency*(rate momentum+frequency)^2) := by
  rw [excitation_radial, Dispersion.excitation_quadratic_remainder, ← rate_radial,
    show (Real.sqrt (spatialSquare momentum))^4 = (spatialSquare momentum)^2 by
      rw [show (4 : ℕ) = 2*2 from rfl, pow_mul, Real.sq_sqrt (spatialSquare_nonneg momentum)],
    Real.sq_sqrt (spatialSquare_nonneg momentum)]

theorem excitation_bounds (momentum : Fin 3 → ℝ) :
    0 ≤ excitation momentum ∧ excitation momentum ≤ spatialSquare momentum/(2*Dispersion.inertia) := by
  have rateNonneg : 0 ≤ rate momentum := Real.sqrt_nonneg _
  constructor
  · rw [excitation_exact]
    exact div_nonneg (mul_nonneg (sq_nonneg _) (spatialSquare_nonneg _))
      (add_nonneg rateNonneg Dispersion.frequency_pos.le)
  · rw [excitation_quadratic_remainder]
    apply sub_le_self
    exact div_nonneg (mul_nonneg (pow_nonneg lapse_pos.le _) (sq_nonneg _))
      (mul_nonneg (mul_nonneg (by norm_num) Dispersion.frequency_pos.le) (sq_nonneg _))

end
end SaturationMonoid.PhysicsCore.Stage10.ChargedPreparation.SpatialSpectrum
