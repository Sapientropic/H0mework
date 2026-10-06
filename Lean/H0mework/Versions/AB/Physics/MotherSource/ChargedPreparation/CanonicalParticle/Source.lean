import H0mework.Versions.AB.Physics.MotherSource.CanonicalMatter.Dual
import H0mework.Versions.AB.Physics.MotherSource.ChargedPreparation.SpatialSpectrum

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 700000
namespace SaturationMonoid.PhysicsCore.Stage10.ChargedPreparation.CanonicalParticle
open ProofFreeRicherAnholonomicSource StageNineHolonomicField DiracExteriorMatterAction
open DiracCliffordRepresentation Stage9C.Material.SpinPair Stage9DEF Stage9DEF.Compatibility
open YangMills.FullPairing ChargedPreparation.Dynamics ChargedPreparation.SpatialSpectrum
open scoped Matrix InnerProductSpace
noncomputable section

def upperValues (values : Fin 4 → ℂ) : Source.Index → ℂ :=
  fun index => !![values 0,values 1;values 2,values 3;0,0;0,0] index.1 index.2

theorem physical_upper_matrix (point : BasePoint) (momentum : Fin 3 → ℝ) (values : Fin 4 → ℂ) :
    LowEnergy.FullQuantum.hamiltonian Stage10.Runtime.configuration point momentum (embed (upperValues values)) =
      embed (upperValues (-(sourceMatrix momentum *ᵥ values))) := by
  rw [Stage10.Runtime.configuration_eq, physical_hamiltonian_embed, physical_free_embed]
  congr 1
  funext index
  rcases index with ⟨spin,color⟩
  fin_cases spin <;> fin_cases color <;>
    simp [principalValues, spinValues, gaugeValues, upperValues, sourceMatrix,
      dotProduct, sourceColorPauli, diracGamma, diracGammaZero,
      diracGammaOne, diracGammaTwo, diracGammaThree, diracGammaFive,
      Matrix.mul_apply, Fin.sum_univ_four, Fin.sum_univ_three, Fin.sum_univ_two,
      frequency, gaugeScale]
  all_goals ring_nf; simp only [Complex.I_sq]; ring

def energy (momentum : Fin 3 → ℝ) : ℝ := -2*frequency+rate momentum

def sourceAction (momentum : Fin 3 → ℝ) : Mother :=
  LowEnergy.FullQuantum.hamiltonian Stage10.Runtime.configuration 0 momentum +
    ((2*frequency+rate momentum : ℝ) : ℂ) • (1 : Mother)

def preparation (momentum : Fin 3 → ℝ) : Mother := (sourceAction momentum).comp Positive.preparation

def amplitude (point : BasePoint) : ℂ := (spinScale : ℂ)*upperPhase point/2

def coefficients (momentum : Fin 3 → ℝ) : Fin 4 → ℂ :=
  ![(lapse : ℂ)*((momentum 0 : ℂ)-Complex.I*(momentum 1 : ℂ)),
    (rate momentum : ℂ)+(frequency : ℂ)-(lapse : ℂ)*(momentum 2 : ℂ),
    -(rate momentum : ℂ)-(frequency : ℂ)-(lapse : ℂ)*(momentum 2 : ℂ),
    -(lapse : ℂ)*((momentum 0 : ℂ)+Complex.I*(momentum 1 : ℂ))]

def values (point : BasePoint) (momentum : Fin 3 → ℝ) : Source.Index → ℂ :=
  upperValues (amplitude point • coefficients momentum)

theorem positive_prepared_values (point : BasePoint) :
    Positive.vector point = upperValues ![0,amplitude point,-amplitude point,0] := by
  funext index
  rcases index with ⟨spin,color⟩
  fin_cases spin <;> fin_cases color <;>
    simp [Positive.vector_value, Source.vector, Source.amplitude,
      spinPairCoefficients, amplitude, upperValues]
  all_goals ring

theorem source_preparation (point : BasePoint) (momentum : Fin 3 → ℝ) :
    preparation momentum (embed (Source.vector point)) = embed (values point momentum) := by
  rw [preparation, LinearMap.comp_apply, Positive.preparation_embed, positive_prepared_values]
  simp only [sourceAction, LinearMap.add_apply, LinearMap.smul_apply, Module.End.one_apply,
    physical_upper_matrix]
  rw [← map_smul, ← map_add]
  congr 1
  funext index
  rcases index with ⟨spin,color⟩
  fin_cases spin <;> fin_cases color <;>
    simp [sourceMatrix, values, upperValues, coefficients]
  all_goals ring

theorem source_coefficients_eigen (momentum : Fin 3 → ℝ) :
    sourceMatrix momentum *ᵥ coefficients momentum =
      ((2*frequency-rate momentum : ℝ) : ℂ) • coefficients momentum := by
  have square : (rate momentum : ℂ)^2 =
      (frequency : ℂ)^2+(lapse : ℂ)^2*(∑ index : Fin 3, (momentum index : ℂ)^2) := by
    exact_mod_cast rate_sq momentum
  simp only [Fin.sum_univ_three] at square
  ext index
  fin_cases index <;>
    simp [sourceMatrix, coefficients, Matrix.mulVec, dotProduct, Fin.sum_univ_four]
  all_goals ring_nf <;> simp only [Complex.I_sq] <;> ring_nf
  all_goals first | ring | linear_combination square | linear_combination -square

theorem coefficients_square (momentum : Fin 3 → ℝ) :
    (∑ index : Fin 4, star (coefficients momentum index)*coefficients momentum index) =
      ((4*rate momentum*(rate momentum+frequency) : ℝ) : ℂ) := by
  have square : (rate momentum : ℂ)^2 =
      (frequency : ℂ)^2+(lapse : ℂ)^2*(∑ index : Fin 3, (momentum index : ℂ)^2) := by
    exact_mod_cast rate_sq momentum
  simp only [Fin.sum_univ_three] at square
  simp [coefficients, Fin.sum_univ_four]
  ring_nf
  simp only [Complex.I_sq]
  linear_combination -2*square

def weight (momentum : Fin 3 → ℝ) : ℝ := 2*rate momentum*(rate momentum+frequency)

theorem weight_positive (momentum : Fin 3 → ℝ) : 0 < weight momentum := by
  have ratePositive : 0 < rate momentum := by
    apply Real.sqrt_pos.mpr
    exact add_pos_of_pos_of_nonneg (sq_pos_of_pos Dispersion.frequency_pos)
      (mul_nonneg (sq_nonneg lapse) (spatialSquare_nonneg momentum))
  exact mul_pos (mul_pos (by norm_num) ratePositive) (add_pos ratePositive Dispersion.frequency_pos)

theorem upperValues_smul (scalar : ℂ) (vector : Fin 4 → ℂ) :
    upperValues (scalar • vector) = scalar • upperValues vector := by
  funext index
  rcases index with ⟨spin,color⟩
  fin_cases spin <;> fin_cases color <;> simp [upperValues]

theorem original_full_hamiltonian (point : BasePoint) (momentum : Fin 3 → ℝ) :
    LowEnergy.FullQuantum.hamiltonian Stage10.Runtime.configuration point momentum
      (embed (values point momentum)) =
        (energy momentum : ℂ) • embed (values point momentum) := by
  rw [values, physical_upper_matrix, Matrix.mulVec_smul, source_coefficients_eigen]
  have coefficient : -(amplitude point • (((2*frequency-rate momentum : ℝ) : ℂ) • coefficients momentum)) =
      (energy momentum : ℂ) • (amplitude point • coefficients momentum) := by
    simp only [smul_smul, ← neg_smul, energy]
    push_cast
    congr 1
    ring
  rw [coefficient, upperValues_smul, map_smul]

theorem energy_zero : energy 0 = -frequency := by
  simp [energy, rate, spatialSquare, Real.sqrt_sq_eq_abs, abs_of_pos Dispersion.frequency_pos]
  ring

theorem source_excitation (momentum : Fin 3 → ℝ) :
    energy momentum-energy 0 = SpatialSpectrum.excitation momentum := by
  rw [energy, energy_zero, SpatialSpectrum.excitation, upperEnergy, SpatialSpectrum.upper_zero]
  ring

end
end SaturationMonoid.PhysicsCore.Stage10.ChargedPreparation.CanonicalParticle
