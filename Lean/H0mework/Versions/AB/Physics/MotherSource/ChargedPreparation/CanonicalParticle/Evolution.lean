import H0mework.Versions.AB.Physics.MotherSource.ChargedPreparation.CanonicalParticle.Pair
import H0mework.Versions.AB.Physics.LowEnergy.FullQuantum.Evolution

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 300000
namespace SaturationMonoid.PhysicsCore.Stage10.ChargedPreparation.CanonicalParticle
open ProofFreeRicherAnholonomicSource StageNineHolonomicField DiracExteriorMatterAction
open Stage9C.Material.SpinPair Stage9DEF Stage9DEF.Compatibility YangMills.FullPairing
open LowEnergy.FullQuantum ChargedPreparation.SpatialSpectrum
open scoped Matrix InnerProductSpace
noncomputable section
local instance : NormedAlgebra ℚ (Hilbert →L[ℂ] Hilbert) := NormedAlgebra.restrictScalars ℚ ℂ _
local instance : NormedAlgebra ℝ (Hilbert →L[ℂ] Hilbert) := NormedAlgebra.restrictScalars ℝ ℂ _

private theorem exponential_eigen (action : Hilbert →L[ℂ] Hilbert) (value : ℂ) (state : Hilbert)
    (eigen : action state = value • state) : NormedSpace.exp action state = Complex.exp value • state := by
  have powers (n : ℕ) : (action^n) state = value^n • state := by
    induction n with
    | zero => simp
    | succ n step =>
      rw [pow_succ', mul_apply_eq_comp, step, map_smul, eigen, smul_smul, pow_succ]
  let evaluate := ContinuousLinearMap.apply ℂ Hilbert state
  have series := evaluate.hasSum (NormedSpace.exp_series_hasSum_exp' action (𝕂 := ℂ))
  have scalar := (NormedSpace.exp_series_hasSum_exp' value (𝕂 := ℂ)).smul_const state
  apply series.unique
  convert scalar using 1
  · rfl
  · funext n
    simp only [evaluate, ContinuousLinearMap.apply_apply, smul_apply,
      powers, smul_smul, smul_eq_mul]
  · rw [Complex.exp_eq_exp_ℂ]


def state (point : BasePoint) (momentum : Fin 3 → ℝ) : Hilbert :=
  naturalCoordinates (normalizedPreparation momentum (embed (Source.vector point)))

theorem state_unit (point : BasePoint) (momentum : Fin 3 → ℝ) : inner ℂ (state point momentum) (state point momentum) = 1 := by
  simpa only [state, YangMills.FullPairing.prepared, operator_coordinates] using full_prepared_gram point momentum

theorem drift_eigen (point : BasePoint) (momentum : Fin 3 → ℝ) :
    operator (drift Stage10.Runtime.configuration point momentum) (state point momentum) =
      (-Complex.I*(energy momentum : ℂ)) • state point momentum := by
  rw [state, operator_coordinates, ← hamiltonian_drift]
  simp only [LinearMap.smul_apply, normalized_full_hamiltonian, map_smul, smul_smul]

theorem original_evolution (point : BasePoint) (momentum : Fin 3 → ℝ) (time : ℝ) :
    evolution Stage10.Runtime.configuration point momentum time (state point momentum) =
      Complex.exp (-Complex.I*(time : ℂ)*(energy momentum : ℂ)) • state point momentum := by
  apply exponential_eigen
  change (time : ℂ) • operator (drift Stage10.Runtime.configuration point momentum) (state point momentum) = _
  rw [drift_eigen, smul_smul]
  congr 1
  ring

/-- The central rest phase is displayed, so the source physical energy is retained. -/
def relativeEvolution (point : BasePoint) (momentum : Fin 3 → ℝ) (time : ℝ) : Hilbert :=
  Complex.exp (Complex.I*(time : ℂ)*(energy 0 : ℂ)) •
    evolution Stage10.Runtime.configuration point momentum time (state point momentum)

theorem original_relative_evolution (point : BasePoint) (momentum : Fin 3 → ℝ) (time : ℝ) :
    relativeEvolution point momentum time =
      Complex.exp (-Complex.I*(time : ℂ)*(SpatialSpectrum.excitation momentum : ℂ)) • state point momentum := by
  rw [relativeEvolution, original_evolution, smul_smul, ← Complex.exp_add, ← source_excitation]
  congr 2
  push_cast
  ring

theorem original_phase_kinetic_remainder (point : BasePoint) (momentum : Fin 3 → ℝ) (time : ℝ) :
    relativeEvolution point momentum time =
      Complex.exp (-Complex.I*(time : ℂ)*
        ((spatialSquare momentum/(2*Dispersion.inertia) -
          lapse^4*(spatialSquare momentum)^2/(2*frequency*(rate momentum+frequency)^2) : ℝ) : ℂ)) • state point momentum := by
  rw [original_relative_evolution, SpatialSpectrum.excitation_quadratic_remainder]

theorem original_rest_phase (point : BasePoint) :
    evolution Stage10.Runtime.configuration point 0 (Real.pi/frequency) (state point 0) = -state point 0 := by
  rw [original_evolution, energy_zero]
  have exponent : -Complex.I*((Real.pi/frequency : ℝ) : ℂ)*((-frequency : ℝ) : ℂ) =
      (Real.pi : ℂ)*Complex.I := by
    push_cast
    field_simp [Dispersion.frequency_pos.ne']
  rw [exponent, Complex.exp_pi_mul_I, neg_one_smul]

theorem rejects_discarding_rest_phase (point : BasePoint) :
    evolution Stage10.Runtime.configuration point 0 (Real.pi/frequency) (state point 0) ≠ state point 0 := by
  rw [original_rest_phase]
  intro same
  have paired := congrArg (fun value => inner ℂ (state point 0) value) same
  rw [inner_neg_right, state_unit] at paired
  norm_num at paired

end
end SaturationMonoid.PhysicsCore.Stage10.ChargedPreparation.CanonicalParticle
