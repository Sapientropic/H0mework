import H0mework.Versions.R2.Physics.Helicity.CurrentOperator

/-! The current operator for the same gauge trace Q is stationary in the
accepted phase flow, and the accepted singlet has definite Q. Its connected
kernel is zero. This does not identify it with the distinct B·DB dual response. -/

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.GaugeSpectrum.Helicity

open Matrix DiracCliffordRepresentation MeasureTheory
open StageNineHolonomicField ProofFreeRicherAnholonomicSource
open Stage9C.Material.SpinPair Stage9DEF Stage9DEF.Compatibility

noncomputable section

theorem currentGenerator_commutes_clock (axis generator : Fin 3) (displacement : BasePoint) :
    currentObservable axis.succ (sourceColorP286Generator generator) *
        (Dynamics.unitary displacement : State.Observable) =
      (Dynamics.unitary displacement : State.Observable) *
        currentObservable axis.succ (sourceColorP286Generator generator) := by
  rw [currentObservable_generator_normal]
  ext ⟨spin, color⟩ ⟨other, input⟩
  fin_cases axis <;> fin_cases spin <;> fin_cases other <;>
    simp [Dynamics.unitary_matrix, Matrix.mul_diagonal, Matrix.diagonal_mul,
      spatialSpinMatrix, spinFlip, diracGamma, diracGammaOne, diracGammaTwo, diracGammaThree,
      Dynamics.phaseCoefficient, Dynamics.rate] <;> ring

theorem physicalObservable_commutes_clock (point displacement : BasePoint) :
    physicalObservable point * (Dynamics.unitary displacement : State.Observable) =
      (Dynamics.unitary displacement : State.Observable) * physicalObservable point := by
  unfold physicalObservable
  simp_rw [magnetic_eq, physicalCurrent_smul, physicalCurrent_generator]
  simp only [Fin.sum_univ_three, Matrix.smul_mul, Matrix.mul_smul, Matrix.add_mul, Matrix.mul_add,
    currentGenerator_commutes_clock]

def evolvedPhysical (point displacement : BasePoint) : State.Observable :=
  star (Dynamics.unitary displacement : State.Observable) * physicalObservable point *
    (Dynamics.unitary displacement : State.Observable)

theorem evolvedPhysical_stationary (point displacement : BasePoint) :
    evolvedPhysical point displacement = physicalObservable point := by
  rw [evolvedPhysical, Matrix.mul_assoc, physicalObservable_commutes_clock, ← Matrix.mul_assoc,
    Matrix.mem_unitaryGroup_iff'.mp (Dynamics.unitary displacement).property, Matrix.one_mul]

theorem physicalObservable_secondMoment (point : BasePoint) :
    State.evaluation point (physicalObservable point * physicalObservable point) = (value point) ^ 2 := by
  change star (Source.vector point) ⬝ᵥ
    ((physicalObservable point * physicalObservable point) *ᵥ Source.vector point) = _
  rw [← Matrix.mulVec_mulVec, physicalObservable_eigenvector, Matrix.mulVec_smul,
    physicalObservable_eigenvector, dotProduct_smul, dotProduct_smul]
  have normalized : star (Source.vector point) ⬝ᵥ Source.vector point = 1 := Source.vector_inner_self point
  rw [normalized]
  ring

theorem physical_connected_zero (point first second : BasePoint) :
    connected point (evolvedPhysical point first) (evolvedPhysical point second) = 0 := by
  rw [evolvedPhysical_stationary, evolvedPhysical_stationary]
  simp only [connected, Matrix.star_eq_conjTranspose, (physicalObservable_hermitian point).eq,
    physicalObservable_secondMoment, physicalObservable_value]
  simp [value_eq, pow_two]

theorem physical_connected_spectralIntegral (point first second : BasePoint) :
    connected point (evolvedPhysical point first) (evolvedPhysical point second) =
      ∫ rate : ℝ, phase rate (second - first) ∂(0 : Measure ℝ) := by
  rw [physical_connected_zero, integral_zero_measure]

theorem physical_twoPoint (point first second : BasePoint) :
    State.evaluation point (star (evolvedPhysical point first) * evolvedPhysical point second) =
      (value point) ^ 2 := by
  rw [evolvedPhysical_stationary, evolvedPhysical_stationary, Matrix.star_eq_conjTranspose,
    (physicalObservable_hermitian point).eq, physicalObservable_secondMoment]

theorem ordered_initial_mean : State.evaluation 0 (observable 0) = (amplitude : ℂ) := by
  rw [observable_normalForm, map_smul]
  simp [State.evaluation, State.vectorEvaluation, Matrix.mulVec, dotProduct,
    Fintype.sum_prod_type, Fin.sum_univ_four, Fin.sum_univ_two, exchange, spinFlip,
    Source.vector, Source.amplitude, spinPairCoefficients, upperPhase, lowerPhase, phase_zero]
  ring

theorem ordered_response_ne_physical : observable 0 ≠ physicalObservable 0 := by
  intro same
  have mean := congrArg (State.evaluation 0) same
  rw [ordered_initial_mean, physicalObservable_value] at mean
  have half := amplitude_from_fullTrace 0
  apply value_nonzero 0
  linear_combination 2 * half - 2 * mean

end
end SaturationMonoid.PhysicsCore.Stage10.GaugeSpectrum.Helicity
