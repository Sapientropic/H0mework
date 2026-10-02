import H0mework.Versions.R2.Physics.MatrixResponse.Source
import H0mework.Versions.R2.Physics.MatrixResponse.Differential
import H0mework.Versions.R2.Physics.Helicity.Acceptance

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.GaugeSpectrum.MatrixResponse

open Matrix Stage9C.Material.SpinPair StageNineHolonomicField
open SU7MotherLieAlgebra Helicity

noncomputable section

theorem tangent_trace_kernel (N : Coefficients) :
    deriv (fun t => (value (perturbation gaugeScale N t)).re) 0 = 0 ↔ N.trace = 0 := by
  rw [(value_derivative gaugeScale N).deriv]
  simp [mul_eq_zero, ne_of_gt gaugeScale_pos]

theorem scalar_tangent_nonzero :
    deriv (fun t => (value (perturbation gaugeScale 1 t)).re) 0 ≠ 0 := by
  rw [ne_eq, tangent_trace_kernel]
  norm_num

structure SourceMatrixHelicityClosure : Prop extends SourceHelicityClosure where
  same_source : configuration (gaugeScale • (1 : Coefficients)) = Runtime.configuration
  actual_curvature : ∀ M point axis,
    (p286LieBlockEmbed (holonomicGaugeCurvature (configuration M) point (magneticPair axis)) :
      MotherMatrix) = magnetic M axis
  source_quantity : ∀ point,
    value (gaugeScale • (1 : Coefficients)) = Helicity.value point
  full_value : ∀ M, value M = (M.det * ∑ i : Fin 3, ∑ j : Fin 3, M i j ^ 2 : ℝ)
  full_tangent : ∀ N,
    HasDerivAt (fun t => (value (perturbation gaugeScale N t)).re) (5*gaugeScale^4*N.trace) 0
  exact_kernel : ∀ N,
    deriv (fun t => (value (perturbation gaugeScale N t)).re) 0 = 0 ↔ N.trace = 0
  scalar_nonzero : deriv (fun t => (value (perturbation gaugeScale 1 t)).re) 0 ≠ 0

theorem sourceMatrixHelicityClosure : SourceMatrixHelicityClosure where
  toSourceHelicityClosure := sourceHelicityClosure
  same_source := configuration_source
  actual_curvature := curvature_magnetic
  source_quantity := actual_source_value
  full_value := value_formula
  full_tangent := value_derivative gaugeScale
  exact_kernel := tangent_trace_kernel
  scalar_nonzero := scalar_tangent_nonzero

end
end SaturationMonoid.PhysicsCore.Stage10.GaugeSpectrum.MatrixResponse
