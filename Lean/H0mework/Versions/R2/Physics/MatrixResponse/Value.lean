import H0mework.Versions.R2.Physics.MatrixResponse.Basis

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.GaugeSpectrum.MatrixResponse

open Matrix Helicity
open scoped Matrix

noncomputable section

def connection (M : Coefficients) (axis : Fin 3) : MotherMatrix := mother (M axis)

def magnetic (M : Coefficients) : Fin 3 → MotherMatrix :=
  ![bracket (connection M 1) (connection M 2),
    bracket (connection M 2) (connection M 0),
    bracket (connection M 0) (connection M 1)]

def value (M : Coefficients) : ℂ := homogeneousHelicity (connection M) (magnetic M)

def cofactors (M : Coefficients) : Coefficients :=
  ![M 1 ⨯₃ M 2, M 2 ⨯₃ M 0, M 0 ⨯₃ M 1]

def curlCoefficients (M : Coefficients) : Coefficients :=
  ![M 1 ⨯₃ cofactors M 2 - M 2 ⨯₃ cofactors M 1,
    M 2 ⨯₃ cofactors M 0 - M 0 ⨯₃ cofactors M 2,
    M 0 ⨯₃ cofactors M 1 - M 1 ⨯₃ cofactors M 0]

theorem magnetic_coefficients (M : Coefficients) (axis : Fin 3) :
    magnetic M axis = mother (-(cofactors M axis)) := by
  fin_cases axis <;> simp [magnetic, connection, mother_bracket, cofactors]

theorem curl_coefficients (M : Coefficients) (axis : Fin 3) :
    bracketCurl (connection M) (magnetic M) axis = mother (curlCoefficients M axis) := by
  unfold bracketCurl
  simp_rw [magnetic_coefficients, connection, mother_bracket]
  fin_cases axis <;> simp [curlCoefficients, mother_sub]

theorem value_coordinates (M : Coefficients) :
    value M = ((∑ axis : Fin 3, cofactors M axis ⬝ᵥ curlCoefficients M axis) / 2 : ℝ) := by
  unfold value homogeneousHelicity
  simp_rw [magnetic_coefficients, curl_coefficients, mother_trace_pair]
  simp [neg_dotProduct, Fin.sum_univ_three]
  ring

theorem value_formula (M : Coefficients) :
    value M = (M.det * ∑ i : Fin 3, ∑ j : Fin 3, M i j ^ 2 : ℝ) := by
  rw [value_coordinates]
  congr 1
  simp [cofactors, curlCoefficients, cross_apply, dotProduct, Fin.sum_univ_three, det_fin_three]
  ring

theorem value_scalar (r : ℝ) : value (r • (1 : Coefficients)) = (3 * r ^ 5 : ℝ) := by
  rw [value_formula]
  congr 1
  simp [Fin.sum_univ_three]
  ring

end
end SaturationMonoid.PhysicsCore.Stage10.GaugeSpectrum.MatrixResponse
