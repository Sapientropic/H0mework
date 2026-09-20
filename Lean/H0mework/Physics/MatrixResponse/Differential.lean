import H0mework.Physics.MatrixResponse.Value

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.GaugeSpectrum.MatrixResponse

open Matrix Helicity Stage9C.Material.SpinPair
open scoped Matrix

noncomputable section

def perturbation (r : ℝ) (N : Coefficients) (t : ℝ) : Coefficients := r • 1 + t • N

theorem entry_derivative (r : ℝ) (N : Coefficients) (i j : Fin 3) :
    HasDerivAt (fun t => perturbation r N t i j) (N i j) 0 := by
  simpa [perturbation] using
    HasDerivAt.const_add (r * (1 : Coefficients) i j) ((hasDerivAt_id (0 : ℝ)).mul_const (N i j))

theorem det_derivative (r : ℝ) (N : Coefficients) :
    HasDerivAt (fun t => (perturbation r N t).det) (r^2 * N.trace) 0 := by
  have h := entry_derivative r N
  convert! (((((h 0 0).mul (h 1 1)).mul (h 2 2)).sub
    (((h 0 0).mul (h 1 2)).mul (h 2 1))).sub
    (((h 0 1).mul (h 1 0)).mul (h 2 2))).add
    (((h 0 1).mul (h 1 2)).mul (h 2 0)) |>.add
    (((h 0 2).mul (h 1 0)).mul (h 2 1)) |>.sub
    (((h 0 2).mul (h 1 1)).mul (h 2 0)) using 1
  · funext t
    exact Matrix.det_fin_three _
  · simp [perturbation, Matrix.trace, Fin.sum_univ_three]
    ring

theorem square_derivative (r : ℝ) (N : Coefficients) :
    HasDerivAt (fun t => ∑ i : Fin 3, ∑ j : Fin 3, perturbation r N t i j ^ 2)
      (2 * r * N.trace) 0 := by
  convert! HasDerivAt.fun_sum (u := Finset.univ) (fun i _ =>
    HasDerivAt.fun_sum (u := Finset.univ) (fun j _ => (entry_derivative r N i j).pow 2)) using 1
  simp [perturbation, Matrix.trace, Fin.sum_univ_three]
  ring

theorem value_derivative (r : ℝ) (N : Coefficients) :
    HasDerivAt (fun t => (value (perturbation r N t)).re) (5 * r^4 * N.trace) 0 := by
  simp_rw [value_formula, Complex.ofReal_re]
  convert! (det_derivative r N).mul (square_derivative r N) using 1
  simp [perturbation, Matrix.trace, Fin.sum_univ_three]
  ring


end
end SaturationMonoid.PhysicsCore.Stage10.GaugeSpectrum.MatrixResponse
