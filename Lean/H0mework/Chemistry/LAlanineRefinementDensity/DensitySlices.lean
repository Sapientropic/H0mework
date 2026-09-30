import H0mework.Chemistry.LAlanineRefinementDensity.DensityBounds

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.SourceGaussianModel

open scoped BigOperators

variable {Basis : Type*} [Fintype Basis]

noncomputable section

theorem bilinear_slice_second (orbitals : Basis → List Term) (matrix : Basis → Basis → ℚ)
    (left right : MultiIndex) (x : Point) (axis : Fin 3) :
    iteratedDeriv 2 (fun t => bilinear orbitals matrix left right (Function.update x axis t)) (x axis) =
      secondBilinear orbitals matrix left right axis x := by
  have firstAt (time : ℝ) :
      HasDerivAt (fun t => bilinear orbitals matrix left right (Function.update x axis t))
        (firstBilinear orbitals matrix left right axis (Function.update x axis time)) time := by
    simpa only [Function.update_self, Function.update_idem] using
      bilinear_coordinate_derivative orbitals matrix left right (Function.update x axis time) axis
  have firstEq : deriv (fun t => bilinear orbitals matrix left right (Function.update x axis t)) =
      fun time => firstBilinear orbitals matrix left right axis (Function.update x axis time) :=
    funext (fun time => (firstAt time).deriv)
  rw [show (2 : Nat) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one, firstEq]
  exact (firstBilinear_coordinate_derivative orbitals matrix left right x axis).deriv

theorem density_laplacian_exact (orbitals : Basis → List Term) (matrix : Basis → Basis → ℚ) (x : Point) :
    laplacian orbitals matrix x =
      ∑ axis : Fin 3, iteratedDeriv 2 (fun t => density orbitals matrix (Function.update x axis t)) (x axis) := by
  unfold density laplacian
  simp only [bilinear_slice_second]

theorem laplacian_slice_second (orbitals : Basis → List Term) (matrix : Basis → Basis → ℚ)
    (x : Point) (axis : Fin 3) :
    iteratedDeriv 2 (fun t => laplacian orbitals matrix (Function.update x axis t)) (x axis) =
      laplacianSecond orbitals matrix axis x := by
  have firstAt (time : ℝ) :
      HasDerivAt (fun t => laplacian orbitals matrix (Function.update x axis t))
        (laplacianFirst orbitals matrix axis (Function.update x axis time)) time := by
    simpa only [Function.update_self, Function.update_idem] using
      laplacian_coordinate_derivative orbitals matrix (Function.update x axis time) axis
  have firstEq : deriv (fun t => laplacian orbitals matrix (Function.update x axis t)) =
      fun time => laplacianFirst orbitals matrix axis (Function.update x axis time) :=
    funext (fun time => (firstAt time).deriv)
  rw [show (2 : Nat) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one, firstEq]
  exact (laplacianFirst_coordinate_derivative orbitals matrix x axis).deriv

theorem laplacian_slice_second_at (orbitals : Basis → List Term) (matrix : Basis → Basis → ℚ)
    (x : Point) (axis : Fin 3) (time : ℝ) :
    iteratedDeriv 2 (fun t => laplacian orbitals matrix (Function.update x axis t)) time =
      laplacianSecond orbitals matrix axis (Function.update x axis time) := by
  simpa only [Function.update_self, Function.update_idem] using
    laplacian_slice_second orbitals matrix (Function.update x axis time) axis

theorem laplacian_slice_contDiff (orbitals : Basis → List Term) (matrix : Basis → Basis → ℚ)
    (x : Point) (axis : Fin 3) (order : WithTop ℕ∞) :
    ContDiff ℝ order (fun t => laplacian orbitals matrix (Function.update x axis t)) :=
  (laplacian_contDiff orbitals matrix order).comp (contDiff_update order x axis)

end
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.SourceGaussianModel
