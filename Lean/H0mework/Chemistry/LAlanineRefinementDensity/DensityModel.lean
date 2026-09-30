import H0mework.Chemistry.LAlanineRefinementDensity.GaussianBounds

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.SourceGaussianModel

open Finset
open scoped BigOperators

variable {Basis : Type*} [Fintype Basis]

noncomputable section

def bilinear (orbitals : Basis → List Term) (matrix : Basis → Basis → ℚ)
    (left right : MultiIndex) (x : Point) : ℝ :=
  ∑ i, ∑ j, (matrix i j : ℝ) * orbital (orbitals i) left x * orbital (orbitals j) right x

def firstBilinear (orbitals : Basis → List Term) (matrix : Basis → Basis → ℚ)
    (left right : MultiIndex) (axis : Fin 3) (x : Point) : ℝ :=
  bilinear orbitals matrix (raise left axis) right x + bilinear orbitals matrix left (raise right axis) x

def secondBilinear (orbitals : Basis → List Term) (matrix : Basis → Basis → ℚ)
    (left right : MultiIndex) (axis : Fin 3) (x : Point) : ℝ :=
  bilinear orbitals matrix (raise (raise left axis) axis) right x +
    2 * bilinear orbitals matrix (raise left axis) (raise right axis) x +
      bilinear orbitals matrix left (raise (raise right axis) axis) x

theorem bilinear_coordinate_derivative (orbitals : Basis → List Term) (matrix : Basis → Basis → ℚ)
    (left right : MultiIndex) (x : Point) (axis : Fin 3) :
    HasDerivAt (fun t => bilinear orbitals matrix left right (Function.update x axis t))
      (firstBilinear orbitals matrix left right axis x) (x axis) := by
  have terms (i j : Basis) :=
    ((orbital_coordinate_derivative (orbitals i) left x axis).const_mul (matrix i j : ℝ)).mul
      (orbital_coordinate_derivative (orbitals j) right x axis)
  have all := HasDerivAt.fun_sum (u := Finset.univ) (fun i _ =>
    HasDerivAt.fun_sum (u := Finset.univ) (fun j _ => terms i j))
  convert! all using 1
  all_goals simp only [firstBilinear, bilinear, Finset.sum_add_distrib, Function.update_eq_self]

theorem firstBilinear_coordinate_derivative (orbitals : Basis → List Term) (matrix : Basis → Basis → ℚ)
    (left right : MultiIndex) (x : Point) (axis : Fin 3) :
    HasDerivAt (fun t => firstBilinear orbitals matrix left right axis (Function.update x axis t))
      (secondBilinear orbitals matrix left right axis x) (x axis) := by
  have first := bilinear_coordinate_derivative orbitals matrix (raise left axis) right x axis
  have second := bilinear_coordinate_derivative orbitals matrix left (raise right axis) x axis
  convert! first.add second using 1
  simp only [firstBilinear, secondBilinear]
  ring

theorem bilinear_contDiff (orbitals : Basis → List Term) (matrix : Basis → Basis → ℚ)
    (left right : MultiIndex) (order : WithTop ℕ∞) :
    ContDiff ℝ order (bilinear orbitals matrix left right) := by
  exact ContDiff.sum (fun i _ => ContDiff.sum (fun j _ =>
    (contDiff_const.mul (orbital_contDiff (orbitals i) left order)).mul
      (orbital_contDiff (orbitals j) right order)))

def thirdBilinear (orbitals : Basis → List Term) (matrix : Basis → Basis → ℚ)
    (left right : MultiIndex) (firstAxis secondAxis : Fin 3) (x : Point) : ℝ :=
  firstBilinear orbitals matrix (raise (raise left firstAxis) firstAxis) right secondAxis x +
    2 * firstBilinear orbitals matrix (raise left firstAxis) (raise right firstAxis) secondAxis x +
      firstBilinear orbitals matrix left (raise (raise right firstAxis) firstAxis) secondAxis x

def fourthBilinear (orbitals : Basis → List Term) (matrix : Basis → Basis → ℚ)
    (left right : MultiIndex) (firstAxis secondAxis : Fin 3) (x : Point) : ℝ :=
  secondBilinear orbitals matrix (raise (raise left firstAxis) firstAxis) right secondAxis x +
    2 * secondBilinear orbitals matrix (raise left firstAxis) (raise right firstAxis) secondAxis x +
      secondBilinear orbitals matrix left (raise (raise right firstAxis) firstAxis) secondAxis x

theorem secondBilinear_coordinate_derivative (orbitals : Basis → List Term) (matrix : Basis → Basis → ℚ)
    (left right : MultiIndex) (x : Point) (firstAxis secondAxis : Fin 3) :
    HasDerivAt (fun t => secondBilinear orbitals matrix left right firstAxis (Function.update x secondAxis t))
      (thirdBilinear orbitals matrix left right firstAxis secondAxis x) (x secondAxis) := by
  exact ((bilinear_coordinate_derivative orbitals matrix (raise (raise left firstAxis) firstAxis) right x secondAxis).add
    ((bilinear_coordinate_derivative orbitals matrix (raise left firstAxis) (raise right firstAxis) x secondAxis).const_mul 2)).add
      (bilinear_coordinate_derivative orbitals matrix left (raise (raise right firstAxis) firstAxis) x secondAxis)

theorem thirdBilinear_coordinate_derivative (orbitals : Basis → List Term) (matrix : Basis → Basis → ℚ)
    (left right : MultiIndex) (x : Point) (firstAxis secondAxis : Fin 3) :
    HasDerivAt (fun t => thirdBilinear orbitals matrix left right firstAxis secondAxis (Function.update x secondAxis t))
      (fourthBilinear orbitals matrix left right firstAxis secondAxis x) (x secondAxis) := by
  exact ((firstBilinear_coordinate_derivative orbitals matrix (raise (raise left firstAxis) firstAxis) right x secondAxis).add
    ((firstBilinear_coordinate_derivative orbitals matrix (raise left firstAxis) (raise right firstAxis) x secondAxis).const_mul 2)).add
      (firstBilinear_coordinate_derivative orbitals matrix left (raise (raise right firstAxis) firstAxis) x secondAxis)

def density (orbitals : Basis → List Term) (matrix : Basis → Basis → ℚ) : Point → ℝ :=
  bilinear orbitals matrix (fun _ => 0) (fun _ => 0)

def laplacian (orbitals : Basis → List Term) (matrix : Basis → Basis → ℚ) (x : Point) : ℝ :=
  ∑ axis : Fin 3, secondBilinear orbitals matrix (fun _ => 0) (fun _ => 0) axis x

def laplacianFirst (orbitals : Basis → List Term) (matrix : Basis → Basis → ℚ)
    (axis : Fin 3) (x : Point) : ℝ :=
  ∑ innerAxis : Fin 3, thirdBilinear orbitals matrix (fun _ => 0) (fun _ => 0) innerAxis axis x

def laplacianSecond (orbitals : Basis → List Term) (matrix : Basis → Basis → ℚ)
    (axis : Fin 3) (x : Point) : ℝ :=
  ∑ innerAxis : Fin 3, fourthBilinear orbitals matrix (fun _ => 0) (fun _ => 0) innerAxis axis x

theorem laplacian_coordinate_derivative (orbitals : Basis → List Term) (matrix : Basis → Basis → ℚ)
    (x : Point) (axis : Fin 3) :
    HasDerivAt (fun t => laplacian orbitals matrix (Function.update x axis t))
      (laplacianFirst orbitals matrix axis x) (x axis) :=
  HasDerivAt.fun_sum (u := Finset.univ) (fun innerAxis _ =>
    secondBilinear_coordinate_derivative orbitals matrix (fun _ => 0) (fun _ => 0) x innerAxis axis)

theorem laplacianFirst_coordinate_derivative (orbitals : Basis → List Term) (matrix : Basis → Basis → ℚ)
    (x : Point) (axis : Fin 3) :
    HasDerivAt (fun t => laplacianFirst orbitals matrix axis (Function.update x axis t))
      (laplacianSecond orbitals matrix axis x) (x axis) :=
  HasDerivAt.fun_sum (u := Finset.univ) (fun innerAxis _ =>
    thirdBilinear_coordinate_derivative orbitals matrix (fun _ => 0) (fun _ => 0) x innerAxis axis)

theorem secondBilinear_contDiff (orbitals : Basis → List Term) (matrix : Basis → Basis → ℚ)
    (left right : MultiIndex) (axis : Fin 3) (order : WithTop ℕ∞) :
    ContDiff ℝ order (secondBilinear orbitals matrix left right axis) :=
  ((bilinear_contDiff orbitals matrix _ _ order).add
    (contDiff_const.mul (bilinear_contDiff orbitals matrix _ _ order))).add
      (bilinear_contDiff orbitals matrix _ _ order)

theorem laplacian_contDiff (orbitals : Basis → List Term) (matrix : Basis → Basis → ℚ)
    (order : WithTop ℕ∞) : ContDiff ℝ order (laplacian orbitals matrix) :=
  ContDiff.sum (s := Finset.univ) (fun axis _ =>
    secondBilinear_contDiff orbitals matrix (fun _ => 0) (fun _ => 0) axis order)

end
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.SourceGaussianModel
