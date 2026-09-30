import H0mework.Chemistry.LAlanineRefinementDensity.GaussianPrimitive

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.SourceGaussianModel

open Polynomial Finset
open SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.GaussianPrimitive

abbrev Point := Fin 3 → ℝ
abbrev MultiIndex := Fin 3 → ℕ

structure Term where
  weight : ℚ
  exponent : ℚ
  centre : Fin 3 → ℚ
  powers : Fin 3 → ℕ

noncomputable section

def jetPoly (alpha : ℚ) (power order : ℕ) : Polynomial ℚ :=
  ((jetPolynomial alpha)^[order]) (X ^ power)

def factor (alpha : ℚ) (power order : ℕ) (x : ℝ) : ℝ :=
  gaussian (alpha : ℝ) ((jetPoly alpha power order).map (algebraMap ℚ ℝ)) x

def value (term : Term) (d : MultiIndex) (x : Point) : ℝ :=
  (term.weight : ℝ) *
    factor term.exponent (term.powers 0) (d 0) (x 0 - term.centre 0) *
    factor term.exponent (term.powers 1) (d 1) (x 1 - term.centre 1) *
    factor term.exponent (term.powers 2) (d 2) (x 2 - term.centre 2)

def raise (d : MultiIndex) (axis : Fin 3) : MultiIndex :=
  Function.update d axis (d axis + 1)

theorem factor_hasDerivAt (alpha : ℚ) (power order : ℕ) (x : ℝ) :
    HasDerivAt (factor alpha power order) (factor alpha power (order + 1) x) x := by
  convert! gaussian_hasDerivAt ((jetPoly alpha power order).map (algebraMap ℚ ℝ)) (alpha : ℝ) x using 1
  simp only [factor, jetPoly, Function.iterate_succ_apply', ← jetPolynomial_ratCast]

theorem factor_contDiff (alpha : ℚ) (power order : ℕ) (smoothness : WithTop ℕ∞) :
    ContDiff ℝ smoothness (factor alpha power order) :=
  gaussian_contDiff _ _ smoothness

theorem value_coordinate_derivative (term : Term) (d : MultiIndex) (x : Point) (axis : Fin 3) :
    HasDerivAt (fun t => value term d (Function.update x axis t))
      (value term (raise d axis) x) (x axis) := by
  have factorShift (i : Fin 3) :
      HasDerivAt (fun t => factor term.exponent (term.powers i) (d i) (t - term.centre i))
        (factor term.exponent (term.powers i) (d i + 1) (x i - term.centre i)) (x i) := by
    simpa only [mul_one, Function.comp_def, id_eq] using
      (factor_hasDerivAt term.exponent (term.powers i) (d i) (x i - term.centre i)).comp
        (x i) ((hasDerivAt_id (x i)).sub_const (term.centre i : ℝ))
  fin_cases axis
  · simpa [value, raise, Function.update] using
      (((factorShift 0).const_mul (term.weight : ℝ)).mul_const
        (factor term.exponent (term.powers 1) (d 1) (x 1 - term.centre 1))).mul_const
          (factor term.exponent (term.powers 2) (d 2) (x 2 - term.centre 2))
  · simpa [value, raise, Function.update] using
      ((factorShift 1).const_mul ((term.weight : ℝ) *
        factor term.exponent (term.powers 0) (d 0) (x 0 - term.centre 0))).mul_const
          (factor term.exponent (term.powers 2) (d 2) (x 2 - term.centre 2))
  · simpa [value, raise, Function.update] using
      (factorShift 2).const_mul ((term.weight : ℝ) *
        factor term.exponent (term.powers 0) (d 0) (x 0 - term.centre 0) *
        factor term.exponent (term.powers 1) (d 1) (x 1 - term.centre 1))

def orbital (terms : List Term) (d : MultiIndex) (x : Point) : ℝ :=
  (terms.map fun term => value term d x).sum

theorem orbital_coordinate_derivative (terms : List Term) (d : MultiIndex) (x : Point) (axis : Fin 3) :
    HasDerivAt (fun t => orbital terms d (Function.update x axis t))
      (orbital terms (raise d axis) x) (x axis) := by
  induction terms with
  | nil => simpa [orbital] using hasDerivAt_const (x axis) (0 : ℝ)
  | cons term rest ih =>
    convert! (value_coordinate_derivative term d x axis).add ih using 1

theorem value_contDiff (term : Term) (d : MultiIndex) (order : WithTop ℕ∞) :
    ContDiff ℝ order (value term d) := by
  have smooth (axis : Fin 3) :
      ContDiff ℝ order (fun x : Point => factor term.exponent (term.powers axis) (d axis)
        (x axis - (term.centre axis : ℝ))) :=
    (factor_contDiff _ _ _ order).comp ((by fun_prop :
      ContDiff ℝ order (fun x : Point => x axis)).sub contDiff_const)
  exact ((contDiff_const.mul (smooth 0)).mul (smooth 1)).mul (smooth 2)

theorem orbital_contDiff (terms : List Term) (d : MultiIndex) (order : WithTop ℕ∞) :
    ContDiff ℝ order (orbital terms d) := by
  induction terms with
  | nil => convert! (contDiff_const : ContDiff ℝ order (fun _ : Point => (0 : ℝ))) using 1
  | cons term rest ih =>
    convert! (value_contDiff term d order).add ih using 1

end
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.SourceGaussianModel
