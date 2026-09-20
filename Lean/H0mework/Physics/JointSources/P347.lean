import H0mework.Arithmetic.PrimeProjection.P346

/-!
# Proposition 347: the fundamental fixed-vector color-singlet is too small

P345 introduced a concrete representation action and used the most literal
predicate

`ColorSingletBlockField v := ∀ c : SU(3), c • v = v`.

This file proves the important calibration theorem: for the fundamental
`SU(3)` action on a color vector, the only fixed color vector is zero.  Since a
prime-edge color field has prime values in its color coordinates, no such field
is a fundamental fixed-vector singlet.

Consequently, the naive fixed-vector predicate is not the final physics object
needed for the Goldbach route.  A real Standard-Model/QCD producer must replace
it with the appropriate tensor / closed-loop / contraction singlet predicate.
That is not a failure of P345; it is precisely the boundary P345 made
checkable.
-/

noncomputable section

set_option linter.unusedSectionVars false

namespace SaturationMonoid
namespace StandardModelConstraint

open GaugeProjection
open Matrix
open SaturationMonoid.AffineRelaxation

/-! ## Two determinant-one color flips -/

/-- The `SU(3)` diagonal matrix `diag(-1,-1,1)`. -/
def colorFlip01Raw : Matrix (Fin 3) (Fin 3) ℂ :=
  Matrix.diagonal
    (fun i : Fin 3 =>
      if i = (0 : Fin 3) then (-1 : ℂ)
      else if i = (1 : Fin 3) then (-1 : ℂ)
      else (1 : ℂ))

/-- THEOREM 1: `diag(-1,-1,1)` lies in `SU(3)`. -/
theorem colorFlip01Raw_mem_specialUnitary :
    colorFlip01Raw ∈ Matrix.specialUnitaryGroup (Fin 3) ℂ := by
  rw [Matrix.mem_specialUnitaryGroup_iff]
  constructor
  · rw [Matrix.mem_unitaryGroup_iff, star_eq_conjTranspose]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [colorFlip01Raw, Matrix.mul_apply, Fin.sum_univ_three]
  · rw [colorFlip01Raw, Matrix.det_diagonal]
    rw [show (Finset.univ : Finset (Fin 3)) = {0, 1, 2} by
      ext x
      fin_cases x <;> simp]
    simp

/-- The `SU(3)` element `diag(-1,-1,1)`. -/
def colorFlip01 : SU3Gauge :=
  ⟨colorFlip01Raw, colorFlip01Raw_mem_specialUnitary⟩

/-- The `SU(3)` diagonal matrix `diag(-1,1,-1)`. -/
def colorFlip02Raw : Matrix (Fin 3) (Fin 3) ℂ :=
  Matrix.diagonal
    (fun i : Fin 3 =>
      if i = (0 : Fin 3) then (-1 : ℂ)
      else if i = (2 : Fin 3) then (-1 : ℂ)
      else (1 : ℂ))

/-- THEOREM 2: `diag(-1,1,-1)` lies in `SU(3)`. -/
theorem colorFlip02Raw_mem_specialUnitary :
    colorFlip02Raw ∈ Matrix.specialUnitaryGroup (Fin 3) ℂ := by
  rw [Matrix.mem_specialUnitaryGroup_iff]
  constructor
  · rw [Matrix.mem_unitaryGroup_iff, star_eq_conjTranspose]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [colorFlip02Raw, Matrix.mul_apply, Fin.sum_univ_three]
  · rw [colorFlip02Raw, Matrix.det_diagonal]
    rw [show (Finset.univ : Finset (Fin 3)) = {0, 1, 2} by
      ext x
      fin_cases x <;> simp]
    simp

/-- The `SU(3)` element `diag(-1,1,-1)`. -/
def colorFlip02 : SU3Gauge :=
  ⟨colorFlip02Raw, colorFlip02Raw_mem_specialUnitary⟩

/-- A small complex-number helper: a value equal to its own negative is zero. -/
theorem complex_eq_zero_of_neg_eq_self {z : ℂ} (h : -z = z) :
    z = 0 := by
  have h2 : (2 : ℂ) * z = 0 := by
    calc
      (2 : ℂ) * z = z - (-z) := by ring
      _ = 0 := by rw [h]; ring
  exact (mul_eq_zero.mp h2).resolve_left (by norm_num)

/-! ## Fundamental fixed vectors vanish on the color block -/

/-- THEOREM 3: under the fundamental color action, a fixed block field has zero
on each color coordinate. -/
theorem colorSingletBlockField_color_zero
    (v : SMBlockField) (h : ColorSingletBlockField v)
    (i : Fin 3) :
    v (SMBlockFacet.color i) = 0 := by
  fin_cases i
  · have hfix := congrFun (h colorFlip01) (SMBlockFacet.color 0)
    rw [smGaugeBlockAction_colorInclusion_color] at hfix
    simp [colorFlip01, colorFlip01Raw, Matrix.mulVec, dotProduct,
      Fin.sum_univ_three] at hfix
    exact complex_eq_zero_of_neg_eq_self hfix
  · have hfix := congrFun (h colorFlip01) (SMBlockFacet.color 1)
    rw [smGaugeBlockAction_colorInclusion_color] at hfix
    simp [colorFlip01, colorFlip01Raw, Matrix.mulVec, dotProduct,
      Fin.sum_univ_three] at hfix
    exact complex_eq_zero_of_neg_eq_self hfix
  · have hfix := congrFun (h colorFlip02) (SMBlockFacet.color 2)
    rw [smGaugeBlockAction_colorInclusion_color] at hfix
    simp [colorFlip02, colorFlip02Raw, Matrix.mulVec, dotProduct,
      Fin.sum_univ_three] at hfix
    exact complex_eq_zero_of_neg_eq_self hfix

/-- THEOREM 4: no prime-edge color field is a fundamental fixed-vector
color-singlet.  The first color coordinate is the prime `p`, hence nonzero. -/
theorem not_primeEdgeColorSinglet_fundamental
    (n : ℕ) (p q : PrimeExponent) :
    ¬ PrimeEdgeColorSinglet n p q := by
  intro hsinglet
  have hzero :=
    colorSingletBlockField_color_zero (primeEdgeColorField n p q) hsinglet 0
  simp [primeEdgeColorField] at hzero
  have hp_ne_nat : (p : ℕ) ≠ 0 := Nat.Prime.ne_zero p.2
  have hp_ne_complex : ((p : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast hp_ne_nat
  have hzero' : ((p : ℕ) : ℂ) = 0 := by
    simpa using hzero
  exact hp_ne_complex hzero'

/-- THEOREM 5: the current fixed-vector color-singlet sector has no allowed
prime-edge cycles at all. -/
theorem not_colorSingletSector_allowed
    (n : ℕ) (p q : PrimeExponent) :
    ¬ colorSingletPrimeEdgeSector.allowed n p q :=
  not_primeEdgeColorSinglet_fundamental n p q

/-- THEOREM 6: with the literal fixed-vector predicate, confinement-style
exclusion is automatically true because the allowed sector is empty. -/
theorem fixedVectorColorConfinementExcludesPrimeEdgeObstructions :
    ColorConfinementExcludesPrimeEdgeObstructions := by
  rintro ⟨n, p, q, hn, hallowed, hobs⟩
  exact not_colorSingletSector_allowed n p q hallowed

/-- THEOREM 7: therefore any proof of the P345 color-singlet classifier for
this literal fixed-vector predicate already has Goldbach strength.  This is
the precise reason the real physics producer must use a richer tensor/loop
singlet predicate rather than the fundamental fixed-vector predicate. -/
theorem fixedVectorColorSingletLaw_implies_evenGoldbach
    (L : ColorSingletGoldbachObstructionLaw) :
    EvenGoldbachStatement :=
  colorConfinement_plus_classifier_implies_evenGoldbach
    L fixedVectorColorConfinementExcludesPrimeEdgeObstructions

/-- A compact certificate for the fundamental-singlet calibration. -/
structure P347FundamentalColorSingletBoundaryCertificate : Prop where
  color_fixed_vectors_vanish :
    ∀ (v : SMBlockField), ColorSingletBlockField v ->
      ∀ i : Fin 3, v (SMBlockFacet.color i) = 0
  no_prime_edge_fixed_vector_singlet :
    ∀ (n : ℕ) (p q : PrimeExponent),
      ¬ PrimeEdgeColorSinglet n p q
  fixed_vector_sector_empty :
    ∀ (n : ℕ) (p q : PrimeExponent),
      ¬ colorSingletPrimeEdgeSector.allowed n p q
  fixed_vector_confinement :
    ColorConfinementExcludesPrimeEdgeObstructions
  fixed_vector_law_implies_goldbach :
    ColorSingletGoldbachObstructionLaw -> EvenGoldbachStatement

/-- THEOREM 8: the naive fundamental fixed-vector singlet boundary is fully
machine-checked. -/
theorem p347FundamentalColorSingletBoundaryCertificate :
    P347FundamentalColorSingletBoundaryCertificate where
  color_fixed_vectors_vanish := colorSingletBlockField_color_zero
  no_prime_edge_fixed_vector_singlet :=
    not_primeEdgeColorSinglet_fundamental
  fixed_vector_sector_empty := not_colorSingletSector_allowed
  fixed_vector_confinement :=
    fixedVectorColorConfinementExcludesPrimeEdgeObstructions
  fixed_vector_law_implies_goldbach :=
    fixedVectorColorSingletLaw_implies_evenGoldbach

end StandardModelConstraint
end SaturationMonoid
