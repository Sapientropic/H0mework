import H0mework.Chemistry.LAlanineSignedEvaluator.Contraction

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.SourceRectangleChecks

open SourceGaussianModel SourceSignedEvaluator

/-- The source term's multiplication order, with already-calculated group leaves shared. -/
def cachedTerm (weight : ℚ) (exponentialCache : Pair) (polynomialCache : Fin 3 → Pair) : Pair :=
  mul (mul (mul (mul (point weight) exponentialCache) (polynomialCache 0)) (polynomialCache 1))
    (polynomialCache 2)

theorem relative_same_group (term representative : Term) (box : Rectangle)
    (centre : term.centre = representative.centre) (axis : Fin 3) :
    relative term box axis = relative representative box axis := by
  simp only [relative, centre]

theorem radial_same_group (term representative : Term) (box : Rectangle)
    (centre : term.centre = representative.centre) (exponent : term.exponent = representative.exponent) :
    radialPair term box = radialPair representative box := by
  simp only [radialPair, relative_same_group term representative box centre, exponent]

theorem cachedTerm_commutes (term : Term) (d : MultiIndex) (box : Rectangle) (kl kh : ℕ)
    (exponentialCache : Pair) (polynomialCache : Fin 3 → Pair)
    (expComputed : exponentialCache = exponential (radialPair term box) kl kh)
    (polyComputed : ∀ axis, polynomialCache axis =
      jetHorner term.exponent (term.powers axis) (d axis) (relative term box axis)) :
    cachedTerm term.weight exponentialCache polynomialCache = termPair term d box kl kh := by
  simp only [cachedTerm, termPair, expComputed, polyComputed]

theorem cachedTerm_contains (term : Term) (d : MultiIndex) (box : Rectangle) (kl kh : ℕ)
    (exponentialCache : Pair) (polynomialCache : Fin 3 → Pair)
    (expComputed : exponentialCache = exponential (radialPair term box) kl kh)
    (polyComputed : ∀ axis, polynomialCache axis =
      jetHorner term.exponent (term.powers axis) (d axis) (relative term box axis))
    (reduction : TermReductionValid term box kl kh) (x : Point) (inside : InRectangle box x) :
    Holds (cachedTerm term.weight exponentialCache polynomialCache) (value term d x) := by
  rw [cachedTerm_commutes term d box kl kh exponentialCache polynomialCache expComputed polyComputed]
  exact termPair_contains term d box kl kh reduction x inside

end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.SourceRectangleChecks
