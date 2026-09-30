import H0mework.Versions.X.Arithmetic.EulerGlobal.CoordinateGerm

/-!
# Installed complex points of the generated determinant germ

The generated determinant germ already owns its complex realization interface.
This file installs the Mathlib coordinate and takes its ordinary zero fibre.
A Mathlib zeta zero therefore gives one point by the zero-fibre constructor;
there is no extension of an evaluator on the arithmetic zero-fibre ring.

The point construction is terminal and fixedness-free.  Reversal and
fixedness are consumed only after this point is inserted into the already
settled universal family.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace CanonicalUnitArithmeticFactorizationGlobalDeterminantCoordinateSpecialization

open CanonicalUnitArithmeticFactorizationEulerDependentDiagram
open CanonicalUnitArithmeticFactorizationGlobalDeterminantCoordinateRealization

noncomputable section

/-- The installed frame of the already generated global determinant germ.
Its realization law is part of `ComplexRealization`; the installed function
is not accepted from a coordinate-point caller. -/
structure InstalledComplexDeterminantAt : Type where
  private mk ::
  occurrence_projects : globalGermOccurrence.map Prod.fst = seedOccurrence
  realization : ComplexRealization

def installedComplexDeterminant : InstalledComplexDeterminantAt :=
  ⟨globalGermOccurrence_projects, mathlibRealization⟩

/-- The complex coordinate of the same generated determinant occurrence. -/
noncomputable def coordinateDeterminant : ℂ → ℂ :=
  installedComplexDeterminant.realization.function

/-- Installed-coordinate identification.  This is definitional: no
injective module extension and no identity-theorem argument is used. -/
@[simp] theorem determinantCoordinate_eq_zeta (coordinate : ℂ) :
    coordinateDeterminant coordinate = riemannZeta coordinate :=
  rfl

/-- The installed coordinate still reads the generated determinant germ on
the native Dirichlet half-plane.  This records provenance; it is not used to
construct a zero-fibre point. -/
theorem coordinateDeterminant_reads_generated_germ
    {coordinate : ℂ} (native : 1 < coordinate.re) :
    coordinateDeterminant coordinate =
      globalDeterminantCoordinateGerm coordinate :=
  installedComplexDeterminant.realization.agreesWithGeneratedGerm native

/-! ## Universal coordinate zero fibre -/

/-- Coordinate functions form the installed frame ring.  The generated
determinant is one distinguished section of this ring. -/
abbrev CoordinateFunctionRing := ℂ → ℂ

def coordinateDeterminantSection : CoordinateFunctionRing :=
  coordinateDeterminant

def coordinateZeroIdeal : Ideal CoordinateFunctionRing :=
  Ideal.span {coordinateDeterminantSection}

/-- Coordinate ring of the installed zero fibre of the generated global
determinant section. -/
abbrev CoordinateZeroFiberRing :=
  CoordinateFunctionRing ⧸ coordinateZeroIdeal

def coordinateFunction : CoordinateFunctionRing := fun coordinate => coordinate

/-- Universal coordinate on the installed zero fibre. -/
def universalCoordinate : CoordinateZeroFiberRing :=
  Ideal.Quotient.mk coordinateZeroIdeal coordinateFunction

/-- Point type of the installed complex zero fibre of the same generated
determinant occurrence. -/
abbrev Point : Type :=
  {coordinate : ℂ // coordinateDeterminant coordinate = 0}

def Point.coordinate (point : Point) : ℂ := point.1

@[simp] theorem Point.coordinate_mk (coordinate : ℂ)
    (zeroLaw : coordinateDeterminant coordinate = 0) :
    Point.coordinate ⟨coordinate, zeroLaw⟩ = coordinate :=
  rfl

theorem Point.coordinateZeroIdeal_le_ker_evaluation (point : Point) :
    coordinateZeroIdeal ≤
      RingHom.ker (Pi.evalRingHom (fun _ : ℂ => ℂ) point.coordinate) := by
  rw [coordinateZeroIdeal, Ideal.span_le]
  intro function membership
  simp only [Set.mem_singleton_iff] at membership
  subst function
  change coordinateDeterminant point.coordinate = 0
  exact point.2

/-- The quotient universal property, not an extension theorem, generates the
classical specialization belonging to one zero-fibre point. -/
def Point.specialization (point : Point) : CoordinateZeroFiberRing →+* ℂ :=
  Ideal.Quotient.lift coordinateZeroIdeal
    (Pi.evalRingHom (fun _ : ℂ => ℂ) point.coordinate)
    point.coordinateZeroIdeal_le_ker_evaluation

@[simp] theorem Point.specialization_mk (point : Point)
    (function : CoordinateFunctionRing) :
    point.specialization (Ideal.Quotient.mk coordinateZeroIdeal function) =
      function point.coordinate :=
  rfl

@[simp] theorem Point.specialization_universalCoordinate (point : Point) :
    point.specialization universalCoordinate = point.coordinate :=
  rfl

/-- A Mathlib zeta zero specializes directly to one point of the installed
zero fibre.  No global evaluator, endpoint law, fixedness, or critical-line
equation is supplied. -/
def pointOfMathlibZero (coordinate : ℂ)
    (zetaZero : riemannZeta coordinate = 0) : Point :=
  ⟨coordinate, by
    simpa only [determinantCoordinate_eq_zeta] using zetaZero⟩

@[simp] theorem pointOfMathlibZero_coordinate (coordinate : ℂ)
    (zetaZero : riemannZeta coordinate = 0) :
    (pointOfMathlibZero coordinate zetaZero).coordinate = coordinate :=
  rfl

/-- The component quantified by Mathlib's Riemann hypothesis.  The raw
zero fibre also contains the known trivial zeros, so universal arithmetic
fixedness may only be specialized through this restricted component. -/
structure NontrivialPoint : Type where
  point : Point
  nontrivial : ¬∃ n : Nat, point.coordinate = -2 * (n + 1)
  notPole : point.coordinate ≠ 1

def nontrivialPointOfMathlibZero (coordinate : ℂ)
    (zetaZero : riemannZeta coordinate = 0)
    (nontrivial : ¬∃ n : Nat, coordinate = -2 * (n + 1))
    (notPole : coordinate ≠ 1) : NontrivialPoint :=
  ⟨pointOfMathlibZero coordinate zetaZero, nontrivial, notPole⟩

@[simp] theorem nontrivialPointOfMathlibZero_coordinate
    (coordinate : ℂ) (zetaZero : riemannZeta coordinate = 0)
    (nontrivial : ¬∃ n : Nat, coordinate = -2 * (n + 1))
    (notPole : coordinate ≠ 1) :
    (nontrivialPointOfMathlibZero coordinate zetaZero nontrivial notPole).point.coordinate =
      coordinate :=
  rfl

theorem preserves_same_occurrence_coordinate_and_zero_fibre
    (coordinate : ℂ) (zetaZero : riemannZeta coordinate = 0) :
    installedComplexDeterminant.occurrence_projects =
        globalGermOccurrence_projects ∧
      coordinateDeterminant coordinate = riemannZeta coordinate ∧
      (pointOfMathlibZero coordinate zetaZero).coordinate = coordinate ∧
      (pointOfMathlibZero coordinate zetaZero).specialization
          universalCoordinate = coordinate :=
  ⟨rfl, determinantCoordinate_eq_zeta coordinate, rfl, rfl⟩

end
end CanonicalUnitArithmeticFactorizationGlobalDeterminantCoordinateSpecialization
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
