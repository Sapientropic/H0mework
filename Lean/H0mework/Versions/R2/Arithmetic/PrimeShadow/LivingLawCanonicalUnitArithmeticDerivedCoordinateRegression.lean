import Mathlib.NumberTheory.LSeries.RiemannZeta
import H0mework.Versions.R2.Arithmetic.PrimeShadow.LivingLawCanonicalUnitArithmeticCofinalRelationHomotopyLimit
import H0mework.Versions.R2.Arithmetic.UnitArithmetic.CoordinateProjectionObstruction

/-!
# Derived classical coordinate regression

The full two-term reversal complex admits a classical coordinate map without
assuming fixedness.  Its target differential is multiplication by the actual
coordinate boundary `s - (1 - conj s)`.  This is precisely why the boundary
must remain in the common derived occurrence instead of being quotiented out
before the final coordinate restriction.

The remaining regression obligation is now exact: a Mathlib nontrivial zeta
zero must land in the zero-locus of this generated coordinate boundary.  No
such landing is accepted by the arithmetic producer in this file.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace CanonicalUnitArithmeticDerivedCoordinateRegression

open CanonicalUnitArithmeticCofinalRelationHomotopyLimit
open CanonicalUnitArithmeticCofinalReversalRelation
open CanonicalUnitArithmeticCoordinateProjectionObstruction
open CategoryTheory
open CochainMappingCoconeFunctoriality
open SequentialHomotopyLimit
open scoped ComplexConjugate

noncomputable section

def coordinateDifference (coordinate : ℂ) : ℂ :=
  coordinate - coordinateReversal coordinate

def stageCoefficient (stage : Nat)
    (primeIndex : Fin (StageRank stage)) (dualIndex : Fin 2) :
    StageRelationLattice stage →ₗ[ℤ] ℤ :=
  LinearMap.proj (primeIndex, dualIndex)

def pairSignEvaluation (stage : Nat)
    (primeIndex : Fin (StageRank stage)) :
    StageRelationLattice stage →ₗ[ℤ] ℤ :=
  stageCoefficient stage primeIndex 0 -
    stageCoefficient stage primeIndex 1

def pairCoordinateEvaluation (stage : Nat)
    (primeIndex : Fin (StageRank stage)) (coordinate : ℂ) :
    StageRelationLattice stage →ₗ[ℤ] ℂ :=
  (LinearMap.toSpanSingleton ℤ ℂ coordinate).comp
      (stageCoefficient stage primeIndex 0) +
    (LinearMap.toSpanSingleton ℤ ℂ (coordinateReversal coordinate)).comp
      (stageCoefficient stage primeIndex 1)

def coordinateDifferenceBoundary (coordinate : ℂ) : ℤ →ₗ[ℤ] ℂ :=
  LinearMap.toSpanSingleton ℤ ℂ (coordinateDifference coordinate)

/-- The arithmetic reversal boundary and the coordinate-difference boundary
form an actual square for every complex coordinate.  No zero or fixed-point
law is needed to construct it. -/
theorem pairCoordinate_boundary_square
    (stage : Nat) (primeIndex : Fin (StageRank stage))
    (coordinate : ℂ) :
    (coordinateDifferenceBoundary coordinate).comp
        (pairSignEvaluation stage primeIndex) =
      (pairCoordinateEvaluation stage primeIndex coordinate).comp
        (stageBoundary stage) := by
  apply LinearMap.ext
  intro value
  change
    (value (primeIndex, 0) - value (primeIndex, 1)) •
          coordinateDifference coordinate =
      (stageBoundary stage value (primeIndex, 0)) • coordinate +
        (stageBoundary stage value (primeIndex, 1)) •
          coordinateReversal coordinate
  rw [show stageBoundary stage =
      LinearMap.id - stageReversal stage by
    unfold stageBoundary
    rw [weightedStageReversal_eq_reversal]]
  simp only [LinearMap.sub_apply, LinearMap.id_apply]
  change
    (value (primeIndex, 0) - value (primeIndex, 1)) •
          (coordinate - coordinateReversal coordinate) =
      (value (primeIndex, 0) - value (primeIndex, 1)) • coordinate +
        (value (primeIndex, 1) - value (primeIndex, 0)) •
          coordinateReversal coordinate
  module

abbrev CoordinateSourceModule : ModuleCat.{0} ℤ :=
  ModuleCat.of ℤ ℤ

abbrev CoordinateTargetModule : ModuleCat.{0} ℤ :=
  ModuleCat.of ℤ ℂ

noncomputable abbrev coordinateSourceComplex : IntegralCochainComplex :=
  (CochainComplex.singleFunctor (ModuleCat ℤ) 0).obj
    CoordinateSourceModule

noncomputable abbrev coordinateTargetComplex : IntegralCochainComplex :=
  (CochainComplex.singleFunctor (ModuleCat ℤ) 0).obj
    CoordinateTargetModule

noncomputable def coordinateBoundaryMap (coordinate : ℂ) :
    coordinateSourceComplex ⟶ coordinateTargetComplex :=
  (CochainComplex.singleFunctor (ModuleCat ℤ) 0).map
    (ModuleCat.ofHom (coordinateDifferenceBoundary coordinate))

noncomputable def pairSignMap (stage : Nat)
    (primeIndex : Fin (StageRank stage)) :
    stageLatticeComplex stage ⟶ coordinateSourceComplex :=
  (CochainComplex.singleFunctor (ModuleCat ℤ) 0).map
    (ModuleCat.ofHom (pairSignEvaluation stage primeIndex))

noncomputable def pairCoordinateMap (stage : Nat)
    (primeIndex : Fin (StageRank stage)) (coordinate : ℂ) :
    stageLatticeComplex stage ⟶ coordinateTargetComplex :=
  (CochainComplex.singleFunctor (ModuleCat ℤ) 0).map
    (ModuleCat.ofHom
      (pairCoordinateEvaluation stage primeIndex coordinate))

theorem pairCoordinate_complex_square
    (stage : Nat) (primeIndex : Fin (StageRank stage))
    (coordinate : ℂ) :
    pairSignMap stage primeIndex ≫ coordinateBoundaryMap coordinate =
      stageBoundaryMap stage ≫
        pairCoordinateMap stage primeIndex coordinate := by
  unfold pairSignMap coordinateBoundaryMap stageBoundaryMap pairCoordinateMap
  rw [← Functor.map_comp, ← Functor.map_comp]
  apply congrArg
  apply ModuleCat.hom_ext
  exact pairCoordinate_boundary_square stage primeIndex coordinate

noncomputable def coordinateRelationComplex (coordinate : ℂ) :
    IntegralCochainComplex :=
  CochainComplex.mappingCocone (coordinateBoundaryMap coordinate)

/-- Final coordinate restriction of the full relation complex.  Unlike a
map out of the cokernel, this exists for every coordinate and therefore does
not smuggle the desired zero-locus into its mouth. -/
noncomputable def derivedCoordinateMap
    (stage : Nat) (primeIndex : Fin (StageRank stage))
    (coordinate : ℂ) :
    stageComplex stage ⟶ coordinateRelationComplex coordinate :=
  mappingCoconeMap
    (stageBoundaryMap stage) (coordinateBoundaryMap coordinate)
    (pairSignMap stage primeIndex)
    (pairCoordinateMap stage primeIndex coordinate)
    (pairCoordinate_complex_square stage primeIndex coordinate)

theorem coordinateDifference_eq_zero_iff_fixed (coordinate : ℂ) :
    coordinateDifference coordinate = 0 ↔
      coordinate = coordinateReversal coordinate := by
  exact sub_eq_zero

theorem coordinate_fixed_of_real_eq_half
    (coordinate : ℂ) (realPart : coordinate.re = 1 / 2) :
    coordinate = coordinateReversal coordinate := by
  apply Complex.ext
  · change coordinate.re = 1 - coordinate.re
    linarith
  · simp [coordinateReversal]

/-- Exact terminal regression contract after the upstream derived map has
been generated.  The right-hand side is not used as a producer field. -/
theorem riemannHypothesis_iff_coordinateDifference_zero :
    RiemannHypothesis ↔
      ∀ (coordinate : ℂ),
        riemannZeta coordinate = 0 →
        (¬∃ n : Nat, coordinate = -2 * (n + 1)) →
        coordinate ≠ 1 →
        coordinateDifference coordinate = 0 := by
  constructor
  · intro rh coordinate zetaZero nontrivial notPole
    apply (coordinateDifference_eq_zero_iff_fixed coordinate).2
    exact coordinate_fixed_of_real_eq_half coordinate
      (rh coordinate zetaZero nontrivial notPole)
  · intro boundaryZero coordinate zetaZero nontrivial notPole
    have fixed := (coordinateDifference_eq_zero_iff_fixed coordinate).1
      (boundaryZero coordinate zetaZero nontrivial notPole)
    have realFixed := congrArg Complex.re fixed
    change coordinate.re = 1 - coordinate.re at realFixed
    linarith

end
end CanonicalUnitArithmeticDerivedCoordinateRegression
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
