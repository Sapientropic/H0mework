import H0mework.Versions.R2.Arithmetic.PrimeShadow.LivingLawCanonicalUnitArithmeticCofinalRelationZeroLocus
import H0mework.Versions.R2.Arithmetic.PrimeShadow.LivingLawCanonicalUnitArithmeticDerivedCoordinateRegression

/-!
# Unit-normalized classical coordinate restriction

The affine involution `s ↦ 1 - conj s` becomes an honest integral-linear
involution after adjoining the unit coordinate:

`(n, z) ↦ (n, n - conj z)` on `ℤ × ℂ`.

Each generated arithmetic dual pair maps to `(1,s)` and
`(1,1-conj s)`.  This map intertwines reversal and therefore descends, at
the chain level, through the full relation cofiber for every complex
coordinate.  No zeta-zero or fixed-point law is used to build it.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace CanonicalUnitArithmeticUnitNormalizedCoordinateRegression

open CanonicalUnitArithmeticCofinalRelationAction
open CanonicalUnitArithmeticCofinalRelationHomotopyLimit
open CanonicalUnitArithmeticCofinalRelationZeroLocus
open CanonicalUnitArithmeticCofinalReversalRelation
open CanonicalUnitArithmeticCoordinateProjectionObstruction
open CanonicalUnitArithmeticDerivedCoordinateRegression
open CategoryTheory
open CochainMappingCoconeFunctoriality
open SequentialHomotopyLimit
open scoped ComplexConjugate

noncomputable section

abbrev UnitCoordinate : Type := ℤ × ℂ

/-- Homogeneous linearization of `s ↦ 1 - conj s`. -/
def unitCoordinateReversal : UnitCoordinate →ₗ[ℤ] UnitCoordinate where
  toFun := fun point =>
    (point.1, point.1 • (1 : ℂ) - conj point.2)
  map_add' := by
    intro left right
    ext
    · rfl
    · simp only [Prod.fst_add, Prod.snd_add, map_add, add_smul]
      abel
  map_smul' := by
    intro scalar point
    ext <;> simp [smul_sub]

theorem unitCoordinateReversal_involutive :
    Function.Involutive unitCoordinateReversal := by
  intro point
  rcases point with ⟨unit, coordinate⟩
  ext <;> simp [unitCoordinateReversal, sub_eq_add_neg]

def unitCoordinateGenerator (coordinate : ℂ) : UnitCoordinate :=
  (1, coordinate)

@[simp] theorem unitCoordinateReversal_generator (coordinate : ℂ) :
    unitCoordinateReversal (unitCoordinateGenerator coordinate) =
      unitCoordinateGenerator (coordinateReversal coordinate) := by
  ext <;> simp [unitCoordinateReversal, unitCoordinateGenerator,
    coordinateReversal]

def pairUnitCoordinateEvaluation (stage : Nat)
    (primeIndex : Fin (StageRank stage)) (coordinate : ℂ) :
    StageRelationLattice stage →ₗ[ℤ] UnitCoordinate :=
  (LinearMap.toSpanSingleton ℤ UnitCoordinate
      (unitCoordinateGenerator coordinate)).comp
        (stageCoefficient stage primeIndex 0) +
    (LinearMap.toSpanSingleton ℤ UnitCoordinate
      (unitCoordinateGenerator (coordinateReversal coordinate))).comp
        (stageCoefficient stage primeIndex 1)

theorem pairUnitCoordinateEvaluation_reversal
    (stage : Nat) (primeIndex : Fin (StageRank stage))
    (coordinate : ℂ) :
    (pairUnitCoordinateEvaluation stage primeIndex coordinate).comp
        (stageReversal stage) =
      unitCoordinateReversal.comp
        (pairUnitCoordinateEvaluation stage primeIndex coordinate) := by
  apply LinearMap.ext
  intro value
  change
    value (primeIndex, 1) • unitCoordinateGenerator coordinate +
        value (primeIndex, 0) •
          unitCoordinateGenerator (coordinateReversal coordinate) =
      unitCoordinateReversal
        (value (primeIndex, 0) • unitCoordinateGenerator coordinate +
          value (primeIndex, 1) •
            unitCoordinateGenerator (coordinateReversal coordinate))
  rw [map_add, map_smul, map_smul,
    unitCoordinateReversal_generator,
    unitCoordinateReversal_generator]
  rw [show coordinateReversal (coordinateReversal coordinate) = coordinate by
    unfold coordinateReversal
    apply Complex.ext <;> simp]
  ac_rfl

def unitCoordinateBoundary : UnitCoordinate →ₗ[ℤ] UnitCoordinate :=
  LinearMap.id - unitCoordinateReversal

theorem pairUnitCoordinate_boundary_square
    (stage : Nat) (primeIndex : Fin (StageRank stage))
    (coordinate : ℂ) :
    (pairUnitCoordinateEvaluation stage primeIndex coordinate).comp
        (stageBoundary stage) =
      unitCoordinateBoundary.comp
        (pairUnitCoordinateEvaluation stage primeIndex coordinate) := by
  rw [show stageBoundary stage =
      LinearMap.id - stageReversal stage by
    unfold stageBoundary
    rw [weightedStageReversal_eq_reversal]]
  unfold unitCoordinateBoundary
  rw [LinearMap.comp_sub, LinearMap.sub_comp,
    LinearMap.comp_id, LinearMap.id_comp,
    pairUnitCoordinateEvaluation_reversal]

abbrev UnitCoordinateModule : ModuleCat.{0} ℤ :=
  ModuleCat.of ℤ UnitCoordinate

noncomputable abbrev unitCoordinateComplex : IntegralCochainComplex :=
  (CochainComplex.singleFunctor (ModuleCat ℤ) 0).obj
    UnitCoordinateModule

noncomputable def unitCoordinateBoundaryMap :
    unitCoordinateComplex ⟶ unitCoordinateComplex :=
  (CochainComplex.singleFunctor (ModuleCat ℤ) 0).map
    (ModuleCat.ofHom unitCoordinateBoundary)

noncomputable def unitCoordinateReversalMap :
    unitCoordinateComplex ⟶ unitCoordinateComplex :=
  (CochainComplex.singleFunctor (ModuleCat ℤ) 0).map
    (ModuleCat.ofHom unitCoordinateReversal)

theorem unitCoordinateReversal_boundary_commutes :
    unitCoordinateBoundary.comp unitCoordinateReversal =
      unitCoordinateReversal.comp unitCoordinateBoundary := by
  unfold unitCoordinateBoundary
  rw [LinearMap.sub_comp, LinearMap.comp_sub,
    LinearMap.id_comp, LinearMap.comp_id]

theorem unitCoordinateReversal_complex_boundary_square :
    unitCoordinateReversalMap ≫ unitCoordinateBoundaryMap =
      unitCoordinateBoundaryMap ≫ unitCoordinateReversalMap := by
  unfold unitCoordinateReversalMap unitCoordinateBoundaryMap
  rw [← Functor.map_comp, ← Functor.map_comp]
  apply congrArg
  apply ModuleCat.hom_ext
  exact unitCoordinateReversal_boundary_commutes

noncomputable def pairUnitCoordinateMap (stage : Nat)
    (primeIndex : Fin (StageRank stage)) (coordinate : ℂ) :
    stageLatticeComplex stage ⟶ unitCoordinateComplex :=
  (CochainComplex.singleFunctor (ModuleCat ℤ) 0).map
    (ModuleCat.ofHom
      (pairUnitCoordinateEvaluation stage primeIndex coordinate))

theorem pairUnitCoordinate_complex_square
    (stage : Nat) (primeIndex : Fin (StageRank stage))
    (coordinate : ℂ) :
    pairUnitCoordinateMap stage primeIndex coordinate ≫
        unitCoordinateBoundaryMap =
      stageBoundaryMap stage ≫
        pairUnitCoordinateMap stage primeIndex coordinate := by
  unfold pairUnitCoordinateMap unitCoordinateBoundaryMap stageBoundaryMap
  rw [← Functor.map_comp, ← Functor.map_comp]
  apply congrArg
  apply ModuleCat.hom_ext
  exact (pairUnitCoordinate_boundary_square
    stage primeIndex coordinate).symm

noncomputable abbrev unitCoordinateRelationComplex : IntegralCochainComplex :=
  CochainComplex.mappingCocone unitCoordinateBoundaryMap

noncomputable def unitCoordinateRelationReversal :
    unitCoordinateRelationComplex ⟶ unitCoordinateRelationComplex :=
  mappingCoconeMap unitCoordinateBoundaryMap unitCoordinateBoundaryMap
    unitCoordinateReversalMap unitCoordinateReversalMap
    unitCoordinateReversal_complex_boundary_square

/-- Unit-normalized coordinate restriction of one full finite relation
complex.  It exists for every coordinate. -/
noncomputable def stageUnitCoordinateMap
    (stage : Nat) (primeIndex : Fin (StageRank stage))
    (coordinate : ℂ) :
    stageComplex stage ⟶ unitCoordinateRelationComplex :=
  mappingCoconeMap (stageBoundaryMap stage) unitCoordinateBoundaryMap
    (pairUnitCoordinateMap stage primeIndex coordinate)
    (pairUnitCoordinateMap stage primeIndex coordinate)
    (pairUnitCoordinate_complex_square stage primeIndex coordinate)

theorem pairUnitCoordinateMap_reversal
    (stage : Nat) (primeIndex : Fin (StageRank stage))
    (coordinate : ℂ) :
    stageReversalMap stage ≫
        pairUnitCoordinateMap stage primeIndex coordinate =
      pairUnitCoordinateMap stage primeIndex coordinate ≫
        unitCoordinateReversalMap := by
  unfold stageReversalMap pairUnitCoordinateMap unitCoordinateReversalMap
  rw [← Functor.map_comp, ← Functor.map_comp]
  apply congrArg
  apply ModuleCat.hom_ext
  exact pairUnitCoordinateEvaluation_reversal stage primeIndex coordinate

theorem stageUnitCoordinateMap_reversal
    (stage : Nat) (primeIndex : Fin (StageRank stage))
    (coordinate : ℂ) :
    stageRelationReversal stage ≫
        stageUnitCoordinateMap stage primeIndex coordinate =
      stageUnitCoordinateMap stage primeIndex coordinate ≫
        unitCoordinateRelationReversal := by
  unfold stageRelationReversal stageUnitCoordinateMap
    unitCoordinateRelationReversal
  rw [← mappingCoconeMap_comp, ← mappingCoconeMap_comp]
  apply mappingCoconeMap_congr
  · exact pairUnitCoordinateMap_reversal stage primeIndex coordinate
  · exact pairUnitCoordinateMap_reversal stage primeIndex coordinate

noncomputable def towerUnitCoordinateMap
    (stage : Nat) (primeIndex : Fin (StageRank stage))
    (coordinate : ℂ) :
    homotopyLimitFace.towerObject stage ⟶
      unitCoordinateRelationComplex := by
  change stageComplex stage ⟶ unitCoordinateRelationComplex
  exact stageUnitCoordinateMap stage primeIndex coordinate

theorem towerUnitCoordinateMap_reversal
    (stage : Nat) (primeIndex : Fin (StageRank stage))
    (coordinate : ℂ) :
    reversalActionFace.componentAt stage ≫
        towerUnitCoordinateMap stage primeIndex coordinate =
      towerUnitCoordinateMap stage primeIndex coordinate ≫
        unitCoordinateRelationReversal := by
  change stageRelationReversal stage ≫
        stageUnitCoordinateMap stage primeIndex coordinate =
      stageUnitCoordinateMap stage primeIndex coordinate ≫
        unitCoordinateRelationReversal
  exact stageUnitCoordinateMap_reversal stage primeIndex coordinate

/-- Coordinate restriction of the global relation limit through one actual
finite prime stage. -/
noncomputable def globalUnitCoordinateMap
    (stage : Nat) (primeIndex : Fin (StageRank stage))
    (coordinate : ℂ) :
  derivedRelationLimit ⟶ unitCoordinateRelationComplex :=
  homotopyLimitFace.restriction stage ≫
    towerUnitCoordinateMap stage primeIndex coordinate

theorem globalUnitCoordinateMap_reversal
    (stage : Nat) (primeIndex : Fin (StageRank stage))
    (coordinate : ℂ) :
    derivedRelationReversal ≫
        globalUnitCoordinateMap stage primeIndex coordinate =
      globalUnitCoordinateMap stage primeIndex coordinate ≫
        unitCoordinateRelationReversal := by
  unfold globalUnitCoordinateMap
  unfold derivedRelationReversal
  calc
    reversalActionFace.homotopyLimitAction ≫
        (homotopyLimitFace.restriction stage ≫
          towerUnitCoordinateMap stage primeIndex coordinate) =
      (reversalActionFace.homotopyLimitAction ≫
        homotopyLimitFace.restriction stage) ≫
          towerUnitCoordinateMap stage primeIndex coordinate :=
        (Category.assoc _ _ _).symm
    _ = (homotopyLimitFace.restriction stage ≫
        reversalActionFace.componentAt stage) ≫
          towerUnitCoordinateMap stage primeIndex coordinate := by
      rw [reversalActionFace.homotopyLimitAction_restriction]
    _ = homotopyLimitFace.restriction stage ≫
        (reversalActionFace.componentAt stage ≫
          towerUnitCoordinateMap stage primeIndex coordinate) :=
      Category.assoc _ _ _
    _ = homotopyLimitFace.restriction stage ≫
        (towerUnitCoordinateMap stage primeIndex coordinate ≫
          unitCoordinateRelationReversal) := by
      rw [towerUnitCoordinateMap_reversal]
    _ = (homotopyLimitFace.restriction stage ≫
          towerUnitCoordinateMap stage primeIndex coordinate) ≫
        unitCoordinateRelationReversal :=
      (Category.assoc _ _ _).symm

noncomputable def unitCoordinateAntiInvariantTransition :
    unitCoordinateRelationComplex ⟶ unitCoordinateRelationComplex :=
  𝟙 unitCoordinateRelationComplex - unitCoordinateRelationReversal

theorem globalAntiInvariant_coordinate_square
    (stage : Nat) (primeIndex : Fin (StageRank stage))
    (coordinate : ℂ) :
    antiInvariantTransition ≫
        globalUnitCoordinateMap stage primeIndex coordinate =
      globalUnitCoordinateMap stage primeIndex coordinate ≫
        unitCoordinateAntiInvariantTransition := by
  unfold antiInvariantTransition unitCoordinateAntiInvariantTransition
  rw [Preadditive.sub_comp, Preadditive.comp_sub,
    globalUnitCoordinateMap_reversal]
  simp

noncomputable abbrev unitCoordinateZeroLocusComplex : IntegralCochainComplex :=
  CochainComplex.mappingCocone unitCoordinateAntiInvariantTransition

/-- The full source-generated global zero-locus has a unit-normalized
classical coordinate restriction for every complex coordinate.  The map
still assumes no zeta-zero or boundary-zero law. -/
noncomputable def zeroLocusUnitCoordinateMap
    (stage : Nat) (primeIndex : Fin (StageRank stage))
    (coordinate : ℂ) :
    zeroLocusComplex ⟶ unitCoordinateZeroLocusComplex :=
  mappingCoconeMap antiInvariantTransition
    unitCoordinateAntiInvariantTransition
    (globalUnitCoordinateMap stage primeIndex coordinate)
    (globalUnitCoordinateMap stage primeIndex coordinate)
    (globalAntiInvariant_coordinate_square
      stage primeIndex coordinate).symm

theorem unitCoordinateBoundary_generator (coordinate : ℂ) :
    unitCoordinateBoundary (unitCoordinateGenerator coordinate) =
      (0, coordinateDifference coordinate) := by
  ext <;> simp [unitCoordinateBoundary, unitCoordinateGenerator,
    unitCoordinateReversal, coordinateDifference, coordinateReversal]

theorem unitCoordinateBoundary_generator_eq_zero_iff_fixed
    (coordinate : ℂ) :
    unitCoordinateBoundary (unitCoordinateGenerator coordinate) = 0 ↔
      coordinate = coordinateReversal coordinate := by
  rw [unitCoordinateBoundary_generator]
  constructor
  · intro equality
    apply (coordinateDifference_eq_zero_iff_fixed coordinate).1
    exact congrArg Prod.snd equality
  · intro fixed
    apply Prod.ext
    · simp
    · simpa using (coordinateDifference_eq_zero_iff_fixed coordinate).2 fixed

end
end CanonicalUnitArithmeticUnitNormalizedCoordinateRegression
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
