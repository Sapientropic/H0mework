import H0mework.Realization.MappingCone.BoundaryAtom
import H0mework.Versions.R2.Arithmetic.EulerGlobal.CofiberFamily
import H0mework.Realization.GlobalSections.CofinalPrimeRigidity

/-!
# Cofinal rigidity of the integral tautological family

The family-level action cofiber is already rooted and its tautological
inclusion has actual local boundary rows.  This file applies those rows to an
arbitrary integral cocycle of the same global whole-relation complex.

The domain supplies one runtime stage carrying the currently scheduled prime
power and the actual restriction to the next such stage.  Every local carrier
is the existing finite free full-Euler recurrence carrier.  The frozen
local-process kernel generates the schedule, all division roots, same-component
history, and rigidity.  No point, normalized unit, completed table, or scalar
zero-fibre inverse is supplied.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace CanonicalUnitArithmeticIntegralActionCofiberCofinalRigidity

open CanonicalUnitArithmeticFactorizationEulerDependentDiagram
open CanonicalUnitArithmeticFactorizationFullEulerSolutionAction
open CanonicalUnitArithmeticFactorizationFullEulerWholeRelationComplexAction
open CanonicalUnitArithmeticFactorizationFullEulerWholeRelationDerivedDeterminantSection
open CanonicalUnitArithmeticFactorizationFullEulerWholeRelationGlobalAction
open CanonicalUnitArithmeticFactorizationFullEulerWholeRelationUniversalSolution
open CanonicalUnitArithmeticFactorizationFullEulerWholeRelationUniversalSolutionLocalLanding
open CanonicalUnitArithmeticFactorizationOccurrence
open CanonicalUnitArithmeticFactorizationWholeHistorySolutionCarrier
open CanonicalUnitArithmeticFactorizationWholeHistorySolutionCofinalRigidity
open CofinalPrimePowerRestrictionRigidity
open CofinalPrimePowerRestrictionRigidity.RootGeneratedCofinalPrimePowerRestrictionHistoryAt
open CategoryTheory
open CategoryTheory.Limits
open SaturationMonoid.CochainMappingCoconeMappedBoundaryAtom

noncomputable section

/-! ## The entire integral cocycle family -/

abbrev IntegralGlobalCocycleKernel := LinearMap.ker globalDifferential

def localIntegralVertex (stage : Nat) :
    IntegralGlobalCocycleKernel →ₗ[ℤ]
      WholeVertexModule seedOccurrence.root stage where
  toFun value := vertexRestriction stage value.1
  map_add' left right := by simp
  map_smul' scalar value := by simp

theorem localIntegralVertex_differential_zero (stage : Nat)
    (value : IntegralGlobalCocycleKernel) :
    factorizationDifferential seedOccurrence.root stage
        (localIntegralVertex stage value) = 0 := by
  have square := LinearMap.congr_fun
    (globalRestriction_differential_square stage) value.1
  change
    factorizationDifferential seedOccurrence.root stage
        (vertexRestriction stage value.1) =
      relationRestriction stage (globalDifferential value.1) at square
  rw [LinearMap.mem_ker.mp value.2, map_zero] at square
  exact square

def localIntegralWholeAntiInvariant (stage : Nat)
    (value : IntegralGlobalCocycleKernel) :
    InnerCarrier seedOccurrence.root stage :=
  innerAntiInvariant seedOccurrence.root stage
    (wholeValue (localIntegralVertex stage value))

def localIntegralQuotientAntiInvariant (stage : Nat)
    (row : FactorRow seedOccurrence.root stage)
    (value : IntegralGlobalCocycleKernel) :
    InnerCarrier seedOccurrence.root stage :=
  innerAntiInvariant seedOccurrence.root stage
    (quotientValue (localIntegralVertex stage value) row)

theorem localIntegral_factorization_landing
    (stage : Nat) (row : FactorRow seedOccurrence.root stage)
    (value : IntegralGlobalCocycleKernel) :
    localIntegralWholeAntiInvariant stage value =
      (rowPrime row : Nat) ^ rowExponent row •
        localIntegralQuotientAntiInvariant stage row value := by
  have equation := congrFun
    (localIntegralVertex_differential_zero stage value) row
  change
    localIntegralWholeAntiInvariant stage value -
      (((rowPrime row : Nat) : ℤ) ^ rowExponent row) •
        localIntegralQuotientAntiInvariant stage row value = 0 at equation
  rw [sub_eq_zero] at equation
  simpa only [← Nat.cast_pow, natCast_zsmul] using equation

/-! ## Actual source restrictions -/

def runtimeSuccessorArrow (stage : Nat) :
    (Opposite.op (stage + 1) : ℕᵒᵖ) ⟶ Opposite.op stage :=
  (homOfLE (Nat.le_succ stage)).op

theorem actualDiagram_map_runtimeSuccessor (stage : Nat) :
    CanonicalUnitArithmeticFactorizationFullEulerWholeRelationGlobalAction.globalFace.actualDiagram.map
        (runtimeSuccessorArrow stage) =
      directRestriction seedOccurrence.root stage := by
  change (localRelationDiagram seedOccurrence.root).map
      (runtimeSuccessorArrow stage) = _
  simp only [localRelationDiagram, runtimeSuccessorArrow,
    Functor.ofOpSequence_map_homOfLE_succ]

theorem localIntegralVertex_successor (stage : Nat)
    (value : IntegralGlobalCocycleKernel) :
    CanonicalUnitArithmeticFactorizationFullEulerWholeRelationComplexAction.vertexRestriction
        seedOccurrence.root stage
        (localIntegralVertex (stage + 1) value) =
      localIntegralVertex stage value := by
  have coneSquare :=
    CanonicalUnitArithmeticFactorizationFullEulerWholeRelationGlobalAction.globalFace.restriction_naturality
      (runtimeSuccessorArrow stage)
  rw [actualDiagram_map_runtimeSuccessor] at coneSquare
  have degreeZero := congrArg
    (fun arrow :
        CanonicalUnitArithmeticFactorizationFullEulerWholeRelationGlobalAction.GlobalState ⟶
        (localRelationDiagram seedOccurrence.root).obj
          (Opposite.op stage) =>
      (arrow.f 0).hom value.1)
    coneSquare
  exact degreeZero

theorem localIntegralWholeAntiInvariant_successor (stage : Nat)
    (value : IntegralGlobalCocycleKernel) :
    CanonicalUnitArithmeticFactorizationFullEulerSolutionAction.carrierRestriction
        seedOccurrence.root stage
        (localIntegralWholeAntiInvariant (stage + 1) value) =
      localIntegralWholeAntiInvariant stage value := by
  unfold localIntegralWholeAntiInvariant
  rw [← innerAntiInvariant_restriction]
  exact congrArg
    (innerAntiInvariant seedOccurrence.root stage)
    (congrArg wholeValue (localIntegralVertex_successor stage value))

def innerRestrictionFromOffset (base : Nat) :
    (offset : Nat) →
      InnerCarrier seedOccurrence.root (base + offset) →ₗ[ℤ]
        InnerCarrier seedOccurrence.root base
  | 0 => LinearMap.id
  | offset + 1 =>
      (innerRestrictionFromOffset base offset).comp
        (CanonicalUnitArithmeticFactorizationFullEulerSolutionAction.carrierRestriction
          seedOccurrence.root (base + offset))

theorem innerRestrictionFromOffset_component (base : Nat)
    (value : IntegralGlobalCocycleKernel) :
    ∀ offset,
      innerRestrictionFromOffset base offset
          (localIntegralWholeAntiInvariant (base + offset) value) =
        localIntegralWholeAntiInvariant base value
  | 0 => rfl
  | offset + 1 => by
      change innerRestrictionFromOffset base offset
          (CanonicalUnitArithmeticFactorizationFullEulerSolutionAction.carrierRestriction
            seedOccurrence.root (base + offset)
              (localIntegralWholeAntiInvariant (base + offset + 1) value)) = _
      rw [localIntegralWholeAntiInvariant_successor,
        innerRestrictionFromOffset_component base value offset]

def innerCarrierCast {source target : Nat} (equality : source = target) :
    InnerCarrier seedOccurrence.root source →ₗ[ℤ]
      InnerCarrier seedOccurrence.root target := by
  subst target
  exact LinearMap.id

theorem innerCarrierCast_component {source target : Nat}
    (equality : source = target) (value : IntegralGlobalCocycleKernel) :
    innerCarrierCast equality
        (localIntegralWholeAntiInvariant source value) =
      localIntegralWholeAntiInvariant target value := by
  subst target
  rfl

def innerRestrictionBetween (base target : Nat) (order : base ≤ target) :
    InnerCarrier seedOccurrence.root target →ₗ[ℤ]
      InnerCarrier seedOccurrence.root base :=
  (innerRestrictionFromOffset base (target - base)).comp
    (innerCarrierCast (Nat.add_sub_of_le order).symm)

theorem innerRestrictionBetween_component (base target : Nat)
    (order : base ≤ target) (value : IntegralGlobalCocycleKernel) :
    innerRestrictionBetween base target order
        (localIntegralWholeAntiInvariant target value) =
      localIntegralWholeAntiInvariant base value := by
  unfold innerRestrictionBetween
  change innerRestrictionFromOffset base (target - base)
      (innerCarrierCast (Nat.add_sub_of_le order).symm
        (localIntegralWholeAntiInvariant target value)) = _
  rw [innerCarrierCast_component,
    innerRestrictionFromOffset_component]

/-! ## Runtime schedule generated from one successor -/

def scheduledPower (cursor : Nat) : Nat :=
  (scheduledPrime cursor : Nat) ^ scheduledExponent cursor

def scheduledRuntimeStage (base : Nat) : Nat → Nat
  | 0 => max base (scheduledPower 0)
  | cursor + 1 =>
      max (scheduledRuntimeStage base cursor + 1)
        (scheduledPower (cursor + 1))

theorem base_le_scheduledRuntimeStage (base : Nat) :
    ∀ cursor, base ≤ scheduledRuntimeStage base cursor
  | 0 => Nat.le_max_left _ _
  | cursor + 1 =>
      (base_le_scheduledRuntimeStage base cursor).trans
        ((Nat.le_succ _).trans (Nat.le_max_left _ _))

theorem scheduledPower_le_runtimeStage (base : Nat) :
    ∀ cursor, scheduledPower cursor ≤ scheduledRuntimeStage base cursor
  | 0 => Nat.le_max_right _ _
  | _cursor + 1 => Nat.le_max_right _ _

theorem scheduledRuntimeStage_mono_succ (base cursor : Nat) :
    scheduledRuntimeStage base cursor ≤
      scheduledRuntimeStage base (cursor + 1) :=
  (Nat.le_succ _).trans (Nat.le_max_left _ _)

def factorAdvanceBy
    {prime : Nat.Primes} {exponent : Nat} :
    Nat → RuntimePrimePowerFactorAt prime exponent →
      RuntimePrimePowerFactorAt prime exponent
  | 0, factor => factor
  | count + 1, factor => factorAdvanceBy count factor |>.advance

@[simp] theorem factorAdvanceBy_stage
    {prime : Nat.Primes} {exponent : Nat}
    (count : Nat) (factor : RuntimePrimePowerFactorAt prime exponent) :
    (factorAdvanceBy count factor).stage = factor.stage + count := by
  induction count with
  | zero => rfl
  | succ count inductionHypothesis =>
      simp [factorAdvanceBy, inductionHypothesis, Nat.add_assoc]

def scheduledFactorAt (base cursor : Nat) :
    RuntimePrimePowerFactorAt
      (scheduledPrime cursor) (scheduledExponent cursor) :=
  let initial := RuntimePrimePowerFactorAt.generate
    (scheduledPrime cursor) (scheduledExponent cursor)
      (scheduledExponent_positive cursor)
  factorAdvanceBy
    (scheduledRuntimeStage base cursor - scheduledPower cursor) initial

theorem scheduledFactorAt_stage (base cursor : Nat) :
    (scheduledFactorAt base cursor).stage =
      scheduledRuntimeStage base cursor := by
  unfold scheduledFactorAt
  rw [factorAdvanceBy_stage]
  change scheduledPower cursor +
      (scheduledRuntimeStage base cursor - scheduledPower cursor) = _
  exact Nat.add_sub_of_le (scheduledPower_le_runtimeStage base cursor)

/-! ## Direct frozen local-process splice -/

def localProcess (base : Nat) (value : IntegralGlobalCocycleKernel) :
    PrimePowerRestrictionLocalProcessAt Nat where
  cursor state := state
  Carrier state := AddCommGrpCat.of
    (InnerCarrier seedOccurrence.root (scheduledRuntimeStage base state))
  component state :=
    localIntegralWholeAntiInvariant (scheduledRuntimeStage base state) value
  finiteGenerated _state := Module.Finite.iff_addGroup_fg.mp inferInstance
  quotientZero state := by
    let factor := scheduledFactorAt base state
    have factorStage := scheduledFactorAt_stage base state
    rw [← factorStage]
    let row := stageFactorRow factor
    have landing := localIntegral_factorization_landing
      factor.stage row value
    rw [stageFactorRow_prime, stageFactorRow_exponent] at landing
    apply (QuotientAddGroup.eq_zero_iff
      (localIntegralWholeAntiInvariant factor.stage value)).2
    exact ⟨localIntegralQuotientAntiInvariant factor.stage row value,
      landing.symm⟩
  next state := state + 1
  cursor_next _state := rfl
  restriction state :=
    (innerRestrictionBetween
      (scheduledRuntimeStage base state)
      (scheduledRuntimeStage base (state + 1))
      (scheduledRuntimeStage_mono_succ base state)).toAddMonoidHom
  component_next state :=
    innerRestrictionBetween_component
      (scheduledRuntimeStage base state)
      (scheduledRuntimeStage base (state + 1))
      (scheduledRuntimeStage_mono_succ base state) value

def processSeedOccurrence (_base : Nat) (_value : IntegralGlobalCocycleKernel) :
    RootedAccountedUnfolding (FactorizationPayload × Nat) :=
  seedOccurrence.map fun root => (root, 0)

def processOccurrence (base : Nat) (value : IntegralGlobalCocycleKernel) :
    RootedAccountedUnfolding
      (FactorizationPayload × PrimePowerRestrictionLocalProcessAt Nat) :=
  seedOccurrence.map fun root => (root, localProcess base value)

theorem process_projects (base : Nat) (value : IntegralGlobalCocycleKernel) :
    (processOccurrence base value).map Prod.fst =
      (processSeedOccurrence base value).map Prod.fst := by
  unfold processOccurrence processSeedOccurrence
  rw [RootedAccountedUnfolding.map_map,
    RootedAccountedUnfolding.map_map]
  rfl

theorem process_seed_cursor (base : Nat)
    (value : IntegralGlobalCocycleKernel) :
    (processOccurrence base value).root.2.cursor
      (processSeedOccurrence base value).root.2 = 0 :=
  rfl

def historyFace (base : Nat) (value : IntegralGlobalCocycleKernel) :
    RootGeneratedCofinalPrimePowerRestrictionHistoryAt
      (processSeedOccurrence base value) (processOccurrence base value)
        (process_projects base value) (process_seed_cursor base value) :=
  RootGeneratedCofinalPrimePowerRestrictionHistoryAt.generate

theorem scheduledSeedComponent_eq_zero (base : Nat)
    (value : IntegralGlobalCocycleKernel) :
    localIntegralWholeAntiInvariant (scheduledRuntimeStage base 0) value = 0 :=
  (historyFace base value).generatedSeedComponent_eq_zero

/-- Frozen all-prime rigidity kills the whole anti-invariant of every
integral cocycle in the actual global relation family. -/
theorem everyLocalIntegralWholeAntiInvariant_eq_zero (base : Nat)
    (value : IntegralGlobalCocycleKernel) :
    localIntegralWholeAntiInvariant base value = 0 := by
  have generated := congrArg
    (innerRestrictionBetween base (scheduledRuntimeStage base 0)
      (base_le_scheduledRuntimeStage base 0))
    (scheduledSeedComponent_eq_zero base value)
  rw [innerRestrictionBetween_component, map_zero] at generated
  exact generated

theorem preserves_exact_root_actual_rows_and_frozen_rigidity
    (base : Nat) (value : IntegralGlobalCocycleKernel) :
    (historyFace base value).root = seedOccurrence ∧
      localIntegralWholeAntiInvariant base value = 0 := by
  constructor
  · unfold RootGeneratedCofinalPrimePowerRestrictionHistoryAt.root
      processSeedOccurrence
    rw [RootedAccountedUnfolding.map_map]
    exact RootedAccountedUnfolding.map_id _
  · exact everyLocalIntegralWholeAntiInvariant_eq_zero base value

/-! ## Readback through the already generated action-cofiber family -/

def integralCocycleScalarInclusion :
    IntegralGlobalCocycleKernel →ₗ[ℤ] ScalarVertex where
  toFun value := TensorProduct.mk ℤ CoefficientRing GlobalVertex 1 value.1
  map_add' left right :=
    (TensorProduct.mk ℤ CoefficientRing GlobalVertex 1).map_add
      left.1 right.1
  map_smul' scalar value := by
    have sourceSmul : (scalar • value).1 =
        (inferInstance : Module ℤ GlobalVertex).smul scalar value.1 :=
      (int_smul_eq_zsmul
        (inferInstance : Module ℤ GlobalVertex) scalar value.1).symm
    change (TensorProduct.mk ℤ CoefficientRing GlobalVertex 1)
        (scalar • value).1 =
      scalar • (TensorProduct.mk ℤ CoefficientRing GlobalVertex 1) value.1
    rw [sourceSmul]
    exact (TensorProduct.mk ℤ CoefficientRing GlobalVertex 1).map_smul
      scalar value.1

theorem integralCocycleScalarInclusion_differential_zero
    (value : IntegralGlobalCocycleKernel) :
    extendedDifferential (integralCocycleScalarInclusion value) = 0 := by
  change (1 : CoefficientRing) ⊗ₜ[ℤ] globalDifferential value.1 = 0
  rw [LinearMap.mem_ker.mp value.2, TensorProduct.tmul_zero]

theorem integralCocycleScalarInclusion_local (stage : Nat)
    (value : IntegralGlobalCocycleKernel) :
    localTensorRestriction stage (integralCocycleScalarInclusion value) =
      TensorProduct.mk ℤ (LocalCoefficientRing stage)
        (LocalVertex stage) 1 (localIntegralVertex stage value) := by
  change
    (limit.π
        CanonicalUnitArithmeticFactorizationFullEulerGlobalZeroFiber.GlobalZeroFiberDiagram
        (Opposite.op stage)).hom 1 ⊗ₜ[ℤ]
        (CanonicalUnitArithmeticFactorizationFullEulerWholeRelationUniversalSolutionLocalLanding.vertexRestriction
          stage) value.1 =
      (1 : LocalCoefficientRing stage) ⊗ₜ[ℤ]
        (CanonicalUnitArithmeticFactorizationFullEulerWholeRelationUniversalSolutionLocalLanding.vertexRestriction
          stage) value.1
  rw [map_one]

/-- The anti-invariant coordinate of the tautological family vanishes on
every integral global cocycle, and the proof factors through the direct
frozen local-process consumer above. -/
theorem integralTautologicalAntiInvariant_eq_zero (stage : Nat)
    (value : IntegralGlobalCocycleKernel) :
    localWholeAntiInvariantComponent stage
        (localTensorRestriction stage
          (integralCocycleScalarInclusion value)) = 0 := by
  rw [integralCocycleScalarInclusion_local]
  change (1 : LocalCoefficientRing stage) ⊗ₜ[ℤ]
      localIntegralWholeAntiInvariant stage value = 0
  rw [everyLocalIntegralWholeAntiInvariant_eq_zero,
    TensorProduct.tmul_zero]

/-! ## The same cofiber point enters frozen rigidity -/

def tautologicalElementHom (value : ScalarVertex) :
    IntegralUnit ⟶ CanonicalUnitArithmeticIntegralActionCofiberFamily.ScalarVertexObject :=
  elementHom value

noncomputable def tautologicalScalarVertexPointMap (value : ScalarVertex) :
    (CochainComplex.singleFunctor (ModuleCat ℤ) 0).obj IntegralUnit ⟶
      CanonicalUnitArithmeticIntegralActionCofiberFamily.scalarVertexSingle :=
  (CochainComplex.singleFunctor (ModuleCat ℤ) 0).map
    (tautologicalElementHom value)

theorem tautologicalScalarVertexPointMap_differential_zero
    (value : ScalarVertex) (zeroLaw : extendedDifferential value = 0) :
    tautologicalScalarVertexPointMap value ≫
        CanonicalUnitArithmeticIntegralActionCofiberFamily.scalarDifferentialMap = 0 := by
  unfold tautologicalScalarVertexPointMap
    CanonicalUnitArithmeticIntegralActionCofiberFamily.scalarDifferentialMap
  rw [← Functor.map_comp]
  unfold tautologicalElementHom
  rw [elementHom_comp]
  change (CochainComplex.singleFunctor (ModuleCat ℤ) 0).map
    (elementHom
      (M := CanonicalUnitArithmeticIntegralActionCofiberFamily.ScalarRelationObject)
      (extendedDifferential value)) = 0
  rw [zeroLaw, elementHom_zero]
  simp

/-- The caller supplies only an actual cocycle.  The mapping-cocone universal
property, rather than a chosen cofiber element, generates its point in the
whole relation family. -/
noncomputable def tautologicalWholeSourcePointMap
    (value : ScalarVertex) (zeroLaw : extendedDifferential value = 0) :
    (CochainComplex.singleFunctor (ModuleCat ℤ) 0).obj IntegralUnit ⟶
      CanonicalUnitArithmeticIntegralActionCofiberFamily.ScalarWholeRelationComplex :=
  CochainComplex.mappingCocone.lift
    CanonicalUnitArithmeticIntegralActionCofiberFamily.scalarDifferentialMap
    (tautologicalScalarVertexPointMap value) 0 (by
      rw [tautologicalScalarVertexPointMap_differential_zero value zeroLaw]
      simp)

@[reassoc] theorem tautologicalWholeSourcePointMap_fst
    (value : ScalarVertex) (zeroLaw : extendedDifferential value = 0) :
    tautologicalWholeSourcePointMap value zeroLaw ≫
        CochainComplex.mappingCocone.fst
          CanonicalUnitArithmeticIntegralActionCofiberFamily.scalarDifferentialMap =
      tautologicalScalarVertexPointMap value := by
  exact CochainComplex.mappingCocone.lift_fst _ _ _ _

@[reassoc] theorem tautologicalWholeSourcePointMap_fst_zero
    (value : ScalarVertex) (zeroLaw : extendedDifferential value = 0) :
    (tautologicalWholeSourcePointMap value zeroLaw).f 0 ≫
        (CochainComplex.mappingCocone.fst
          CanonicalUnitArithmeticIntegralActionCofiberFamily.scalarDifferentialMap).f 0 =
      (tautologicalScalarVertexPointMap value).f 0 := by
  exact congrArg (fun arrow => arrow.f 0)
    (tautologicalWholeSourcePointMap_fst value zeroLaw)

/-- This is the actual point obtained by applying the framework-owned
tautological inclusion to the generated source cocycle. -/
noncomputable def wholeTautologicalPoint
    (value : ScalarVertex) (zeroLaw : extendedDifferential value = 0) :
    ((CochainComplex.singleFunctor (ModuleCat ℤ) 0).obj
      IntegralUnit).X 0 ⟶
        CanonicalUnitArithmeticIntegralActionCofiberFamily.WholeActionCofiber.X 1 :=
  (tautologicalWholeSourcePointMap value zeroLaw).f 0 ≫
    CanonicalUnitArithmeticIntegralActionCofiberFamily.wholeTautologicalInclusion.1.v
      0 1 (by omega)

/-- The anti-invariant readback is taken from that same point, after the
actual local restriction. -/
noncomputable def localTautologicalAntiInvariantReadback
    (stage : Nat) (value : ScalarVertex)
    (zeroLaw : extendedDifferential value = 0) :
    ((CochainComplex.singleFunctor (ModuleCat ℤ) 0).obj
      IntegralUnit).X 0 ⟶
        (CanonicalUnitArithmeticIntegralActionCofiberFamily.localScalarInnerSingle
          stage).X 0 :=
  wholeTautologicalPoint value zeroLaw ≫
    (CanonicalUnitArithmeticIntegralActionCofiberFamily.wholeCofiberRestriction
      stage).f 1 ≫
    (CochainComplex.mappingCocone.snd
      (CanonicalUnitArithmeticIntegralActionCofiberFamily.localWholeActionMap
        stage)).v 1 0 (by omega) ≫
    (CanonicalUnitArithmeticIntegralActionCofiberFamily.localWholeAntiInvariantCoordinateMap
      stage).f 0

theorem tautologicalScalarVertexPointMap_coordinate
    (stage : Nat) (value : ScalarVertex) :
    tautologicalScalarVertexPointMap value ≫
        CanonicalUnitArithmeticIntegralActionCofiberFamily.globalToLocalMap stage ≫
        CanonicalUnitArithmeticIntegralActionCofiberFamily.localWholeAntiInvariantSingleMap
          stage =
      (CochainComplex.singleFunctor (ModuleCat ℤ) 0).map
        (elementHom
          (M := CanonicalUnitArithmeticIntegralActionCofiberFamily.LocalScalarInnerObject
            stage)
          (localWholeAntiInvariantComponent stage
            (localTensorRestriction stage value))) := by
  unfold tautologicalScalarVertexPointMap
    CanonicalUnitArithmeticIntegralActionCofiberFamily.globalToLocalMap
    CanonicalUnitArithmeticIntegralActionCofiberFamily.localWholeAntiInvariantSingleMap
  rw [← Functor.map_comp, ← Functor.map_comp]
  apply congrArg
  unfold tautologicalElementHom
  rw [elementHom_comp]
  rfl

/-- Provenance splice: the cofiber readback is definitionally the exact
component used by the local prime-power process, not a theorem paired with an
independent value owner. -/
theorem localTautologicalAntiInvariantReadback_eq_component
    (stage : Nat) (value : ScalarVertex)
    (zeroLaw : extendedDifferential value = 0) :
    localTautologicalAntiInvariantReadback stage value zeroLaw =
      ((CochainComplex.singleFunctor (ModuleCat ℤ) 0).map
        (elementHom
          (M := CanonicalUnitArithmeticIntegralActionCofiberFamily.LocalScalarInnerObject
            stage)
          (localWholeAntiInvariantComponent stage
            (localTensorRestriction stage value)))).f 0 := by
  simp only [localTautologicalAntiInvariantReadback,
    wholeTautologicalPoint, Category.assoc]
  rw [CanonicalUnitArithmeticIntegralActionCofiberFamily.wholeTautologicalInclusion_restriction_v_assoc,
    CanonicalUnitArithmeticIntegralActionCofiberFamily.localWholeTautologicalInclusion_readback_v_assoc]
  simp only [CanonicalUnitArithmeticIntegralActionCofiberFamily.localWholeAntiInvariantCoordinateMap,
    HomologicalComplex.comp_f]
  rw [CanonicalUnitArithmeticIntegralActionCofiberFamily.globalToLocalWholeRelationMap_fst_zero_assoc,
    tautologicalWholeSourcePointMap_fst_zero_assoc]
  exact congrArg (fun arrow => arrow.f 0)
    (tautologicalScalarVertexPointMap_coordinate stage value)

/-- Frozen rigidity now acts on the literal readback of the same
framework-generated cofiber point. -/
theorem localIntegralTautologicalReadback_eq_zero
    (stage : Nat) (value : IntegralGlobalCocycleKernel) :
    localTautologicalAntiInvariantReadback stage
        (integralCocycleScalarInclusion value)
        (integralCocycleScalarInclusion_differential_zero value) = 0 := by
  rw [localTautologicalAntiInvariantReadback_eq_component,
    integralTautologicalAntiInvariant_eq_zero stage value]
  simp

/-! ## Entire zero-fibre scalar span of the integral cocycle family -/

def integralCocycleSubtype : IntegralGlobalCocycleKernel →ₗ[ℤ] GlobalVertex where
  toFun value := value.1
  map_add' _left _right := rfl
  map_smul' scalar value := by
    change (scalar • value).1 =
      (inferInstance : Module ℤ GlobalVertex).smul scalar value.1
    exact (int_smul_eq_zsmul
      (inferInstance : Module ℤ GlobalVertex) scalar value.1).symm

abbrev IntegralScalarCocycleCarrier :=
  TensorProduct ℤ CoefficientRing IntegralGlobalCocycleKernel

def integralScalarCocycleInclusion :
    IntegralScalarCocycleCarrier →ₗ[ℤ] ScalarVertex :=
  TensorProduct.map LinearMap.id integralCocycleSubtype

theorem integralScalarCocycleInclusion_differential_zero
    (value : IntegralScalarCocycleCarrier) :
    extendedDifferential (integralScalarCocycleInclusion value) = 0 := by
  induction value using TensorProduct.induction_on with
  | zero => simp
  | tmul coefficient integral =>
      simp only [integralScalarCocycleInclusion, extendedDifferential,
        TensorProduct.map_tmul, LinearMap.id_apply, integralCocycleSubtype]
      change coefficient ⊗ₜ[ℤ] globalDifferential integral.1 = 0
      rw [LinearMap.mem_ker.mp integral.2, TensorProduct.tmul_zero]
  | add left right left_ih right_ih =>
      simp only [map_add, left_ih, right_ih, add_zero]

theorem integralScalarTautologicalAntiInvariant_eq_zero
    (stage : Nat) (value : IntegralScalarCocycleCarrier) :
    localWholeAntiInvariantComponent stage
        (localTensorRestriction stage
          (integralScalarCocycleInclusion value)) = 0 := by
  induction value using TensorProduct.induction_on with
  | zero => simp
  | tmul coefficient integral =>
      simp only [integralScalarCocycleInclusion,
        localTensorRestriction, localWholeAntiInvariantComponent,
        TensorProduct.map_tmul, LinearMap.id_apply, integralCocycleSubtype]
      change
        (coefficientRestriction stage coefficient) ⊗ₜ[ℤ]
          localIntegralWholeAntiInvariant stage integral = 0
      rw [everyLocalIntegralWholeAntiInvariant_eq_zero,
        TensorProduct.tmul_zero]
  | add left right left_ih right_ih =>
      simp only [map_add, left_ih, right_ih, add_zero]

theorem localIntegralScalarTautologicalReadback_eq_zero
    (stage : Nat) (value : IntegralScalarCocycleCarrier) :
    localTautologicalAntiInvariantReadback stage
        (integralScalarCocycleInclusion value)
        (integralScalarCocycleInclusion_differential_zero value) = 0 := by
  rw [localTautologicalAntiInvariantReadback_eq_component,
    integralScalarTautologicalAntiInvariant_eq_zero stage value]
  simp

end
end CanonicalUnitArithmeticIntegralActionCofiberCofinalRigidity
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
