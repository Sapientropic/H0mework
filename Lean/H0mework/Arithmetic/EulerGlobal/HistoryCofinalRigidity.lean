import H0mework.Arithmetic.EulerGlobal.WholeHistory
import H0mework.Realization.GlobalSections.CofinalPrimeRigidity

/-!
# Cofinal rigidity of the common whole-history solution

The actual finite solution carriers form one inverse diagram under the
source-generated forgetful restriction.  The frozen dependent-global-state
engine creates the common integral solution.  Its one whole dual difference
is independent of stage, while every framework-scheduled prime power is read
from one actual factor row at a sufficiently late runtime occurrence.

The domain supplies only that row.  The frozen cofinal quotient/rigidity
consumer generates the schedule, division roots, all-prime closure, residual
zero, and the final vanishing of the common whole difference.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace CanonicalUnitArithmeticFactorizationWholeHistorySolutionCofinalRigidity

open CanonicalUnitArithmeticFactorizationOccurrence
open CanonicalUnitArithmeticFactorizationEulerDependentDiagram
open CanonicalUnitArithmeticFactorizationWholeHistorySolutionCarrier
open CofinalPrimePowerRestrictionRigidity
open CofinalPrimePowerRestrictionRigidity.RootGeneratedCofinalPrimePowerRestrictionHistoryAt
open DependentDerivedGlobalState
open DependentDerivedGlobalState.RootGeneratedDependentDerivedGlobalStateAt
open DerivedAdicCofiber
open CategoryTheory
open CategoryTheory.Limits

noncomputable section

abbrev ZeroCarrier := Fin 0 → ℤ

noncomputable abbrev ActualComplex (seed : FactorizationPayload) (stage : Nat) :
    IntegralCochainComplex ℤ where
  X degree := if degree = 0 then
    ModuleCat.of ℤ (Carrier seed stage)
  else
    ModuleCat.of ℤ ZeroCarrier
  d _source _target := 0

noncomputable def actualRestriction (seed : FactorizationPayload) (stage : Nat) :
    ActualComplex seed (stage + 1) ⟶ ActualComplex seed stage where
  f degree := by
    by_cases degreeZero : degree = 0
    · subst degree
      exact ModuleCat.ofHom (carrierRestriction seed stage)
    · exact 0
  comm' _source _target _relation := by
    change _ ≫ (0 : _ ⟶ _) = (0 : _ ⟶ _) ≫ _
    rw [Limits.comp_zero, Limits.zero_comp]

noncomputable def solutionDiagram (seed : FactorizationPayload) :
    ℕᵒᵖ ⥤ IntegralCochainComplex ℤ :=
  Functor.ofOpSequence
    (X := fun stage => ActualComplex seed stage)
    (actualRestriction seed)

def dependentOccurrence : RootedAccountedUnfolding
    (FactorizationPayload × (ℕᵒᵖ ⥤ IntegralCochainComplex ℤ)) :=
  seedOccurrence.map fun seed => (seed, solutionDiagram seed)

def globalFace : RootGeneratedDependentDerivedGlobalStateAt dependentOccurrence :=
  RootGeneratedDependentDerivedGlobalStateAt.generate

abbrev GlobalState : IntegralCochainComplex ℤ :=
  globalFace.globalState

abbrev GlobalCarrier := (GlobalState.X 0 : Type)

noncomputable def globalRestriction (stage : ℕᵒᵖ) :
    GlobalState ⟶ globalFace.actualDiagram.obj stage :=
  globalFace.restriction stage

def localValue (stage : Nat) : GlobalCarrier →ₗ[ℤ]
    Carrier seedOccurrence.root stage :=
  (globalRestriction (Opposite.op stage)).f 0 |>.hom

noncomputable abbrev DiagonalUnitComplex : IntegralCochainComplex ℤ :=
  (CochainComplex.singleFunctor (ModuleCat ℤ) 0).obj (ModuleCat.of ℤ ℤ)

noncomputable def diagonalUnitMap (seed : FactorizationPayload) (stage : Nat) :
    DiagonalUnitComplex ⟶ ActualComplex seed stage where
  f degree := by
    by_cases degreeZero : degree = 0
    · subst degree
      exact ModuleCat.ofHom
        (LinearMap.toSpanSingleton ℤ (Carrier seed stage)
          (diagonalUnit seed stage))
    · exact 0
  comm' source target related := by
    change source + 1 = target at related
    subst target
    change _ ≫ (0 : _ ⟶ _) = (0 : _ ⟶ _) ≫ _
    rw [comp_zero, zero_comp]

theorem diagonalUnitMap_successor (seed : FactorizationPayload) (stage : Nat) :
    diagonalUnitMap seed (stage + 1) ≫ actualRestriction seed stage =
      diagonalUnitMap seed stage := by
  ext degree value
  by_cases degreeZero : degree = 0
  · subst degree
    change carrierRestriction seed stage
        (value • diagonalUnit seed (stage + 1)) =
      value • diagonalUnit seed stage
    rw [map_smul, carrierRestriction_diagonalUnit]
  · let targetSubsingleton : Subsingleton
        ((ActualComplex seed stage).X degree) := by
      dsimp only [ActualComplex]
      rw [if_neg degreeZero]
      infer_instance
    exact @Subsingleton.elim _ targetSubsingleton _ _

noncomputable def diagonalUnitCone (seed : FactorizationPayload) :
    Cone (solutionDiagram seed) where
  pt := DiagonalUnitComplex
  π := NatTrans.ofOpSequence (diagonalUnitMap seed) (fun stage => by
    simp only [Functor.const_obj_map, solutionDiagram,
      Functor.ofOpSequence_map_homOfLE_succ]
    simpa using (diagonalUnitMap_successor seed stage).symm)

noncomputable def globalDiagonalUnitMap :
    DiagonalUnitComplex ⟶ GlobalState :=
  limit.lift _ (diagonalUnitCone seedOccurrence.root)

def diagonalUnitSource : (DiagonalUnitComplex.X 0 : Type) := by
  change ℤ
  exact 1

/-- Compatible `w₀=w₁=1,q=0` family as one actual global carrier element. -/
noncomputable def globalDiagonalUnit : GlobalCarrier :=
  (globalDiagonalUnitMap.f 0).hom diagonalUnitSource

theorem globalDiagonalUnit_restriction_raw (stage : Nat) :
    ((limit.π (solutionDiagram seedOccurrence.root)
        (Opposite.op stage)).f 0).hom
        ((globalDiagonalUnitMap.f 0).hom diagonalUnitSource) =
      ((diagonalUnitMap seedOccurrence.root stage).f 0).hom
        diagonalUnitSource := by
  have restriction := congrArg
    (fun arrow : DiagonalUnitComplex ⟶
        (solutionDiagram seedOccurrence.root).obj (Opposite.op stage) =>
      (arrow.f 0).hom diagonalUnitSource)
    (limit.lift_π (diagonalUnitCone seedOccurrence.root)
      (Opposite.op stage))
  change
    ((limit.π (solutionDiagram seedOccurrence.root)
        (Opposite.op stage)).f 0).hom
        (((limit.lift (solutionDiagram seedOccurrence.root)
          (diagonalUnitCone seedOccurrence.root)).f 0).hom
            diagonalUnitSource) =
      ((diagonalUnitMap seedOccurrence.root stage).f 0).hom
        diagonalUnitSource at restriction
  exact restriction

theorem localValue_globalDiagonalUnit (stage : Nat) :
    localValue stage globalDiagonalUnit =
      diagonalUnit seedOccurrence.root stage := by
  change
    ((limit.π (solutionDiagram seedOccurrence.root)
        (Opposite.op stage)).f 0).hom
        ((globalDiagonalUnitMap.f 0).hom diagonalUnitSource) = _
  rw [globalDiagonalUnit_restriction_raw]
  change (1 : ℤ) • diagonalUnit seedOccurrence.root stage = _
  simp

@[simp] theorem globalDiagonalUnit_wholeCoordinate
    (stage : Nat) (dualIndex : Fin 2) :
    wholeCoordinate seedOccurrence.root stage dualIndex
        (localValue stage globalDiagonalUnit) = 1 := by
  rw [localValue_globalDiagonalUnit, diagonalUnit_wholeCoordinate]

@[simp] theorem globalDiagonalUnit_quotientCoordinate
    (stage : Nat) (row : FactorRow seedOccurrence.root stage) :
    quotientCoordinate row (localValue stage globalDiagonalUnit) = 0 := by
  rw [localValue_globalDiagonalUnit, diagonalUnit_quotientCoordinate]

theorem globalDiagonalUnit_ne_zero : globalDiagonalUnit ≠ 0 := by
  intro diagonalZero
  have coordinateOne := globalDiagonalUnit_wholeCoordinate 0 0
  rw [diagonalZero, map_zero, map_zero] at coordinateOne
  norm_num at coordinateOne

def successorArrow (stage : Nat) :
    (Opposite.op (stage + 1) : ℕᵒᵖ) ⟶ Opposite.op stage :=
  (homOfLE (Nat.le_succ stage)).op

theorem actualDiagram_map_successor (stage : Nat) :
    globalFace.actualDiagram.map (successorArrow stage) =
      actualRestriction seedOccurrence.root stage := by
  change (solutionDiagram seedOccurrence.root).map (successorArrow stage) = _
  simp only [solutionDiagram, successorArrow,
    Functor.ofOpSequence_map_homOfLE_succ]

theorem localValue_successor (stage : Nat) (value : GlobalCarrier) :
    carrierRestriction seedOccurrence.root stage
        (localValue (stage + 1) value) =
      localValue stage value := by
  have coneSquare := globalFace.restriction_naturality (successorArrow stage)
  rw [actualDiagram_map_successor] at coneSquare
  have degreeZero := congrArg
    (fun arrow : GlobalState ⟶
        (solutionDiagram seedOccurrence.root).obj (Opposite.op stage) =>
      (arrow.f 0).hom value)
    coneSquare
  change carrierRestriction seedOccurrence.root stage
      (localValue (stage + 1) value) = localValue stage value
  change carrierRestriction seedOccurrence.root stage
      ((globalRestriction (Opposite.op (stage + 1))).f 0 value) =
    (globalRestriction (Opposite.op stage)).f 0 value at degreeZero
  exact degreeZero

def localWholeDifference (stage : Nat) (value : GlobalCarrier) : ℤ :=
  wholeCoordinate seedOccurrence.root stage 0 (localValue stage value) -
    wholeCoordinate seedOccurrence.root stage 1 (localValue stage value)

theorem localWholeDifference_successor (stage : Nat)
    (value : GlobalCarrier) :
    localWholeDifference (stage + 1) value =
      localWholeDifference stage value := by
  unfold localWholeDifference
  rw [← carrierRestriction_wholeCoordinate seedOccurrence.root stage 0,
    ← carrierRestriction_wholeCoordinate seedOccurrence.root stage 1,
    localValue_successor]

def globalWholeDifference (value : GlobalCarrier) : ℤ :=
  localWholeDifference 0 value

theorem localWholeDifference_eq_global (value : GlobalCarrier) :
    ∀ stage, localWholeDifference stage value = globalWholeDifference value
  | 0 => rfl
  | stage + 1 =>
      (localWholeDifference_successor stage value).trans
        (localWholeDifference_eq_global value stage)

theorem stageHistory_eq_runtimeWholeHistory (stage : Nat) :
    StageHistory seedOccurrence.root stage = runtimeWholeHistory stage := by
  cases stage with
  | zero => rfl
  | succ stage => rfl

theorem castPrimeIndex_value
    {left right : ArithmeticGeneration.UnitHistory}
    (historyEquality : left = right) (index : PrimeIndex left) :
    (_root_.cast (congrArg PrimeIndex historyEquality) index :
      PrimeIndex right).1 = index.1 := by
  subst right
  rfl

def stagePrimeIndex
    {requestedPrime : Nat.Primes} {requestedExponent : Nat}
    (factor : RuntimePrimePowerFactorAt requestedPrime requestedExponent) :
    StagePrime seedOccurrence.root factor.stage := by
  exact _root_.cast
    (congrArg PrimeIndex
      (stageHistory_eq_runtimeWholeHistory factor.stage).symm)
    factor.primeIndex

@[simp] theorem stagePrimeIndex_value
    {requestedPrime : Nat.Primes} {requestedExponent : Nat}
    (factor : RuntimePrimePowerFactorAt requestedPrime requestedExponent) :
    (stagePrimeIndex factor).1 = factor.primeIndex.1 := by
  unfold stagePrimeIndex
  exact castPrimeIndex_value
    (stageHistory_eq_runtimeWholeHistory factor.stage).symm factor.primeIndex

theorem stagePrimeIndex_multiplicity
    {requestedPrime : Nat.Primes} {requestedExponent : Nat}
    (factor : RuntimePrimePowerFactorAt requestedPrime requestedExponent) :
    CanonicalUnitArithmeticFactorizationOccurrence.multiplicity
        (StageHistory seedOccurrence.root factor.stage)
        (stagePrimeIndex factor) =
      CanonicalUnitArithmeticFactorizationOccurrence.multiplicity
        (runtimeWholeHistory factor.stage) factor.primeIndex := by
  unfold CanonicalUnitArithmeticFactorizationOccurrence.multiplicity
  rw [stagePrimeIndex_value, stageHistory_eq_runtimeWholeHistory]

def stageFactorExponent
    {requestedPrime : Nat.Primes} {requestedExponent : Nat}
    (factor : RuntimePrimePowerFactorAt requestedPrime requestedExponent) :
    FactorExponent seedOccurrence.root factor.stage (stagePrimeIndex factor) := by
  refine ⟨factor.exponentIndex.1, ?_⟩
  rw [stagePrimeIndex_multiplicity]
  exact factor.exponentIndex.2

def stageFactorRow
    {requestedPrime : Nat.Primes} {requestedExponent : Nat}
    (factor : RuntimePrimePowerFactorAt requestedPrime requestedExponent) :
    FactorRow seedOccurrence.root factor.stage :=
  ⟨stagePrimeIndex factor, stageFactorExponent factor⟩

theorem stageFactorRow_prime
    {requestedPrime : Nat.Primes} {requestedExponent : Nat}
    (factor : RuntimePrimePowerFactorAt requestedPrime requestedExponent) :
    rowPrime (stageFactorRow factor) = requestedPrime := by
  apply Subtype.ext
  change (stagePrimeIndex factor).1 = requestedPrime.1
  rw [stagePrimeIndex_value]
  exact congrArg Subtype.val factor.prime_eq

theorem stageFactorRow_exponent
    {requestedPrime : Nat.Primes} {requestedExponent : Nat}
    (factor : RuntimePrimePowerFactorAt requestedPrime requestedExponent) :
    rowExponent (stageFactorRow factor) = requestedExponent := by
  change factor.exponentIndex.1 + 1 = requestedExponent
  exact factor.exponent_eq

def localQuotientDifference
    {requestedPrime : Nat.Primes} {requestedExponent : Nat}
    (factor : RuntimePrimePowerFactorAt requestedPrime requestedExponent)
    (value : GlobalCarrier) : ℤ :=
  quotientCoordinate (stageFactorRow factor)
    (localValue factor.stage value)

theorem localWholeDifference_factor_landing
    {requestedPrime : Nat.Primes} {requestedExponent : Nat}
    (factor : RuntimePrimePowerFactorAt requestedPrime requestedExponent)
    (value : GlobalCarrier) :
    localWholeDifference factor.stage value =
      (requestedPrime : Nat) ^ requestedExponent •
        localQuotientDifference factor value := by
  have landing := wholeDifference_eq_primePower_mul_quotientCoordinate
    seedOccurrence.root factor.stage (stageFactorRow factor)
      (localValue factor.stage value)
  unfold localWholeDifference localQuotientDifference
  change
    wholeCoordinate seedOccurrence.root factor.stage 0
          (localValue factor.stage value) -
        wholeCoordinate seedOccurrence.root factor.stage 1
          (localValue factor.stage value) = _
  change
    wholeCoordinate seedOccurrence.root factor.stage 0
          (localValue factor.stage value) -
        wholeCoordinate seedOccurrence.root factor.stage 1
          (localValue factor.stage value) =
      ((rowPrime (stageFactorRow factor) : Nat) : ℤ) ^
          rowExponent (stageFactorRow factor) *
        quotientCoordinate (stageFactorRow factor)
          (localValue factor.stage value) at landing
  rw [stageFactorRow_prime, stageFactorRow_exponent] at landing
  exact landing

theorem globalWholeDifference_factor_landing
    {requestedPrime : Nat.Primes} {requestedExponent : Nat}
    (factor : RuntimePrimePowerFactorAt requestedPrime requestedExponent)
    (value : GlobalCarrier) :
    globalWholeDifference value =
      (requestedPrime : Nat) ^ requestedExponent •
        localQuotientDifference factor value := by
  rw [← localWholeDifference_eq_global value factor.stage]
  exact localWholeDifference_factor_landing factor value

def localProcess (value : GlobalCarrier) :
    PrimePowerRestrictionLocalProcessAt Nat where
  cursor state := state
  Carrier _state := AddCommGrpCat.of ℤ
  component _state := globalWholeDifference value
  finiteGenerated _state := Module.Finite.iff_addGroup_fg.mp inferInstance
  quotientZero state := by
    let factor := RuntimePrimePowerFactorAt.generate
      (scheduledPrime state) (scheduledExponent state)
        (scheduledExponent_positive state)
    have landing := globalWholeDifference_factor_landing factor value
    apply (QuotientAddGroup.eq_zero_iff (globalWholeDifference value)).2
    refine ⟨localQuotientDifference factor value, ?_⟩
    exact landing.symm
  next state := state + 1
  cursor_next _state := rfl
  restriction _state := AddMonoidHom.id ℤ
  component_next _state := rfl

def processSeedOccurrence (_value : GlobalCarrier) :
    RootedAccountedUnfolding (FactorizationPayload × Nat) :=
  seedOccurrence.map fun root => (root, 0)

def processOccurrence (value : GlobalCarrier) : RootedAccountedUnfolding
    (FactorizationPayload × PrimePowerRestrictionLocalProcessAt Nat) :=
  seedOccurrence.map fun root => (root, localProcess value)

theorem process_projects (value : GlobalCarrier) :
    (processOccurrence value).map Prod.fst =
      (processSeedOccurrence value).map Prod.fst := by
  unfold processOccurrence processSeedOccurrence
  rw [RootedAccountedUnfolding.map_map,
    RootedAccountedUnfolding.map_map]
  change seedOccurrence.map id = seedOccurrence.map id
  rfl

theorem process_seed_cursor (value : GlobalCarrier) :
    (processOccurrence value).root.2.cursor
      (processSeedOccurrence value).root.2 = 0 := by
  rfl

def historyFace (value : GlobalCarrier) :
    RootGeneratedCofinalPrimePowerRestrictionHistoryAt
      (processSeedOccurrence value) (processOccurrence value)
        (process_projects value) (process_seed_cursor value) :=
  RootGeneratedCofinalPrimePowerRestrictionHistoryAt.generate

/-- Frozen all-prime rigidity kills the one whole dual difference of every
framework-generated global integral solution. -/
theorem globalWholeDifference_eq_zero (value : GlobalCarrier) :
    globalWholeDifference value = 0 := by
  exact (historyFace value).generatedSeedComponent_eq_zero

theorem everyLocalWholeDifference_eq_zero (stage : Nat)
    (value : GlobalCarrier) :
    localWholeDifference stage value = 0 := by
  rw [localWholeDifference_eq_global, globalWholeDifference_eq_zero]

theorem preserves_exact_root_and_frozen_rigidity (value : GlobalCarrier) :
    globalFace.root = seedOccurrence ∧
      (historyFace value).root = seedOccurrence ∧
      globalWholeDifference value = 0 := by
  refine ⟨rfl, ?_, globalWholeDifference_eq_zero value⟩
  unfold RootGeneratedCofinalPrimePowerRestrictionHistoryAt.root
    processSeedOccurrence
  rw [RootedAccountedUnfolding.map_map]
  change seedOccurrence.map id = seedOccurrence
  exact RootedAccountedUnfolding.map_id _

end
end CanonicalUnitArithmeticFactorizationWholeHistorySolutionCofinalRigidity
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
