import H0mework.Realization.ScalarCofinal.RootOccurrence
import H0mework.Versions.Y.Arithmetic.RiemannGraph.History.PrimePower.Factorization.Responsibility.Source.LivingLawCanonicalRiemannZeroOwnedPrimeExponentPoleReceiptRelation

/-!
# Zero-owned cofinal completion of all receipt roles

The complete cursor-indexed retained/energy/vertical table is generated from
one zero-owned all-prime occurrence.  Its finite prefixes form the actual
evaluator tower, truncation is the successor map, and the scalar cofinal
engine generates the inverse-limit completion.  No compatible family is an
input: the source table itself enters through the generated completion map.
-/

set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.AllPlace.WeilQuadratic.Runtime
namespace MuntzGraph.Conductor.History.PrimePowerCurrent.ReceiptRelation.Cofinal

open CategoryTheory
open ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
open PrimePower.Occurrence
open RootGeneratedCanonicalUnitArithmeticPrimePowerCofinalClosure
open SourceGeneratedScalarCofinalKernelCompletion
open SourceGeneratedScalarCofinalRootOccurrence
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.AllPlace.WeilQuadratic.Occurrence
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.AllPlace.WeilQuadratic.Runtime.MuntzGraph.Conductor.History.PrimePowerCurrent.ReceiptRelation.Source

noncomputable section

abbrev ReceiptTable := Nat → PrimeExponentPoleReceiptRole → QRich.ClozelJPair

abbrev ReceiptPrefix (stage : Nat) :=
  Fin (stage + 1) → PrimeExponentPoleReceiptRole → QRich.ClozelJPair

def tableEvaluator (stage : Nat) : ReceiptTable →ₗ[ℂ] ReceiptPrefix stage where
  toFun := fun table index role => table index.1 role
  map_add' := by intros; rfl
  map_smul' := by intros; rfl

def prefixTransition (stage : Nat) :
    ReceiptPrefix (stage + 1) →ₗ[ℂ] ReceiptPrefix stage where
  toFun := fun high index role => high index.castSucc role
  map_add' := by intros; rfl
  map_smul' := by intros; rfl

def receiptCofinalData : Data (R := ℂ) (Generator := ReceiptTable)
    (Carrier := ReceiptPrefix) where
  evaluator := tableEvaluator
  transition := prefixTransition

theorem receiptCofinalData_compatible : receiptCofinalData.Compatible := by
  intro stage
  rfl

theorem receiptCofinalData_separated : receiptCofinalData.KernelSeparated := by
  intro table vanishes
  funext cursor role
  have atCursor := vanishes cursor
  have atIndex := congrFun atCursor ⟨cursor, Nat.lt_succ_self cursor⟩
  exact congrFun atIndex role

def sourceReceiptTable
    {observation : GeneratedRiemannZeroObservation}
    {nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)}
    (source : ZeroOwnedAllPrimeWeilQuadraticPayload observation nontrivial) :
    ReceiptTable := fun cursor role =>
  zeroOwnedReceiptRoleValue
    ⟨source, generateZeroOwnedPrimePowerWeilBoundaryFace
      observation nontrivial (scheduledPrime cursor)
        (scheduledExponent cursor) (scheduledExponent_positive cursor) source⟩ role

theorem sourceReceiptTable_root
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (cursor : Nat) (role : PrimeExponentPoleReceiptRole) :
    sourceReceiptTable
        (zeroOwnedAllPrimeWeilQuadraticOccurrence observation nontrivial).root
        cursor role =
      receiptRoleValue observation nontrivial cursor role := by
  change zeroOwnedReceiptRoleValue
      (zeroOwnedPrimePowerWeilBoundaryOccurrence observation nontrivial
        (scheduledPrime cursor) (scheduledExponent cursor)
          (scheduledExponent_positive cursor)).root role = _
  cases role
  · exact zeroOwnedReceiptRawBoundary_root observation nontrivial
      (scheduledPrime cursor) (scheduledExponent cursor)
        (scheduledExponent_positive cursor)
  · exact zeroOwnedReceiptRieszEnergy_root observation nontrivial
      (scheduledPrime cursor) (scheduledExponent cursor)
        (scheduledExponent_positive cursor)
  · exact zeroOwnedReceiptVerticalTrace_root observation nontrivial
      (scheduledPrime cursor) (scheduledExponent cursor)
        (scheduledExponent_positive cursor)

structure GeneratedReceiptTableAt
    {observation : GeneratedRiemannZeroObservation}
    {nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)}
    (source : ZeroOwnedAllPrimeWeilQuadraticPayload observation nontrivial) where
  private mk ::
  table : ReceiptTable
  table_eq : table = sourceReceiptTable source

def generateReceiptTable
    {observation : GeneratedRiemannZeroObservation}
    {nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)}
    (source : ZeroOwnedAllPrimeWeilQuadraticPayload observation nontrivial) :
    GeneratedReceiptTableAt source :=
  ⟨sourceReceiptTable source, rfl⟩

abbrev ReceiptTablePayload
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :=
  Σ source : ZeroOwnedAllPrimeWeilQuadraticPayload observation nontrivial,
    GeneratedReceiptTableAt source

def receiptCofinalOccurrence
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    RootedAccountedUnfolding
      (ReceiptTablePayload observation nontrivial ×
        Data (R := ℂ) (Generator := ReceiptTable) (Carrier := ReceiptPrefix)) :=
  (zeroOwnedAllPrimeWeilQuadraticOccurrence observation nontrivial).map
    fun source => (⟨source, generateReceiptTable source⟩, receiptCofinalData)

def receiptCofinalFace
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    Face (receiptCofinalOccurrence observation nontrivial) :=
  Face.generate

theorem receiptCofinalCalculation
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    Face.GeneratedCompatibilityCalculationAt
      (receiptCofinalFace observation nontrivial) :=
  Face.generateCompatibility _ receiptCofinalData_compatible

def prefixCoordinate (stage : Nat) (role : PrimeExponentPoleReceiptRole) :
    ReceiptPrefix stage →ₗ[ℂ] QRich.ClozelJPair where
  toFun := fun value => value ⟨stage, Nat.lt_succ_self stage⟩ role
  map_add' := by intros; rfl
  map_smul' := by intros; rfl

def completionCoordinate
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (cursor : Nat) (role : PrimeExponentPoleReceiptRole) :
    (receiptCofinalFace observation nontrivial).completion
        (receiptCofinalCalculation observation nontrivial) →ₗ[ℂ]
      QRich.ClozelJPair :=
  (prefixCoordinate cursor role).comp
    (((receiptCofinalFace observation nontrivial).data.stageRealization cursor).comp
      ((receiptCofinalFace observation nontrivial).restriction
        (receiptCofinalCalculation observation nontrivial) cursor).hom)

def completionToTable
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    (receiptCofinalFace observation nontrivial).completion
        (receiptCofinalCalculation observation nontrivial) →ₗ[ℂ]
      ReceiptTable where
  toFun := fun completed cursor role =>
    completionCoordinate observation nontrivial cursor role completed
  map_add' := by
    intro left right
    funext cursor role
    exact (completionCoordinate observation nontrivial cursor role).map_add left right
  map_smul' := by
    intro scalar value
    funext cursor role
    exact (completionCoordinate observation nontrivial cursor role).map_smul scalar value

theorem completionToTable_source
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (table : ReceiptTable) :
    completionToTable observation nontrivial
        ((receiptCofinalFace observation nontrivial).completionMap
          (receiptCofinalCalculation observation nontrivial) table) = table := by
  funext cursor role
  have readback := ConcreteCategory.congr_hom
    ((receiptCofinalFace observation nontrivial).source_to_evaluator
      (receiptCofinalCalculation observation nontrivial) cursor) table
  change
    ((receiptCofinalFace observation nontrivial).data.stageRealization cursor)
        (((receiptCofinalFace observation nontrivial).restriction
          (receiptCofinalCalculation observation nontrivial) cursor).hom
            ((receiptCofinalFace observation nontrivial).completionMap
              (receiptCofinalCalculation observation nontrivial) table)) =
      tableEvaluator cursor table at readback
  change
    (((receiptCofinalFace observation nontrivial).data.stageRealization cursor)
        (((receiptCofinalFace observation nontrivial).restriction
          (receiptCofinalCalculation observation nontrivial) cursor).hom
            ((receiptCofinalFace observation nontrivial).completionMap
              (receiptCofinalCalculation observation nontrivial) table)))
        ⟨cursor, Nat.lt_succ_self cursor⟩ role = table cursor role
  exact congrFun (congrFun readback ⟨cursor, Nat.lt_succ_self cursor⟩) role

theorem receiptCofinalFace_projects_allPrime
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    (receiptCofinalFace observation nontrivial).root.map Sigma.fst =
      zeroOwnedAllPrimeWeilQuadraticOccurrence observation nontrivial := by
  unfold receiptCofinalFace Face.root receiptCofinalOccurrence
  rw [RootedAccountedUnfolding.map_map,
    RootedAccountedUnfolding.map_map]
  change (zeroOwnedAllPrimeWeilQuadraticOccurrence observation nontrivial).map id = _
  exact RootedAccountedUnfolding.map_id _

theorem receiptCofinalFace_root_table
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (cursor : Nat) (role : PrimeExponentPoleReceiptRole) :
    (receiptCofinalFace observation nontrivial).root.root.2.table cursor role =
      receiptRoleValue observation nontrivial cursor role := by
  change sourceReceiptTable
      (zeroOwnedAllPrimeWeilQuadraticOccurrence observation nontrivial).root
        cursor role = _
  exact sourceReceiptTable_root observation nontrivial cursor role

theorem receiptCofinalFace_root_relation
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (cursor : Nat) :
    (receiptCofinalFace observation nontrivial).root.root.2.table
        cursor .retained =
      (receiptCofinalFace observation nontrivial).root.root.2.table
          cursor .energy +
        (receiptCofinalFace observation nontrivial).root.root.2.table
          cursor .vertical := by
  rw [receiptCofinalFace_root_table, receiptCofinalFace_root_table,
    receiptCofinalFace_root_table]
  change pairedPrimeExponentPoleBoundaryMellin observation nontrivial
      (scheduledConductorPrimePowerIndex cursor) =
    pairedPrimeExponentPoleBoundaryRieszEnergy observation nontrivial
        (scheduledConductorPrimePowerIndex cursor) +
      pairedPrimeExponentPoleBoundaryVerticalTrace observation nontrivial
        (scheduledConductorPrimePowerIndex cursor)
  exact pairedPrimeExponentPoleBoundaryMellin_verticalSplit
    observation nontrivial _

def zeroOwnedReceiptGlobalComponent
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    (receiptCofinalFace observation nontrivial).completion
      (receiptCofinalCalculation observation nontrivial) :=
  (receiptCofinalFace observation nontrivial).completionMap
    (receiptCofinalCalculation observation nontrivial)
      (receiptCofinalFace observation nontrivial).root.root.2.table

theorem zeroOwnedReceiptGlobalComponent_readback
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    completionToTable observation nontrivial
        (zeroOwnedReceiptGlobalComponent observation nontrivial) =
      (receiptCofinalFace observation nontrivial).root.root.2.table :=
  completionToTable_source observation nontrivial _

theorem zeroOwnedReceiptGlobalComponent_relation
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (cursor : Nat) :
    completionToTable observation nontrivial
        (zeroOwnedReceiptGlobalComponent observation nontrivial)
        cursor .retained =
      completionToTable observation nontrivial
          (zeroOwnedReceiptGlobalComponent observation nontrivial)
          cursor .energy +
        completionToTable observation nontrivial
          (zeroOwnedReceiptGlobalComponent observation nontrivial)
          cursor .vertical := by
  rw [zeroOwnedReceiptGlobalComponent_readback]
  exact receiptCofinalFace_root_relation observation nontrivial cursor

end
end MuntzGraph.Conductor.History.PrimePowerCurrent.ReceiptRelation.Cofinal
end NoIslandNoMagic.CanonicalRiemann.AllPlace.WeilQuadratic.Runtime
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
