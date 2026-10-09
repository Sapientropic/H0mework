import H0mework.Versions.V2.Arithmetic.FockUnitAction.Inventory.SourceSelected.Calculation.Cursor.Source
import H0mework.Versions.R2.Realization.Operations.RuntimeCharacter
import H0mework.Versions.V2.Realization.Operations.Fibre.Recovery
import H0mework.Realization.Operations.ScalarComplex

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalArithmeticState.GoldbachUnitSelectedActor.Calculation.Cursor.Consumer

open NoIslandNoMagic.CanonicalArithmeticState.GoldbachUnitSelectedActor.Calculation.Cursor.Source

noncomputable section

abbrev Formal (depth : Nat) := SourceOperationRuntime.FormalCarrier ℤ (Cursor.Source.Value depth) Var Unit.unit

def actorRestriction (depth : Nat) : Material depth →ₗ[ℤ] ActorWord depth :=
  Finsupp.lcomapDomain Option.some (Option.some_injective (Registered.Point depth))

theorem actorRestriction_someLift (depth : Nat) (word : ActorWord depth) :
    actorRestriction depth (someLift depth word) = word :=
  Finsupp.leftInverse_lcomapDomain_mapDomain Option.some (Option.some_injective (Registered.Point depth)) word

/-- The complete syntax-derived material feeds the existing cofinal character. -/
def sourceField (depth : Nat) :=
  SourceOperationRuntime.Character.sourceMap (R := ℤ) (s := Unit.unit)
    (readMaterial depth) (environment depth) (mathTail depth)

def sourceMorphism (depth : Nat) :=
  SourceOperationRuntime.Fibre.actualMorphism (R := ℤ) (s := Unit.unit)
    (readMaterial depth) (environment depth) (mathTail depth)

def sourceRecovery (depth : Nat) :=
  SourceOperationRuntime.Fibre.recover (R := ℤ) (s := Unit.unit)
    (readMaterial depth) (environment depth) (mathTail depth)

abbrev sourceLogic (depth : Nat) :=
  SourceOperationLogic.Scope (SourceOperationRuntime.Fibre.evaluation (R := ℤ) (s := Unit.unit)
    (readMaterial depth) (environment depth) (mathTail depth))

def sourceLogicalFibres (depth : Nat) :=
  SourceOperationLogic.fibreDecomposition
    (SourceOperationRuntime.Fibre.evaluation (R := ℤ) (s := Unit.unit)
      (readMaterial depth) (environment depth) (mathTail depth))

def sourceCochain (depth : Nat) :=
  SourceOperationScalarCochain.cochain (R := ℤ) (s := Unit.unit)
    (SourceOperationRuntime.oldEnvironment (readMaterial depth) (environment depth)
      (SourceGeneratedRuntimeMaterialStageAt.generate (mathTail depth)))
    (SourceOperationRuntime.incrementEnvironment (readMaterial depth) (environment depth)
      (SourceGeneratedRuntimeMaterialStageAt.generate (mathTail depth)))

/-- Character coordinates are the inventories of the actual generated stages. -/
theorem field_reads_actual (depth bound : Nat) (word : Formal depth) (stage : Fin (bound + 1)) :
    SourceOperationRuntime.Character.stageRead (readMaterial depth) (environment depth) (mathTail depth) bound
        (sourceField depth word) stage =
      SourceOperationRuntime.stageInventory (readMaterial depth) (environment depth)
        ((SourceOperationRuntime.materialHistory (mathTail depth) bound).stageAt stage) word :=
  SourceOperationRuntime.Character.source_reads_actual_stage
    (R := ℤ) (s := Unit.unit) (readMaterial depth) (environment depth) (mathTail depth) bound word stage

theorem first_stage_actual (depth : Nat) :
    SourceOperationRuntime.Fibre.firstStage (R := ℤ) (s := Unit.unit)
        (readMaterial depth) (environment depth) (mathTail depth) =
      SourceOperationScalarRelations.updateInventory (R := ℤ) (s := Unit.unit)
        (SourceOperationRuntime.oldEnvironment (readMaterial depth) (environment depth)
          (SourceGeneratedRuntimeMaterialStageAt.generate (mathTail depth)))
        (liftEnvironment depth (Registered.actualIncrement depth)) := by
  unfold SourceOperationRuntime.Fibre.firstStage SourceOperationRuntime.stageInventory
  rw [first_pulse_increment]

/-- Existing reverse-lifting recovery retains both old and effect coordinates. -/
theorem inverse_receipt (depth : Nat) :
    Function.Injective (sourceRecovery depth) ∧
    ∀ residual : SourceOperationLogic.FibreLift.LiftingResidual (sourceMorphism depth),
      (sourceRecovery depth residual).1 + (sourceRecovery depth residual).2 = 0 :=
  ⟨SourceOperationRuntime.Fibre.recover_injective (R := ℤ) (s := Unit.unit)
    (readMaterial depth) (environment depth) (mathTail depth),
   SourceOperationRuntime.Fibre.recover_balanced (R := ℤ) (s := Unit.unit)
    (readMaterial depth) (environment depth) (mathTail depth)⟩

/-- The cochain consumes the same literal actor increment as the inverse fibre. -/
theorem cochain_actual (depth : Nat) :
    sourceCochain depth = SourceOperationScalarCochain.cochain (R := ℤ) (s := Unit.unit)
      (SourceOperationRuntime.oldEnvironment (readMaterial depth) (environment depth)
        (SourceGeneratedRuntimeMaterialStageAt.generate (mathTail depth)))
      (liftEnvironment depth (Registered.actualIncrement depth)) := by
  unfold sourceCochain
  rw [first_pulse_increment]

theorem field_next (depth : Nat) (word : Formal depth) :
    SourceOperationRuntime.Character.successor (readMaterial depth) (environment depth) (mathTail depth)
        (sourceField depth word) =
      SourceOperationRuntime.Character.sourceMap (readMaterial depth) (environment depth)
        (mathTail depth).tick.next word :=
  SourceOperationRuntime.Character.successor_source (R := ℤ) (s := Unit.unit)
    (readMaterial depth) (environment depth) (mathTail depth) word

end
end NoIslandNoMagic.CanonicalArithmeticState.GoldbachUnitSelectedActor.Calculation.Cursor.Consumer
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
