import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Runtime.StoredTimeline
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalArithmeticState.ParticleWave.Fock.Runtime.Goldbach.Occurrence.Actuality.Dynamics.History.Inventory.SourceSelected.Calculation.Cursor.Stored

set_option autoImplicit false
noncomputable section

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalArithmeticState.GoldbachUnitSelectedActor.Calculation.Cursor.Timeline

open SourceOperationEffects SourceOperationRuntime
open NoIslandNoMagic.CanonicalArithmeticState.GoldbachUnitSelectedActor.Calculation.Cursor.Source
open NoIslandNoMagic.CanonicalArithmeticState.GoldbachUnitSelectedActor.Calculation.Cursor.Stored
open private advance_first from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Runtime.StoredHistory

/-- The original bind and every actor pulse supply a single material table. -/
def fullTable (depth : Nat) : Vector (Material depth) (budget depth+2) :=
  (fullHistory depth).storedTimeline (readMaterial depth)

/-- All actual pulse environments and the independent terminal read share one table. -/
def sourceReadout (depth : Nat) :
    (Fin (budget depth) → Env (Cursor.Source.Value depth) Var × Env (Cursor.Source.Value depth) Var) × Material depth :=
  let table := fullTable depth
  (fun i => timelineEnvironments (environment depth) table i.succ,table.get (Fin.last (budget depth+1)))

theorem source_readout_pulse (depth : Nat) (i : Fin (budget depth)) :
    let stage := SourceGeneratedRuntimeMaterialStageAt.generate ((mathTail depth).advance i.val)
    (sourceReadout depth).1 i =
      (oldEnvironment (readMaterial depth) (environment depth) stage,
        incrementEnvironment (readMaterial depth) (environment depth) stage) := by
  have actual := timeline_environments_actual (environment depth) (readMaterial depth)
    (fullHistory depth) i.succ
  have same : (mathTail depth).advance i.val = (mathSeed depth).advance i.succ.val :=
    advance_first (mathSeed depth) i.val
  dsimp only
  rw [same]
  exact actual

def pulseInventory (depth : Nat) (i : Fin (budget depth)) :
    Consumer.Formal depth →ₗ[ℤ] Material depth × Material depth :=
  timelineInventory (R := ℤ) (s := Unit.unit) (environment depth) (fullTable depth) i.succ

theorem pulse_inventory_actual (depth : Nat) (i : Fin (budget depth)) :
    pulseInventory depth i =
      stageInventory (R := ℤ) (s := Unit.unit) (readMaterial depth) (environment depth)
        (SourceGeneratedRuntimeMaterialStageAt.generate ((mathTail depth).advance i.val)) := by
  have actual := timeline_inventory_actual (R := ℤ) (s := Unit.unit) (environment depth)
    (readMaterial depth) (fullHistory depth) i.succ
  have same : (mathTail depth).advance i.val = (mathSeed depth).advance i.succ.val :=
    advance_first (mathSeed depth) i.val
  rw [same]
  exact actual

/-- The existing cofinal character reads each real pulse from the full bound actor. -/
theorem source_character_from_full (depth bound : Nat) (within : bound < budget depth)
    (word : Consumer.Formal depth) (i : Fin (bound+1)) :
    Character.stageRead (readMaterial depth) (environment depth) (mathTail depth) bound
        (Consumer.sourceField depth word) i =
      pulseInventory depth ⟨i.val, Nat.lt_of_le_of_lt (Nat.le_of_lt_succ i.isLt) within⟩ word := by
  let pulse : Fin (budget depth) := ⟨i.val,Nat.lt_of_le_of_lt (Nat.le_of_lt_succ i.isLt) within⟩
  have paid := congrArg (fun inventory : Consumer.Formal depth →ₗ[ℤ] Material depth × Material depth =>
    inventory word) (pulse_inventory_actual depth pulse)
  exact (Consumer.field_reads_actual depth bound word i).trans paid.symm

/-- The independent disposition receives the terminal cell of the same material table. -/
theorem source_readout_terminal (depth : Nat) : (sourceReadout depth).2 = storedFinal depth := by
  have adjacent := SourceNativeLivingRootHistoryAt.stored_timeline_adjacent (readMaterial depth)
    (fullHistory depth) (Fin.last (budget depth))
  have lastIndex : (Fin.last (budget depth)).succ = Fin.last (budget depth+1) := Fin.ext rfl
  change (fullTable depth).get (Fin.last (budget depth+1)) = _
  rw [← lastIndex]
  exact congrArg Prod.snd adjacent

end NoIslandNoMagic.CanonicalArithmeticState.GoldbachUnitSelectedActor.Calculation.Cursor.Timeline
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
