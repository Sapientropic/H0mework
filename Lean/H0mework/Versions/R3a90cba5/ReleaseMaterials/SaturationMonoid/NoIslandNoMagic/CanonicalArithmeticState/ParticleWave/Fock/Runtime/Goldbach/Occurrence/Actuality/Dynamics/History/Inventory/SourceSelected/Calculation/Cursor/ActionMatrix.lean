import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Runtime.TimelineBasis
import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalArithmeticState.ParticleWave.Fock.Runtime.Goldbach.Occurrence.Actuality.Dynamics.History.Inventory.SourceSelected.Calculation.Cursor.FirstCompletion

set_option autoImplicit false
noncomputable section

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalArithmeticState.GoldbachUnitSelectedActor.Calculation.Cursor.ActionMatrix

open SourceOperationRuntime SourceOperationEffects
open NoIslandNoMagic.CanonicalArithmeticState.GoldbachUnitSelectedActor.Calculation.Cursor.Source
open NoIslandNoMagic.CanonicalArithmeticState.GoldbachUnitSelectedActor.Calculation.Cursor.Stored
open NoIslandNoMagic.CanonicalArithmeticState.GoldbachUnitSelectedActor.Calculation.Cursor.FirstCompletion

abbrev length (depth : Nat) : Nat := (firstComplete depth).val

/-- The complete precompletion coordinates are selected by the original stored actor. -/
@[instance_reducible]
def sourceInverse (depth : Nat) :
    Invertible (TimelineBasis.observed (R := ℤ) (prefixPoint depth)) :=
  TimelineBasis.inverse (prefixPoint depth) (prefix_point_injective depth)

theorem source_determinant (depth : Nat) :
    (TimelineBasis.observed (R := ℤ) (prefixPoint depth)).det = 1 :=
  TimelineBasis.determinant_one (prefixPoint depth) (prefix_point_injective depth)

def indexedTransition (depth : Nat) (i : Fin (length depth)) : Fin (budget depth + 1) :=
  i.castLE (Nat.le_of_lt_succ (firstComplete depth).isLt)

theorem root_word (depth : Nat) :
    TimelineBasis.word (R := ℤ) (prefixPoint depth) 0 =
      readMaterial depth ((fullHistory depth).storedPairAt 0).1 := by
  rw [TimelineBasis.word_zero]
  exact congrArg Prod.fst (actor_material_adjacent depth 0)

theorem effect_word (depth : Nat) (i : Fin (length depth)) :
    let transition := indexedTransition depth i
    let states := (fullHistory depth).storedPairAt transition
    TimelineBasis.word (R := ℤ) (prefixPoint depth) i.succ =
      readMaterial depth states.2 - readMaterial depth states.1 := by
  rw [TimelineBasis.word_succ]
  exact congrArg (fun pair : Material depth × Material depth => pair.2 - pair.1)
    (actor_material_adjacent depth (indexedTransition depth i))

theorem effect_environment (depth : Nat) (i : Fin (length depth)) :
    let transition := indexedTransition depth i
    let stage := SourceGeneratedRuntimeMaterialStageAt.generate ((mathSeed depth).advance transition.val)
    environment depth (TimelineBasis.word (R := ℤ) (prefixPoint depth) i.succ) =
      incrementEnvironment (readMaterial depth) (environment depth) stage :=
  (congrArg (environment depth) (effect_word depth i)).trans
    (congrArg Prod.snd (stored_environments_actual (readMaterial depth) (environment depth)
      (fullHistory depth) (indexedTransition depth i)))

theorem terminal_synthesis (depth : Nat) :
    TimelineBasis.synth (R := ℤ) (prefixPoint depth) (fun _ => 1) = storedFinal depth :=
  (TimelineBasis.synth_terminal (prefixPoint depth)).trans (first_material_terminal depth)

theorem terminal_inverse (depth : Nat) :
    TimelineBasis.recover (prefixPoint depth) (sourceInverse depth) (storedFinal depth) = fun _ => 1 := by
  rw [← terminal_synthesis depth]
  exact TimelineBasis.recover_synth (prefixPoint depth) (sourceInverse depth) (fun _ => 1)

private theorem hold_word (depth : Nat) (i : Fin (budget depth + 1))
    (after : firstComplete depth ≤ i.castSucc) :
    TimelineBasis.word (R := ℤ) (actorTable depth).get i.succ = 0 := by
  have later : i.castSucc ≤ i.succ := Nat.le_succ i.val
  have same := (completed_suffix depth i.succ (after.trans later)).trans
    (completed_suffix depth i.castSucc after).symm
  rw [TimelineBasis.word_succ, same, sub_self]

theorem hold_environment (depth : Nat) (i : Fin (budget depth + 1))
    (after : firstComplete depth ≤ i.castSucc) :
    storedIncrementEnvironment (readMaterial depth) (environment depth) (fullHistory depth) i = 0 := by
  have same : TimelineBasis.word (R := ℤ) (actorTable depth).get i.succ =
      readMaterial depth ((fullHistory depth).storedPairAt i).2 -
        readMaterial depth ((fullHistory depth).storedPairAt i).1 := by
    rw [TimelineBasis.word_succ]
    exact congrArg (fun pair : Material depth × Material depth => pair.2 - pair.1)
      (actor_material_adjacent depth i)
  change environment depth (readMaterial depth ((fullHistory depth).storedPairAt i).2 -
    readMaterial depth ((fullHistory depth).storedPairAt i).1) = 0
  rw [← same, hold_word depth i after, map_zero]

/-- A genuine held pulse adds a zero column to the full actor matrix. -/
theorem full_determinant_zero_of_hold (depth : Nat) (i : Fin (budget depth + 1))
    (after : firstComplete depth ≤ i.castSucc) :
    (TimelineBasis.observed (R := ℤ) (actorTable depth).get).det = 0 := by
  apply Matrix.det_eq_zero_of_column_eq_zero i.succ
  intro row
  change TimelineBasis.word (R := ℤ) (actorTable depth).get i.succ ((actorTable depth).get row) = 0
  rw [hold_word depth i after, Finsupp.zero_apply]

end NoIslandNoMagic.CanonicalArithmeticState.GoldbachUnitSelectedActor.Calculation.Cursor.ActionMatrix
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
