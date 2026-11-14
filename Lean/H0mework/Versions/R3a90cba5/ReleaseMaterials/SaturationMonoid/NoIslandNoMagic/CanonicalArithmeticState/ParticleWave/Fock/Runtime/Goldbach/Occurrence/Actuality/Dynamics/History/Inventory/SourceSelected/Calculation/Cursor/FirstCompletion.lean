import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalArithmeticState.ParticleWave.Fock.Runtime.Goldbach.Occurrence.Actuality.Dynamics.History.Inventory.SourceSelected.Calculation.Cursor.Timeline
import Batteries.Data.Fin.Lemmas

set_option autoImplicit false
noncomputable section

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalArithmeticState.GoldbachUnitSelectedActor.Calculation.Cursor.FirstCompletion

open NoIslandNoMagic.CanonicalArithmeticState.GoldbachUnitSelectedActor.Calculation.Registered
open NoIslandNoMagic.CanonicalArithmeticState.GoldbachUnitSelectedActor.Calculation.Cursor.Source
open NoIslandNoMagic.CanonicalArithmeticState.GoldbachUnitSelectedActor.Calculation.Cursor.Stored
open CanonicalUnitArithmeticEffectiveAdditiveProducer
open CanonicalUnitArithmeticEffectiveFactorRepairOrbitProducer
open private readCursor_pulses from H0mework.Versions.R7e4da746.Arithmetic.FockUnitAction.Inventory.SourceSelected.Calculation.Cursor.Source

private def cursorRead (depth : Nat) (state : State depth) : Option (Registered.Point depth) :=
  readCursor depth (OF.finiteVisit (old depth) (origin depth) (reader depth) state.down).current.1

/-- Read the full occurrence and actor branch from each of the stored states. -/
def actorTable (depth : Nat) : Vector (Option (Registered.Point depth)) (budget depth + 2) :=
  (fullHistory depth).storedTimeline (cursorRead depth)

theorem actor_table_root (depth : Nat) : (actorTable depth).get 0 = none := by
  have adjacent := SourceNativeLivingRootHistoryAt.stored_timeline_adjacent
    (cursorRead depth) (fullHistory depth) (0 : Fin (budget depth + 1))
  rw [SourceNativeLivingRootHistoryAt.stored_pair_actual] at adjacent
  have root := congrArg Prod.fst adjacent
  exact root.trans (readCursor_pulses depth (budget depth))

theorem actor_table_at (depth count : Nat) (within : count ≤ budget depth) :
    (actorTable depth).get ⟨count + 1, Nat.succ_lt_succ (Nat.lt_succ_of_le within)⟩ =
      some (⟨emitted depth, run count (initial (source depth (emitted depth)))⟩ :
        Registered.Point depth) := by
  have adjacent := SourceNativeLivingRootHistoryAt.stored_timeline_adjacent
    (cursorRead depth) (fullHistory depth) ⟨count, Nat.lt_succ_of_le within⟩
  rw [SourceNativeLivingRootHistoryAt.stored_pair_actual] at adjacent
  exact (congrArg Prod.snd adjacent).trans (current_cursor_fibre depth count within)

/-- Both points determine the very same material boundary read by the runtime. -/
theorem actor_material_adjacent (depth : Nat) (i : Fin (budget depth + 1)) :
    (Finsupp.single ((actorTable depth).get i.castSucc) 1,
      Finsupp.single ((actorTable depth).get i.succ) 1) =
      Prod.map (readMaterial depth) (readMaterial depth) ((fullHistory depth).storedPairAt i) := by
  let material : Option (Registered.Point depth) → Material depth := fun point => Finsupp.single point 1
  exact congrArg (Prod.map material material)
    (SourceNativeLivingRootHistoryAt.stored_timeline_adjacent (cursorRead depth) (fullHistory depth) i)

private theorem table_run_at (depth : Nat) (i : Fin (budget depth + 2)) (bound : 0 < i.val) :
    (actorTable depth).get i =
      some (⟨emitted depth, run (i.val - 1) (initial (source depth (emitted depth)))⟩ :
        Registered.Point depth) := by
  have upper := i.isLt
  have within : i.val - 1 ≤ budget depth := by omega
  have read := actor_table_at depth (i.val - 1) within
  have address : (⟨i.val - 1 + 1, Nat.succ_lt_succ (Nat.lt_succ_of_le within)⟩ :
      Fin (budget depth + 2)) = i := Fin.ext (by
    change i.val - 1 + 1 = i.val
    omega)
  rw [address] at read
  exact read

def isCompleted {depth : Nat} : Option (Registered.Point depth) → Bool
  | some ⟨_, .completed _⟩ => true
  | _ => false

private theorem completion_present (depth : Nat) :
    (Fin.find? (fun i => isCompleted ((actorTable depth).get i))).isSome := by
  apply Fin.isSome_find?_of_eq_true (i := Fin.last (budget depth + 1))
  change isCompleted ((actorTable depth).get
    ⟨budget depth + 1, Nat.succ_lt_succ (Nat.lt_succ_self _)⟩) = true
  rw [actor_table_at depth (budget depth) le_rfl, run_source]
  rfl

/-- The terminal address is selected by the completed branch of a stored state. -/
def firstComplete (depth : Nat) : Fin (budget depth + 2) :=
  (Fin.find? (fun i => isCompleted ((actorTable depth).get i))).get (completion_present depth)

theorem first_is_completed (depth : Nat) :
    isCompleted ((actorTable depth).get (firstComplete depth)) = true :=
  Fin.get_find?_eq_true (completion_present depth)

theorem earlier_not_completed (depth : Nat) (i : Fin (budget depth + 2))
    (before : i < firstComplete depth) : isCompleted ((actorTable depth).get i) = false :=
  Fin.get_find?_minimal (completion_present depth) i before

theorem first_after_bind (depth : Nat) : 2 ≤ (firstComplete depth).val := by
  have completed := first_is_completed depth
  by_contra tooSoon
  have small : (firstComplete depth).val = 0 ∨ (firstComplete depth).val = 1 := by omega
  rcases small with zero | one
  · have address : firstComplete depth = 0 := Fin.ext zero
    rw [address, actor_table_root] at completed
    cases completed
  · have address : firstComplete depth = ⟨1, by omega⟩ := Fin.ext one
    rw [address, actor_table_at depth 0 (Nat.zero_le _)] at completed
    cases completed

/-- This transition is an actor pulse from the same complete original history. -/
def terminalTransition (depth : Nat) : Fin (budget depth + 1) :=
  ⟨(firstComplete depth).val - 1, by
    have upper := (firstComplete depth).isLt
    have lower := first_after_bind depth
    omega⟩

theorem terminal_successor (depth : Nat) :
    (terminalTransition depth).succ = firstComplete depth :=
  Fin.ext (by have bound := first_after_bind depth; change (firstComplete depth).val - 1 + 1 = _; omega)

theorem terminal_predecessor_live (depth : Nat) :
    isCompleted ((actorTable depth).get (terminalTransition depth).castSucc) = false :=
  earlier_not_completed depth _ (by
    have bound := first_after_bind depth
    change (firstComplete depth).val - 1 < (firstComplete depth).val
    omega)

private theorem run_add {index : Nat} {s : EffectiveSplitAt index} (first second : Nat) (state : StateAt s) :
    run (first + second) state = run second (run first state) := by
  induction first generalizing state with
  | zero => simp only [Nat.zero_add, run]
  | succ first previous =>
      rw [show first + 1 + second = first + second + 1 by omega]
      exact previous (next state)

private theorem run_completed {index : Nat} {s : EffectiveSplitAt index} (count : Nat) (outcome : OutcomeAt s) :
    run count (.completed outcome) = .completed outcome := by
  induction count with
  | zero => rfl
  | succ count previous => exact previous

/-- Every later cell retains the same completed occurrence and all its receipts. -/
theorem completed_suffix (depth : Nat) (i : Fin (budget depth + 2)) (later : firstComplete depth ≤ i) :
    (actorTable depth).get i = (actorTable depth).get (firstComplete depth) := by
  let finish := firstComplete depth
  have bound := first_after_bind depth
  have laterVal : finish.val ≤ i.val := later
  have finishRead := table_run_at depth finish (by change 0 < (firstComplete depth).val; omega)
  have laterRead := table_run_at depth i (by change 2 ≤ finish.val at bound; omega)
  have completed := first_is_completed depth
  change isCompleted ((actorTable depth).get finish) = true at completed
  rw [finishRead] at completed
  rw [laterRead, finishRead]
  have offset : i.val - 1 = (finish.val - 1) + (i.val - finish.val) := by omega
  rw [offset, run_add]
  cases same : run (finish.val - 1) (initial (source depth (emitted depth))) with
  | active trail => simp [same, isCompleted] at completed
  | completed outcome => rw [run_completed]

private def pointRemaining (depth : Nat) : Option (Registered.Point depth) → Nat
  | none => budget depth + 1
  | some ⟨_, state⟩ => remaining state

/-- The complete material coordinates up to and including the first completion. -/
def prefixPoint (depth : Nat) (i : Fin ((firstComplete depth).val + 1)) :
    Option (Registered.Point depth) :=
  (actorTable depth).get (i.castLE (Nat.succ_le_of_lt (firstComplete depth).isLt))

private theorem live_remaining {depth : Nat} {point : Registered.Point depth}
    (live : isCompleted (some point) = false) : 0 < remaining point.2 := by
  rcases point with ⟨_, state⟩
  cases state with
  | @active current trail =>
      have floor := splitRight_atLeastTwo current
      change 0 < splitRight current - 1
      omega
  | completed outcome => cases live

private theorem prefix_remaining (depth : Nat) :
    StrictAnti (fun i => pointRemaining depth (prefixPoint depth i)) := by
  intro i j before
  let oldSlot : Fin (budget depth + 2) := i.castLE (Nat.succ_le_of_lt (firstComplete depth).isLt)
  let newSlot : Fin (budget depth + 2) := j.castLE (Nat.succ_le_of_lt (firstComplete depth).isLt)
  have chronological : oldSlot.val < newSlot.val := before
  have newPositive : 0 < newSlot.val := by omega
  let start := initial (source depth (emitted depth))
  change pointRemaining depth ((actorTable depth).get newSlot) <
    pointRemaining depth ((actorTable depth).get oldSlot)
  rw [table_run_at depth newSlot newPositive]
  by_cases unbound : oldSlot.val = 0
  · have address : oldSlot = 0 := Fin.ext unbound
    rw [address, actor_table_root]
    change remaining (run (newSlot.val - 1) start) < budget depth + 1
    have cap := remaining_run_le (newSlot.val - 1) start
    change remaining (run (newSlot.val - 1) start) ≤ budget depth - (newSlot.val - 1) at cap
    omega
  · have oldPositive := Nat.pos_of_ne_zero unbound
    have newLe : newSlot.val ≤ (firstComplete depth).val := Nat.le_of_lt_succ j.isLt
    have live := earlier_not_completed depth oldSlot (by change oldSlot.val < _; omega)
    have oldRead := table_run_at depth oldSlot oldPositive
    rw [oldRead] at live ⊢
    have positive : 0 < remaining (run (oldSlot.val - 1) start) := live_remaining live
    change remaining (run (newSlot.val - 1) start) < remaining (run (oldSlot.val - 1) start)
    have offset : newSlot.val - 1 = (oldSlot.val - 1) + (newSlot.val - oldSlot.val) := by omega
    rw [offset, run_add]
    have cap := remaining_run_le (newSlot.val - oldSlot.val) (run (oldSlot.val - 1) start)
    omega

theorem prefix_point_injective (depth : Nat) : Function.Injective (prefixPoint depth) := by
  intro i j same
  exact (prefix_remaining depth).injective (congrArg (pointRemaining depth) same)

/-- The first completed source coordinate already supplies the independent terminal material. -/
theorem first_material_terminal (depth : Nat) :
    Finsupp.single ((actorTable depth).get (firstComplete depth)) 1 = storedFinal depth := by
  let last := Fin.last (budget depth)
  have actual := congrArg Prod.snd (actor_material_adjacent depth last)
  have lastAddress : last.succ = Fin.last (budget depth + 1) := Fin.ext rfl
  change Finsupp.single ((actorTable depth).get last.succ) 1 = storedFinal depth at actual
  rw [lastAddress, completed_suffix depth _ (Fin.le_last _)] at actual
  exact actual

end NoIslandNoMagic.CanonicalArithmeticState.GoldbachUnitSelectedActor.Calculation.Cursor.FirstCompletion
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
