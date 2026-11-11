import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Runtime.StoredHistory

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceNativeLivingRootHistoryAt

universe u a
variable {N : WorldRelationNetwork.{u}} {process : SourceNativeLivingRootProcess N}
variable {A : Type a}
open private storedHead stored_head_eq withStoredHead stored_pair_cast from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Runtime.StoredHistory

private abbrev CollectCursor (process : SourceNativeLivingRootProcess N) (A : Type a) (fuel : Nat) :=
  Σ state : process.State, SourceNativeLivingRootHistoryAt process fuel state × Array A

private def collectStep (project : process.State → A) (fuel : Nat)
    (cursor : CollectCursor process A (fuel + 1)) : CollectCursor process A fuel := by
  rcases cursor with ⟨state,history,acc⟩
  cases history with
  | step tail => exact ⟨storedHead tail,withStoredHead tail,acc.push (project state)⟩

private def collect (project : process.State → A) (fuel : Nat) {state : process.State}
    (history : SourceNativeLivingRootHistoryAt process fuel state) (acc : Array A) : Array A :=
  let last := Nat.dfoldRev (α := fun n _ => CollectCursor process A n) fuel
    (fun n _ => collectStep project n) ⟨state,history,acc⟩
  last.2.2.push (project last.1)

private theorem collect_size (project : process.State → A) {fuel : Nat} {state : process.State}
    (history : SourceNativeLivingRootHistoryAt process fuel state) (acc : Array A) :
    (collect project fuel history acc).size = acc.size + (fuel + 1) := by
  induction fuel generalizing state acc with
  | zero => exact Array.size_push _
  | succ fuel previous =>
    cases history with
    | step tail =>
      change (collect project fuel (withStoredHead tail) (acc.push (project state))).size = _
      simp only [previous,Array.size_push]
      omega

private theorem collect_keeps (project : process.State → A) {fuel : Nat} {state : process.State}
    (history : SourceNativeLivingRootHistoryAt process fuel state) (acc : Array A)
    (i : Nat) (within : i < acc.size) :
    (collect project fuel history acc)[i]'(by rw [collect_size]; omega) = acc[i] := by
  induction fuel generalizing state acc with
  | zero => exact Array.getElem_push_lt within
  | succ fuel previous =>
    cases history with
    | step tail =>
      exact (previous (withStoredHead tail) (acc.push (project state))
        (by simp only [Array.size_push]; omega)).trans (Array.getElem_push_lt within)

private theorem collect_first (project : process.State → A) {fuel : Nat} {state : process.State}
    (history : SourceNativeLivingRootHistoryAt process fuel state) (acc : Array A) :
    (collect project fuel history acc)[acc.size]'(by rw [collect_size]; omega) = project state := by
  cases history with
  | exhausted => exact Array.getElem_push_eq
  | step tail =>
    exact (collect_keeps project (withStoredHead tail) (acc.push (project state)) acc.size
      (by simp only [Array.size_push]; omega)).trans Array.getElem_push_eq

private theorem collect_adjacent (project : process.State → A) {fuel : Nat} {state : process.State}
    (history : SourceNativeLivingRootHistoryAt process fuel state) (acc : Array A) (i : Fin fuel) :
    let table := collect project fuel history acc
    (table[acc.size+i.val]'(by rw [collect_size]; omega),
      table[acc.size+(i.val+1)]'(by rw [collect_size]; omega)) =
        Prod.map project project (history.storedPairAt i) := by
  induction fuel generalizing state acc with
  | zero => exact Fin.elim0 i
  | succ fuel previous =>
    cases history with
    | step tail =>
      let pushed := acc.push (project state)
      let rest := withStoredHead tail
      refine Fin.cases ?_ (fun j => ?_) i
      · have first := (collect_keeps project rest pushed acc.size
          (by simp only [pushed,Array.size_push]; omega)).trans Array.getElem_push_eq
        have second := collect_first project rest pushed
        change ((collect project fuel rest pushed)[acc.size]'_,
          (collect project fuel rest pushed)[acc.size+1]'_) = (project state,project (storedHead tail))
        have size : acc.size+1 = pushed.size := (Array.size_push _).symm
        exact Prod.ext first ((getElem_congr_idx size).trans second)
      · have adjacent := previous rest pushed j
        change ((collect project fuel rest pushed)[acc.size+(j.val+1)]'_,
          (collect project fuel rest pushed)[acc.size+(j.val+1+1)]'_) =
            Prod.map project project (rest.storedPairAt j)
        have size : pushed.size = acc.size+1 := Array.size_push _
        have oldIndex : acc.size+(j.val+1) = pushed.size+j.val := by omega
        have nextIndex : acc.size+(j.val+1+1) = pushed.size+(j.val+1) := by omega
        exact (Prod.ext (getElem_congr_idx oldIndex) (getElem_congr_idx nextIndex)).trans adjacent

/-- Read every stored state once into an array with direct stage indexing. -/
def storedTimeline (project : process.State → A) {fuel : Nat} {state : process.State}
    (history : SourceNativeLivingRootHistoryAt process fuel state) : Vector A (fuel + 1) :=
  ⟨collect project fuel (withStoredHead history) (Array.emptyWithCapacity (fuel + 1)),
    by rw [collect_size]; simp⟩

theorem stored_timeline_adjacent (project : process.State → A) {fuel : Nat} {state : process.State}
    (history : SourceNativeLivingRootHistoryAt process fuel state) (i : Fin fuel) :
    ((history.storedTimeline project).get i.castSucc,(history.storedTimeline project).get i.succ) =
      Prod.map project project (history.storedPairAt i) := by
  let empty : Array A := Array.emptyWithCapacity (fuel+1)
  have adjacent := collect_adjacent project (withStoredHead history) empty i
  have same : (withStoredHead history).storedPairAt i = history.storedPairAt i :=
    stored_pair_cast (stored_head_eq history).symm history i
  dsimp only at adjacent
  rw [same] at adjacent
  let table := collect project fuel (withStoredHead history) empty
  change (table[i.val]'_,table[i.val+1]'_) = _
  have size : empty.size = 0 := rfl
  have oldIndex : i.val = empty.size+i.val := by omega
  have nextIndex : i.val+1 = empty.size+(i.val+1) := by omega
  exact (Prod.ext (getElem_congr_idx oldIndex) (getElem_congr_idx nextIndex)).trans adjacent

end SourceNativeLivingRootHistoryAt

namespace SourceOperationRuntime
open SourceOperationEffects SourceOperationScalarRelations
noncomputable section
universe r u m
variable {N : WorldRelationNetwork.{u}} {process : SourceNativeLivingRootProcess N}
variable {R : Type r} [CommRing R] {Sorts : Type u}
variable {Value Var : Sorts → Type (max r u)}
variable [∀ s, AddCommGroup (Value s)] [∀ s, Module R (Value s)] {s : Sorts}
variable {Material : Type m} [AddCommGroup Material]
variable (environment : Material →+ Env Value Var)

def timelineEnvironments {fuel : Nat} (table : Vector Material (fuel+1)) (i : Fin fuel) :
    Env Value Var × Env Value Var :=
  let old := table.get i.castSucc
  (environment old,environment (table.get i.succ - old))

/-- The existing update inventory reads the old and effect coordinates of this table. -/
def timelineInventory {fuel : Nat} (table : Vector Material (fuel+1)) (i : Fin fuel) :
    FormalCarrier R Value Var s →ₗ[R] Value s × Value s :=
  let reads := timelineEnvironments environment table i
  updateInventory (R := R) (s := s) reads.1 reads.2

theorem timeline_environments_actual (readMaterial : process.State → Material)
    {runtime : LivingRuntimeState process} {fuel : Nat}
    (history : SourceNativeLivingRootHistoryAt process fuel runtime.state) (i : Fin fuel) :
    let stage := SourceGeneratedRuntimeMaterialStageAt.generate (runtime.advance i.val)
    timelineEnvironments environment (history.storedTimeline readMaterial) i =
      (oldEnvironment readMaterial environment stage,incrementEnvironment readMaterial environment stage) := by
  let applyPair := fun states : Material × Material =>
    (environment states.1,environment (states.2-states.1))
  exact (congrArg applyPair (SourceNativeLivingRootHistoryAt.stored_timeline_adjacent readMaterial history i)).trans
    (stored_environments_actual readMaterial environment history i)

theorem timeline_inventory_actual (readMaterial : process.State → Material)
    {runtime : LivingRuntimeState process} {fuel : Nat}
    (history : SourceNativeLivingRootHistoryAt process fuel runtime.state) (i : Fin fuel) :
    timelineInventory (R := R) (s := s) environment (history.storedTimeline readMaterial) i =
      stageInventory (R := R) (s := s) readMaterial environment
        (SourceGeneratedRuntimeMaterialStageAt.generate (runtime.advance i.val)) :=
  congrArg (fun reads : Env Value Var × Env Value Var => updateInventory (R := R) (s := s) reads.1 reads.2)
    (timeline_environments_actual environment readMaterial history i)

end
end SourceOperationRuntime
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
