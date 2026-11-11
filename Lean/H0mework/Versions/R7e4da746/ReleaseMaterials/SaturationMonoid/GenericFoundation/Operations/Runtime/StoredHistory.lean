import H0mework.Versions.R2.Realization.Operations.RuntimePrefix

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot

universe u

namespace SourceNativeLivingRootHistoryAt

variable {N : WorldRelationNetwork.{u}} {process : SourceNativeLivingRootProcess N}

@[noinline] private def storedHead {fuel : Nat} {state : process.State}
    (history : SourceNativeLivingRootHistoryAt process fuel state) : process.State :=
  SourceNativeLivingRootHistoryAt.casesOn (motive := fun _ _ _ => process.State) history
    (fun reached => reached) (fun {_} {current} _ => current)

private theorem stored_head_eq {fuel : Nat} {state : process.State}
    (history : SourceNativeLivingRootHistoryAt process fuel state) : storedHead history = state := by
  cases history <;> rfl

private def withStoredHead {fuel : Nat} {state : process.State}
    (history : SourceNativeLivingRootHistoryAt process fuel state) :
    SourceNativeLivingRootHistoryAt process fuel (storedHead history) :=
  Eq.mp (congrArg (SourceNativeLivingRootHistoryAt process fuel) (stored_head_eq history).symm) history

/-- Read the two stored states of one exact micro transition. -/
def storedPairAt {fuel : Nat} {state : process.State}
    (history : SourceNativeLivingRootHistoryAt process fuel state) : Fin fuel → process.State × process.State :=
  Nat.rec (motive := fun fuel => ∀ {state : process.State},
      SourceNativeLivingRootHistoryAt process fuel state → Fin fuel → process.State × process.State)
    (fun {_} _ => Fin.elim0)
    (fun _ previous {state} history i => by
      cases history with
      | step tail => exact Fin.cases (state,storedHead tail) (previous (withStoredHead tail)) i)
    fuel history

private theorem stored_pair_cast {fuel : Nat} {old new : process.State} (same : old = new)
    (history : SourceNativeLivingRootHistoryAt process fuel old) (i : Fin fuel) :
    (Eq.mp (congrArg (SourceNativeLivingRootHistoryAt process fuel) same) history).storedPairAt i =
      history.storedPairAt i := by
  cases same
  rfl

private theorem exact_history {fuel : Nat} {state : process.State}
    (history : SourceNativeLivingRootHistoryAt process fuel state) :
    history = process.generateHistory fuel state := by
  induction history with
  | exhausted => rfl
  | @step fuel state tail previous =>
    change SourceNativeLivingRootHistoryAt.step tail =
      .step (process.generateHistory fuel (process.successor state))
    rw [previous]

private theorem advance_first (runtime : LivingRuntimeState process) (count : Nat) :
    runtime.tick.next.advance count = runtime.advance (count+1) := by
  induction count with
  | zero => rfl
  | succ count previous =>
    change (runtime.tick.next.advance count).tick.next = (runtime.advance (count+1)).tick.next
    rw [previous]

private theorem stored_pair_run (runtime : LivingRuntimeState process) (fuel : Nat) (i : Fin fuel) :
    (runtime.run fuel).storedPairAt i = ((runtime.advance i.val).state,(runtime.advance (i.val+1)).state) := by
  induction fuel generalizing runtime with
  | zero => exact Fin.elim0 i
  | succ fuel previous =>
    refine Fin.cases ?_ (fun j => ?_) i
    · change (runtime.state,storedHead (runtime.tick.next.run fuel)) =
        ((runtime.advance 0).state,(runtime.advance (0+1)).state)
      simp only [stored_head_eq]
      rfl
    · change (withStoredHead (runtime.tick.next.run fuel)).storedPairAt j = _
      unfold withStoredHead
      rw [stored_pair_cast (stored_head_eq (runtime.tick.next.run fuel)).symm,previous]
      simp only [advance_first,Fin.val_succ]

/-- Any retained finite execution of this source has these exact consecutive states. -/
theorem stored_pair_actual {runtime : LivingRuntimeState process} {fuel : Nat}
    (history : SourceNativeLivingRootHistoryAt process fuel runtime.state) (i : Fin fuel) :
    history.storedPairAt i = ((runtime.advance i.val).state,(runtime.advance (i.val+1)).state) :=
  (congrArg (fun h => h.storedPairAt i) (exact_history history)).trans (stored_pair_run runtime fuel i)

/-- The existing causal answer and ledger use the actual stored source state. -/
def storedActivation {runtime : LivingRuntimeState process} {fuel : Nat}
    (history : SourceNativeLivingRootHistoryAt process fuel runtime.state) (i : Fin fuel) :=
  process.canonicalCausalAnswerAndNext (ULift.up (history.storedPairAt i).1)

theorem stored_activation_actual {runtime : LivingRuntimeState process} {fuel : Nat}
    (history : SourceNativeLivingRootHistoryAt process fuel runtime.state) (i : Fin fuel) :
    HEq (history.storedActivation i) (runtime.advance i.val).tick :=
  process.canonicalAnswerAndNext_heq_of_current_eq
    (congrArg (fun states : process.State × process.State => process.stateAt states.1)
      (stored_pair_actual history i))

theorem stored_successor_actual {runtime : LivingRuntimeState process} {fuel : Nat}
    (history : SourceNativeLivingRootHistoryAt process fuel runtime.state) (i : Fin fuel) :
    (history.storedActivation i).nextCurrent = process.stateAt (history.storedPairAt i).2 := by
  change process.stateAt (process.successor (history.storedPairAt i).1) =
    process.stateAt (history.storedPairAt i).2
  rw [stored_pair_actual]
  rfl

end SourceNativeLivingRootHistoryAt

namespace SourceOperationRuntime
open SourceOperationEffects SourceOperationScalarRelations
noncomputable section

universe r m
variable {N : WorldRelationNetwork.{u}} {process : SourceNativeLivingRootProcess N}
variable {R : Type r} [CommRing R] {Sorts : Type u}
variable {Value Var : Sorts → Type (max r u)}
variable [∀ s, AddCommGroup (Value s)] [∀ s, Module R (Value s)] {s : Sorts}
variable {Material : Type m} [AddCommGroup Material]
variable (readMaterial : process.State → Material) (environment : Material →+ Env Value Var)

def storedOldEnvironment {runtime : LivingRuntimeState process} {fuel : Nat}
    (history : SourceNativeLivingRootHistoryAt process fuel runtime.state) (i : Fin fuel) : Env Value Var :=
  environment (readMaterial (history.storedPairAt i).1)

def storedIncrementEnvironment {runtime : LivingRuntimeState process} {fuel : Nat}
    (history : SourceNativeLivingRootHistoryAt process fuel runtime.state) (i : Fin fuel) : Env Value Var :=
  let states := history.storedPairAt i
  environment (readMaterial states.2 - readMaterial states.1)

theorem stored_environments_actual {runtime : LivingRuntimeState process} {fuel : Nat}
    (history : SourceNativeLivingRootHistoryAt process fuel runtime.state) (i : Fin fuel) :
    let stage := SourceGeneratedRuntimeMaterialStageAt.generate (runtime.advance i.val)
    (storedOldEnvironment readMaterial environment history i,storedIncrementEnvironment readMaterial environment history i) =
      (oldEnvironment readMaterial environment stage,incrementEnvironment readMaterial environment stage) := by
  dsimp only [storedOldEnvironment,storedIncrementEnvironment]
  rw [SourceNativeLivingRootHistoryAt.stored_pair_actual]
  rfl

/-- The actual pair of stored states generates the same source update inventory. -/
def storedStageInventory {runtime : LivingRuntimeState process} {fuel : Nat}
    (history : SourceNativeLivingRootHistoryAt process fuel runtime.state) (i : Fin fuel) :
    FormalCarrier R Value Var s →ₗ[R] Value s × Value s :=
  let states := history.storedPairAt i
  updateInventory (R := R) (s := s) (environment (readMaterial states.1))
    (environment (readMaterial states.2 - readMaterial states.1))

theorem stored_inventory_actual {runtime : LivingRuntimeState process} {fuel : Nat}
    (history : SourceNativeLivingRootHistoryAt process fuel runtime.state) (i : Fin fuel) :
    storedStageInventory (R := R) (s := s) readMaterial environment history i =
      stageInventory (R := R) (s := s) readMaterial environment
        (SourceGeneratedRuntimeMaterialStageAt.generate (runtime.advance i.val)) :=
  congrArg (fun reads : Env Value Var × Env Value Var => updateInventory (R := R) (s := s) reads.1 reads.2)
    (stored_environments_actual readMaterial environment history i)

end
end SourceOperationRuntime
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
