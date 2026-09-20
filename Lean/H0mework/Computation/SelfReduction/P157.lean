/-
  Proposition 157: consolidation phase transition.

  P51 says passive storage is not memory: without a recollection act, stored
  data is only data.  P150-P152 say F-only query structure cannot bootstrap
  new recollectable memory because its write component is identity.

  The clinical distinction raised by amnesia examples forces one more layer:

      active/reflexive memory production can be consolidated into a
      long-term store;
      once a recall index over that store exists, the consolidated content can
      be called by F-only reads without creating new reflexive memory.

  This file formalizes that bridge.  It deliberately does not claim that an
  arbitrary runtime automatically performs consolidation, nor that every
  saturated H¹ residual must be committed to long-term storage.  Those are
  mechanism-faithfulness obligations.  Lean proves the type-level separation:
  F-only remains flat for *new* reflexive production, while consolidated
  store-backed recall can still be callable.
-/

import H0mework.Realization.CyclicMemory.P125
import H0mework.Realization.Memory.P156

/-! ## Store-backed recall is an installed retrieval affordance -/

/-- A recall index over stored data.  This is not passive storage by itself:
it is the retrieval act that makes a stored item callable. -/
def storageRecallAct {State Atom : Type*}
    (store : StoredData State Atom) : RecollectionAct State Atom where
  fires := store.stored

/-- THEOREM 1: the store-backed recall act fires exactly on stored data. -/
theorem storageRecallAct_fires_iff_stored
    {State Atom : Type*}
    (store : StoredData State Atom) (x : State) (atom : Atom) :
    (storageRecallAct store).fires x atom <-> store.stored x atom := by
  rfl

/-- THEOREM 2: a store-backed recall act has recollectable potential exactly
when something is stored at that state. -/
theorem storageRecallPotential_iff_exists_stored
    {State Atom : Type*}
    (store : StoredData State Atom) (x : State) :
    RecollectableMemoryPotential (storageRecallAct store) x <->
      exists atom, store.stored x atom := by
  rfl

/-! ## Consolidation bridge from active recollection to long-term store -/

/-- A consolidation phase-transition certificate: an active recollection event
over one state space has committed its atom into a long-term store over another
state space.  The certificate is intentionally explicit; it is not inferred
from storage alone. -/
structure ConsolidationPhaseTransition
    {ActiveState LongTermState Atom : Type*}
    (activeAct : RecollectionAct ActiveState Atom)
    (store : StoredData LongTermState Atom) where
  activeState : ActiveState
  longTermState : LongTermState
  atom : Atom
  active_fires : activeAct.fires activeState atom
  stored_after : store.stored longTermState atom

/-- THEOREM 3: a consolidation certificate contains genuine active
recollectable potential on the source side. -/
theorem consolidation_active_recollectablePotential
    {ActiveState LongTermState Atom : Type*}
    {activeAct : RecollectionAct ActiveState Atom}
    {store : StoredData LongTermState Atom}
    (C : ConsolidationPhaseTransition activeAct store) :
    RecollectableMemoryPotential activeAct C.activeState := by
  exact ⟨C.atom, C.active_fires⟩

/-- THEOREM 4: after consolidation, the long-term store-backed recall act has
callable recollectable potential. -/
theorem consolidation_longTerm_recallPotential
    {ActiveState LongTermState Atom : Type*}
    {activeAct : RecollectionAct ActiveState Atom}
    {store : StoredData LongTermState Atom}
    (C : ConsolidationPhaseTransition activeAct store) :
    RecollectableMemoryPotential (storageRecallAct store) C.longTermState := by
  exact ⟨C.atom, C.stored_after⟩

/-- THEOREM 5: consolidated memory can be called from store while an F-only
query over the same long-term state still produces no new canonical reflexive
memory.  This is the formal HM-style distinction: old consolidated
understanding can remain callable, even though F-only activation cannot create
new reflexive memory. -/
theorem fOnly_can_call_consolidated_without_new_reflexiveProduction
    {ActiveState LongTermState Atom Observation : Type*}
    {activeAct : RecollectionAct ActiveState Atom}
    {store : StoredData LongTermState Atom}
    (C : ConsolidationPhaseTransition activeAct store)
    (q : ReflexiveQuery LongTermState Observation)
    (hF : FOnlyReflexiveQuery q) :
    RecollectableMemoryPotential (storageRecallAct store) C.longTermState /\
      ¬ RecollectableMemoryPotential
        (reflexiveRecollectionAct q) C.longTermState := by
  constructor
  · exact consolidation_longTerm_recallPotential C
  · exact fOnly_no_canonicalRecollectablePotential q hF C.longTermState

/-! ## Saturation side of the phase boundary -/

/-- THEOREM 6: full saturation is absorbing for field-valued noisy-OR rates.
This is the rate-level shape behind "enough consolidation loops reached the
absorbing boundary". -/
theorem satOrField_one_right_absorbing
    {α : Type*} [Field α] (σ : α) :
    satOrField σ 1 = 1 := by
  simp [satOrField]

/-- THEOREM 7: at full saturation, the selected three-agent H¹ residual is
killed and the selected ring becomes exact. -/
theorem fullSaturation_threeAgent_edgeExact
    {α : Type*} [Field α]
    (c : ThreeCycleTime -> ThreeCycleTime -> α) :
    ThreeAgentRingEdgeExact (cohomologyConsolidationStep (1 : α) c) := by
  exact cohomologyConsolidationStep_one_edgeExact c

/-- THEOREM 8: at full saturation, the accumulated finite-cycle residual is
zero.  For arbitrary finite permutations this is weaker than componentwise
exactness, but it is the quotient-level phase boundary P125 exposes. -/
theorem fullSaturation_finiteCycleResidual_zero
    {Index α : Type*} [Fintype Index] [Field α]
    (next : Equiv.Perm Index) (c : Index -> Index -> α) :
    finiteCycleResidual next
      (finiteCohomologyConsolidationStep (1 : α) c) = 0 := by
  rw [finiteCycleResidual_consolidationStep]
  ring

/-!
  Summary:
  - `storageRecallAct` distinguishes passive storage from an installed recall
    affordance.
  - `ConsolidationPhaseTransition` is the explicit bridge certificate from an
    active recollection event to long-term store.
  - F-only remains unable to create new canonical reflexive memory, but it can
    coexist with store-backed recall of already consolidated content.
  - Full saturation is the algebraic phase boundary where the selected H¹
    residual is killed.  The runtime still owes the mechanism that decides when
    such an exacted residual is committed into a concrete long-term store.
-/
