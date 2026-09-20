/-
  Proposition 19: runtime graph join algebra bridge.

  Proposition 18 proves Newman generically.  The Python runtime now emits a
  Newman-style graph certificate for the registered graph surfaces, but that
  certificate is a dictionary.  This file builds the missing Lean bridge:

    * the six runtime label joins are formalized as concrete join algebras;
    * products of join algebras are join algebras, so mixed surfaces are
      covered by a Lean-level product construction rather than a Python-side
      convention;
    * a graph step is modeled as "consume one pending event, append
      content-addressed edges, and join touched labels";
    * any such graph step is terminating by pending-event cardinality;
    * every one-step fork has a local diamond by edge union commutativity and
      label join commutativity/associativity;
    * therefore it packages a real `NewmanGraphConfluenceCertificate`.

  The result is algebraic: once a runtime surface is expressed through one of
  these join algebras, confluence is not a representative-fixture fact anymore.
-/

import Mathlib
import H0mework.Realization.Observation.Saturation
import H0mework.Realization.Observation.RewriteSystem

open Relation

/-! ## Runtime label join algebras -/

/-- The exact algebraic contract implemented by `_join_label` in the Python
runtime certificate.  Associativity and commutativity are enough to make
critical-pair diamonds; concrete runtime boundaries still own value parsing and
source-truth separation. -/
structure RuntimeJoinAlgebra where
  Carrier : Type
  join : Carrier → Carrier → Carrier
  join_comm : ∀ a b, join a b = join b a
  join_assoc : ∀ a b c, join (join a b) c = join a (join b c)

namespace RuntimeJoinAlgebra

variable (A : RuntimeJoinAlgebra)

theorem join_right_comm (a b c : A.Carrier) :
    A.join (A.join a b) c = A.join (A.join a c) b := by
  rw [A.join_assoc, A.join_assoc, A.join_comm b c]

end RuntimeJoinAlgebra

/-! ### The six runtime join operators -/

theorem satOrField_assoc_Q (a b c : ℚ) :
    satOrField (satOrField a b) c = satOrField a (satOrField b c) := by
  simp only [satOrField]
  ring

theorem satOrField_comm_Q (a b : ℚ) : satOrField a b = satOrField b a := by
  simp only [satOrField]
  ring

/-- Runtime `noisy_or`: saturation-rate composition. -/
def noisyOrJoinAlgebra : RuntimeJoinAlgebra where
  Carrier := ℚ
  join := satOrField
  join_comm := satOrField_comm_Q
  join_assoc := satOrField_assoc_Q

/-- Runtime `max`: monotone confidence / evidence join. -/
def maxJoinAlgebra : RuntimeJoinAlgebra where
  Carrier := ℚ
  join := max
  join_comm := by
    intro a b
    exact max_comm a b
  join_assoc := by
    intro a b c
    exact max_assoc a b c

/-- Runtime `sum`: additive delta aggregation after per-surface grouping. -/
def sumJoinAlgebra : RuntimeJoinAlgebra where
  Carrier := ℚ
  join := (· + ·)
  join_comm := by
    intro a b
    exact add_comm a b
  join_assoc := by
    intro a b c
    exact add_assoc a b c

/-- The graph lifecycle statuses currently owned by `concept_lifecycle.py`. -/
inductive RuntimeStatus where
  | staging
  | verified
  | parked
  | retired
  deriving DecidableEq, Repr

namespace RuntimeStatus

def rank : RuntimeStatus → Nat
  | staging => 0
  | verified => 1
  | parked => 2
  | retired => 3

/-- Runtime `status_join`: choose the status with the greater lifecycle rank. -/
def join (a b : RuntimeStatus) : RuntimeStatus :=
  if rank a ≤ rank b then b else a

theorem join_comm (a b : RuntimeStatus) : join a b = join b a := by
  cases a <;> cases b <;> decide

theorem join_assoc (a b c : RuntimeStatus) :
    join (join a b) c = join a (join b c) := by
  cases a <;> cases b <;> cases c <;> decide

end RuntimeStatus

/-- Runtime `status_join`: lifecycle status semilattice. -/
def statusJoinAlgebra : RuntimeJoinAlgebra where
  Carrier := RuntimeStatus
  join := RuntimeStatus.join
  join_comm := RuntimeStatus.join_comm
  join_assoc := RuntimeStatus.join_assoc

/-- Runtime `bool_or`: quarantine / flag accumulation. -/
def boolOrJoinAlgebra : RuntimeJoinAlgebra where
  Carrier := Bool
  join := (· || ·)
  join_comm := by
    intro a b
    cases a <;> cases b <;> rfl
  join_assoc := by
    intro a b c
    cases a <;> cases b <;> cases c <;> rfl

/-- Runtime `set_union`: content-addressed set accumulation. -/
def setUnionJoinAlgebra : RuntimeJoinAlgebra where
  Carrier := Finset Nat
  join := (· ∪ ·)
  join_comm := by
    intro a b
    exact Finset.union_comm a b
  join_assoc := by
    intro a b c
    exact Finset.union_assoc a b c

/-! ### Product algebra for mixed runtime surfaces -/

/-- Product of two runtime join algebras.  This is the missing bridge for mixed
runtime graph surfaces: a surface with multiple independent label operators is
the pointwise product of homogeneous label families. -/
def productJoinAlgebra (A B : RuntimeJoinAlgebra) : RuntimeJoinAlgebra where
  Carrier := A.Carrier × B.Carrier
  join := fun left right =>
    (A.join left.1 right.1, B.join left.2 right.2)
  join_comm := by
    intro left right
    apply Prod.ext
    · exact A.join_comm left.1 right.1
    · exact B.join_comm left.2 right.2
  join_assoc := by
    intro left mid right
    apply Prod.ext
    · exact A.join_assoc left.1 mid.1 right.1
    · exact B.join_assoc left.2 mid.2 right.2

theorem productJoinAlgebra_comm (A B : RuntimeJoinAlgebra)
    (left right : (productJoinAlgebra A B).Carrier) :
    (productJoinAlgebra A B).join left right =
      (productJoinAlgebra A B).join right left :=
  (productJoinAlgebra A B).join_comm left right

theorem productJoinAlgebra_assoc (A B : RuntimeJoinAlgebra)
    (left mid right : (productJoinAlgebra A B).Carrier) :
    (productJoinAlgebra A B).join
        ((productJoinAlgebra A B).join left mid) right =
      (productJoinAlgebra A B).join left
        ((productJoinAlgebra A B).join mid right) :=
  (productJoinAlgebra A B).join_assoc left mid right

/-- Product algebra for the six `_join_label` operators used by the Python
runtime graph certificate. -/
def mixedRuntimeJoinAlgebra : RuntimeJoinAlgebra :=
  productJoinAlgebra noisyOrJoinAlgebra
    (productJoinAlgebra maxJoinAlgebra
      (productJoinAlgebra sumJoinAlgebra
        (productJoinAlgebra statusJoinAlgebra
          (productJoinAlgebra boolOrJoinAlgebra setUnionJoinAlgebra))))

/-! ## Generic runtime graph step -/

variable {EventId Key : Type}
variable [DecidableEq EventId] [DecidableEq Key]

/-- A single graph event for one label algebra.  Multi-operator runtime
surfaces are products of this construction, one homogeneous label family at a
time. -/
structure RuntimeGraphEvent (A : RuntimeJoinAlgebra) where
  edges : Finset Key
  touched : Finset Key
  value : Key → A.Carrier

/-- Graph state for a fixed event environment. -/
@[ext]
structure RuntimeGraphState (A : RuntimeJoinAlgebra) where
  pending : Finset EventId
  edges : Finset Key
  labels : Key → A.Carrier

namespace RuntimeGraph

variable {A : RuntimeJoinAlgebra}

def updateLabels (labels : Key → A.Carrier) (event : RuntimeGraphEvent (Key := Key) A) :
    Key → A.Carrier :=
  fun key =>
    if key ∈ event.touched then
      A.join (labels key) (event.value key)
    else
      labels key

def consumeEvent (events : EventId → RuntimeGraphEvent (Key := Key) A)
    (state : RuntimeGraphState (EventId := EventId) (Key := Key) A)
    (eventId : EventId) : RuntimeGraphState (EventId := EventId) (Key := Key) A where
  pending := state.pending.erase eventId
  edges := state.edges ∪ (events eventId).edges
  labels := updateLabels state.labels (events eventId)

/-- One runtime rewrite step: consume one pending event. -/
def step (events : EventId → RuntimeGraphEvent (Key := Key) A)
    (source target : RuntimeGraphState (EventId := EventId) (Key := Key) A) : Prop :=
  ∃ eventId, eventId ∈ source.pending ∧ target = consumeEvent events source eventId

theorem updateLabels_comm (labels : Key → A.Carrier)
    (left right : RuntimeGraphEvent (Key := Key) A) :
    updateLabels (updateLabels labels left) right =
      updateLabels (updateLabels labels right) left := by
  funext key
  unfold updateLabels
  by_cases hl : key ∈ left.touched <;> by_cases hr : key ∈ right.touched <;>
    simp [hl, hr, RuntimeJoinAlgebra.join_right_comm]

theorem consumeEvent_comm (events : EventId → RuntimeGraphEvent (Key := Key) A)
    (state : RuntimeGraphState (EventId := EventId) (Key := Key) A)
    (leftId rightId : EventId) :
    consumeEvent events (consumeEvent events state leftId) rightId =
      consumeEvent events (consumeEvent events state rightId) leftId := by
  apply RuntimeGraphState.ext
  · ext eventId
    simp only [consumeEvent, Finset.mem_erase]
    tauto
  · ext edge
    simp only [consumeEvent, Finset.mem_union]
    tauto
  · funext key
    exact congrFun (updateLabels_comm state.labels (events leftId) (events rightId)) key

theorem step_card_decreases (events : EventId → RuntimeGraphEvent (Key := Key) A)
    {source target : RuntimeGraphState (EventId := EventId) (Key := Key) A}
    (h : step events source target) :
    target.pending.card < source.pending.card := by
  rcases h with ⟨eventId, hmem, rfl⟩
  rw [consumeEvent]
  rw [Finset.card_erase_of_mem hmem]
  exact Nat.sub_one_lt (Nat.ne_of_gt (Finset.card_pos.mpr ⟨eventId, hmem⟩))

theorem terminating_step (events : EventId → RuntimeGraphEvent (Key := Key) A) :
    Terminating (step events) := by
  unfold Terminating
  exact (InvImage.wf
    (fun state : RuntimeGraphState (EventId := EventId) (Key := Key) A =>
      state.pending.card)
    wellFounded_lt).mono (by
      intro target source h
      exact step_card_decreases events h)

def criticalPair (events : EventId → RuntimeGraphEvent (Key := Key) A)
    (source left right : RuntimeGraphState (EventId := EventId) (Key := Key) A) :
    Prop :=
  ∃ leftId rightId,
    leftId ∈ source.pending ∧
    rightId ∈ source.pending ∧
    left = consumeEvent events source leftId ∧
    right = consumeEvent events source rightId

theorem critical_covers (events : EventId → RuntimeGraphEvent (Key := Key) A) :
    ∀ source left right,
      step events source left →
      step events source right →
      criticalPair events source left right := by
  intro source left right hleft hright
  rcases hleft with ⟨leftId, hleftMem, hleftEq⟩
  rcases hright with ⟨rightId, hrightMem, hrightEq⟩
  exact ⟨leftId, rightId, hleftMem, hrightMem, hleftEq, hrightEq⟩

theorem critical_joinable (events : EventId → RuntimeGraphEvent (Key := Key) A) :
    ∀ source left right,
      criticalPair events source left right →
      Joinable (step events) left right := by
  intro source left right hcrit
  rcases hcrit with ⟨leftId, rightId, hleftMem, hrightMem, rfl, rfl⟩
  by_cases hsame : leftId = rightId
  · subst rightId
    exact ⟨consumeEvent events source leftId, ReflTransGen.refl, ReflTransGen.refl⟩
  · let joined := consumeEvent events (consumeEvent events source leftId) rightId
    have hrightPending : rightId ∈ (consumeEvent events source leftId).pending := by
      have hrightNeLeft : rightId ≠ leftId := fun h => hsame h.symm
      simp [consumeEvent, Finset.mem_erase, hrightNeLeft, hrightMem]
    have hleftPending : leftId ∈ (consumeEvent events source rightId).pending := by
      simp [consumeEvent, Finset.mem_erase, hsame, hleftMem]
    have hcomm :
        consumeEvent events (consumeEvent events source rightId) leftId = joined := by
      unfold joined
      exact consumeEvent_comm events source rightId leftId
    refine ⟨joined, ?_, ?_⟩
    · exact ReflTransGen.single ⟨rightId, hrightPending, rfl⟩
    · exact ReflTransGen.single ⟨leftId, hleftPending, hcomm.symm⟩

def runtimeCriticalPairCertificate
    (events : EventId → RuntimeGraphEvent (Key := Key) A) :
    CriticalPairCertificate (step events) where
  critical := criticalPair events
  covers := critical_covers events
  joinable := critical_joinable events

/-- The Lean-readable bridge object: a concrete graph runtime step, its
termination proof, and its critical-pair certificate. -/
def runtimeNewmanGraphConfluenceCertificate
    (events : EventId → RuntimeGraphEvent (Key := Key) A) :
    NewmanGraphConfluenceCertificate
      (RuntimeGraphState (EventId := EventId) (Key := Key) A) where
  step := step events
  terminating := terminating_step events
  criticalPairs := runtimeCriticalPairCertificate events

theorem runtime_graph_confluent
    (events : EventId → RuntimeGraphEvent (Key := Key) A) :
    Confluent (step events) :=
  graph_confluent_of_newman_certificate
    (runtimeNewmanGraphConfluenceCertificate events)

end RuntimeGraph

/-! ## Named bridge instances for the six Python `_join_label` operators -/

def noisyOrNewmanCertificate
    (events : EventId → RuntimeGraphEvent (Key := Key) noisyOrJoinAlgebra) :
    NewmanGraphConfluenceCertificate
      (RuntimeGraphState (EventId := EventId) (Key := Key) noisyOrJoinAlgebra) :=
  RuntimeGraph.runtimeNewmanGraphConfluenceCertificate events

def maxNewmanCertificate
    (events : EventId → RuntimeGraphEvent (Key := Key) maxJoinAlgebra) :
    NewmanGraphConfluenceCertificate
      (RuntimeGraphState (EventId := EventId) (Key := Key) maxJoinAlgebra) :=
  RuntimeGraph.runtimeNewmanGraphConfluenceCertificate events

def sumNewmanCertificate
    (events : EventId → RuntimeGraphEvent (Key := Key) sumJoinAlgebra) :
    NewmanGraphConfluenceCertificate
      (RuntimeGraphState (EventId := EventId) (Key := Key) sumJoinAlgebra) :=
  RuntimeGraph.runtimeNewmanGraphConfluenceCertificate events

def statusNewmanCertificate
    (events : EventId → RuntimeGraphEvent (Key := Key) statusJoinAlgebra) :
    NewmanGraphConfluenceCertificate
      (RuntimeGraphState (EventId := EventId) (Key := Key) statusJoinAlgebra) :=
  RuntimeGraph.runtimeNewmanGraphConfluenceCertificate events

def boolOrNewmanCertificate
    (events : EventId → RuntimeGraphEvent (Key := Key) boolOrJoinAlgebra) :
    NewmanGraphConfluenceCertificate
      (RuntimeGraphState (EventId := EventId) (Key := Key) boolOrJoinAlgebra) :=
  RuntimeGraph.runtimeNewmanGraphConfluenceCertificate events

def setUnionNewmanCertificate
    (events : EventId → RuntimeGraphEvent (Key := Key) setUnionJoinAlgebra) :
    NewmanGraphConfluenceCertificate
      (RuntimeGraphState (EventId := EventId) (Key := Key) setUnionJoinAlgebra) :=
  RuntimeGraph.runtimeNewmanGraphConfluenceCertificate events

/-- Lean-readable Newman certificate for a mixed graph surface whose labels are
the product of the six runtime join algebras. -/
def mixedSurfaceNewmanCertificate
    (events : EventId → RuntimeGraphEvent (Key := Key) mixedRuntimeJoinAlgebra) :
    NewmanGraphConfluenceCertificate
      (RuntimeGraphState (EventId := EventId) (Key := Key) mixedRuntimeJoinAlgebra) :=
  RuntimeGraph.runtimeNewmanGraphConfluenceCertificate events

/-- Mixed runtime surfaces are confluent for arbitrary finite event
environments once their labels are expressed in the product algebra. -/
theorem mixed_surface_graph_confluent
    (events : EventId → RuntimeGraphEvent (Key := Key) mixedRuntimeJoinAlgebra) :
    Confluent (RuntimeGraph.step events) :=
  RuntimeGraph.runtime_graph_confluent events

/-!
  Boundary:
  - This module proves the operator algebra for arbitrary finite event
    environments using either one homogeneous label algebra or the product of
    the six runtime label algebras.
  - The Python certificate owns the mechanism-faithfulness check that a surface
    uses only these declared ops and rejects mixed-op updates for one label key.
-/
