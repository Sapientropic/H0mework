import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Family.Embedding

import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Migration

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Family.Embedding

open ResponsibilityLifecycle

variable {Party Good Port Technology Instrument Index : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (sources : Index → ProgrammeSource.Input Party Good Port Technology Instrument) (index : Index)

structure Realization (original : (Financial.process (sources index)).GeneratedState) where
  account : (process sources).GeneratedState
  exact_state : account.current = state sources index original.current

def Realization.initial : Realization sources index (.initial (Financial.process (sources index))) :=
  ⟨.initial (process sources), rfl⟩

def Realization.admit {original : (Financial.process (sources index)).GeneratedState}
    (realized : Realization sources index original) (claim : IssuedClaim (sources index)) :
    Realization sources index (Financial.admit (sources index) original claim) where
  account := Family.admit sources realized.account ⟨index, claim⟩
  exact_state := by
    change ({ slots := realized.account.current.slots ++ [_], history := realized.account.current.history ++ [_] } : ResponsibilityState (vocabulary sources)) = _
    rw [realized.exact_state]
    simp only [state, Financial.admit, NativeResponsibilityProcess.GeneratedState.step,
      NativeResponsibilityProcess.Edge.target, NativeResponsibilityProcess.Edge.lifecycleEvent,
      process, Financial.process, List.length_map, List.map_append, List.map_cons, List.map_nil,
      slot, obligation_admission, record, payload_admission]

theorem obligation_coherent (original : AdmittedObligation (Financial.vocabulary (sources index)))
    (coherent : Financial.Coherent (sources index) original) :
    Coherent sources (obligation sources index original) := by
  refine ⟨?_, congrArg (Sigma.mk index) coherent.2.1,
    congrArg (Sigma.mk index) coherent.2.2.1, congrArg (Sigma.mk index) coherent.2.2.2⟩
  change (event sources index original.admission.sourceEvent).claim sources = _
  rw [event_claim]
  exact congrArg (Sigma.mk index) coherent.1

def boundary (original : AdmittedObligation (Financial.vocabulary (sources index)))
    (coherent : Financial.Coherent (sources index) original)
    (receipt : Financial.Review (sources index) original.content) (cap : ℚ)
    (positive : Financial.Nonnegative (sources index) original.residual)
    (available : 0 ≤ cap) (within : cap ≤ receipt.quantity) : Boundary sources (obligation sources index original) :=
  reviewBoundary sources (obligation sources index original) (Review.ofOriginal sources index receipt)
    cap positive available within (obligation_coherent sources index original coherent)

theorem boundary_target (original : AdmittedObligation (Financial.vocabulary (sources index)))
    (coherent : Financial.Coherent (sources index) original)
    (receipt : Financial.Review (sources index) original.content) (cap : ℚ)
    (positive : Financial.Nonnegative (sources index) original.residual)
    (available : 0 ≤ cap) (within : cap ≤ receipt.quantity) :
    (Boundary.disposition sources (boundary sources index original coherent receipt cap positive available within)).targetSlot =
      slot sources index (Financial.boundaryDisposition (sources index)
        (Financial.reviewBoundary (sources index) original coherent receipt cap positive available within)).targetSlot := by
  rcases receipt with ⟨receiptOrigin, instruction, originalEq, kind, quantity, operation, accepted⟩
  cases kind <;> unfold Boundary.disposition
  all_goals split
  all_goals unfold Financial.boundaryDisposition
  all_goals first
    | (rw [dif_pos (by assumption)]; rfl)
    | (rw [dif_neg (by assumption)]; rfl)

theorem boundary_record (position : Nat) (original : AdmittedObligation (Financial.vocabulary (sources index)))
    (coherent : Financial.Coherent (sources index) original)
    (receipt : Financial.Review (sources index) original.content) (cap : ℚ)
    (positive : Financial.Nonnegative (sources index) original.residual)
    (available : 0 ≤ cap) (within : cap ≤ receipt.quantity) :
    Family.Migration.record sources position (boundary sources index original coherent receipt cap positive available within) =
      record sources index (Financial.Migration.record (sources index) position
        (Financial.reviewBoundary (sources index) original coherent receipt cap positive available within)) := by
  by_cases cleared : receipt.after (sources index) original.residual cap = 0
  all_goals rcases receipt with ⟨receiptOrigin, instruction, originalEq, kind, quantity, operation, accepted⟩
  all_goals cases kind
  all_goals unfold Family.Migration.record Boundary.disposition Financial.Migration.record
  all_goals first
    | (rw [dif_pos (by assumption), dif_pos (by assumption)]; rfl)
    | (rw [dif_neg (by assumption), dif_neg (by assumption)]; rfl)

def Realization.allocateLive {original : (Financial.process (sources index)).GeneratedState}
    (realized : Realization sources index original) (position : Fin original.current.slots.length)
    (originalObligation : AdmittedObligation (Financial.vocabulary (sources index)))
    (present : original.current.slots.get position = .live originalObligation)
    (receipt : Financial.Review (sources index) originalObligation.content)
    (available : ℚ) (nonnegative : 0 ≤ available) :
    Realization sources index (Financial.allocateLive (sources index) original position originalObligation present receipt available nonnegative).after := by
  let sound := Financial.live_sound (sources index) original position originalObligation present
  let cap := min available receipt.quantity
  let positive := le_min nonnegative (receipt.quantity_nonnegative _)
  let edgeBoundary := boundary sources index originalObligation sound.1 receipt cap sound.2 positive (min_le_right _ _)
  let targetPosition : Fin realized.account.current.slots.length := ⟨position.val, by
    rw [realized.exact_state]
    simpa only [state, List.length_map] using position.isLt⟩
  have targetPresent : realized.account.current.slots.get targetPosition =
      .live (obligation sources index originalObligation) := by
    have mapped := congrArg (slot sources index) present
    simpa only [realized.exact_state, state, List.get_eq_getElem, List.getElem_map, slot] using mapped
  refine ⟨Family.cross sources realized.account targetPosition (obligation sources index originalObligation) targetPresent edgeBoundary, ?_⟩
  apply congrArg₂ ResponsibilityState.mk
  · change realized.account.current.slots.set position.val (Boundary.disposition sources edgeBoundary).targetSlot =
      (original.current.slots.set position.val _).map (slot sources index)
    rw [List.map_set, boundary_target]
    rw [show realized.account.current.slots = original.current.slots.map (slot sources index) from
      congrArg ResponsibilityState.slots realized.exact_state]
    rfl
  · change realized.account.current.history ++ [_] = (original.current.history ++ [_]).map (record sources index)
    rw [List.map_append]
    simp only [List.map_cons, List.map_nil]
    rw [Family.Migration.cross_record, Financial.Migration.cross_record, boundary_record]
    rw [show realized.account.current.history = original.current.history.map (record sources index) from
      congrArg ResponsibilityState.history realized.exact_state]

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Family.Embedding
