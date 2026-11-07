import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance.Family.Nonnegative
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance.Family.Embedding.Boundary
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance.Invariants

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance.Family

open ResponsibilityLifecycle
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root

noncomputable section

variable {Party Good Port Technology Instrument Index : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (sources : Index → ProgrammeSource.Input Party Good Port Technology Instrument)
  (depths counts : Index → Nat)

def Coherent (obligation : AdmittedObligation (vocabulary sources depths counts)) : Prop :=
  obligation.admission.sourceEvent.claim sources depths counts = obligation.content ∧
  obligation.scope = claimOrigin sources depths counts obligation.content ∧
  obligation.beneficiary = obligation.content ∧ obligation.bearer = claimActor sources depths counts obligation.content

def slotObligation : ObligationSlot (vocabulary sources depths counts) → AdmittedObligation (vocabulary sources depths counts)
  | .live obligation => obligation
  | .terminal archive => archive.obligation

def slotClaim (slot : ObligationSlot (vocabulary sources depths counts)) := (slotObligation sources depths counts slot).content

def slotBalance : ObligationSlot (vocabulary sources depths counts) → Balance (Party := Party)
  | .live obligation => obligation.residual
  | .terminal _ => 0

def SlotSound (slot : ObligationSlot (vocabulary sources depths counts)) : Prop :=
  Coherent sources depths counts (slotObligation sources depths counts slot) ∧
    ∀ holder, 0 ≤ slotBalance sources depths counts slot holder

def Sound (state : ResponsibilityState (vocabulary sources depths counts)) : Prop :=
  ∀ slot ∈ state.slots, SlotSound sources depths counts slot

theorem Embedding.obligation_coherent (index : Index)
    (original : AdmittedObligation (Finance.vocabulary (sources index) (depths index) (counts index)))
    (coherent : Finance.Coherent (sources index) (depths index) (counts index) original) :
    Coherent sources depths counts (Embedding.obligation sources depths counts index original) :=
  ⟨congrArg (Sigma.mk index) coherent.1, congrArg (Sigma.mk index) coherent.2.1,
    congrArg (Sigma.mk index) coherent.2.2.1, congrArg (Sigma.mk index) coherent.2.2.2⟩

theorem admission_sound (claim : Claim sources depths counts) :
    SlotSound sources depths counts (.live (admission sources depths counts claim).toObligation) := by
  rcases claim with ⟨index, claim⟩
  have original := Finance.admission_sound (sources index) (depths index) (counts index) claim
  refine ⟨?_, original.2⟩
  rw [← Embedding.obligation_admission]
  exact Embedding.obligation_coherent sources depths counts index _ original.1

theorem boundary_sound {obligation : AdmittedObligation (vocabulary sources depths counts)}
    (boundary : Boundary sources depths counts obligation) (coherent : Coherent sources depths counts obligation) :
    SlotSound sources depths counts (boundaryDisposition sources depths counts boundary).targetSlot := by
  unfold boundaryDisposition
  split
  · exact ⟨coherent, fun _ => le_refl 0⟩
  · exact ⟨coherent, boundary.event.after_nonnegative sources depths counts boundary.lawful⟩

theorem edge_sound {state : ResponsibilityState (vocabulary sources depths counts)}
    (sound : Sound sources depths counts state) (edge : (process sources depths counts).Edge state) :
    Sound sources depths counts edge.target := by
  intro slot member
  cases edge with
  | admit claim =>
      rcases List.mem_append.mp member with old | fresh
      · exact sound slot old
      · have same : slot = .live (admission sources depths counts claim).toObligation :=
          by simpa only [List.mem_singleton, process] using fresh
        exact same ▸ admission_sound sources depths counts claim
  | cross position obligation present boundary =>
      rcases List.mem_or_eq_of_mem_set member with old | changed
      · exact sound slot old
      · subst slot
        exact boundary_sound sources depths counts boundary
          (sound (.live obligation) (present ▸ List.get_mem state.slots position)).1
  | reopen _ _ _ impossible => exact impossible.elim

theorem generated_sound (state : (process sources depths counts).GeneratedState) : Sound sources depths counts state.current := by
  rcases state with ⟨state, generated⟩
  induction generated with
  | nil => exact fun _ member => (List.not_mem_nil member).elim
  | step prior edge inherited => exact edge_sound sources depths counts inherited edge

theorem live_sound (state : (process sources depths counts).GeneratedState)
    (position : Fin state.current.slots.length) (obligation : AdmittedObligation (vocabulary sources depths counts))
    (present : state.current.slots.get position = .live obligation) :
    Coherent sources depths counts obligation ∧ (∀ holder, 0 ≤ obligation.residual holder) :=
  generated_sound sources depths counts state (.live obligation) (present ▸ List.get_mem state.current.slots position)

#print axioms generated_sound

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance.Family
