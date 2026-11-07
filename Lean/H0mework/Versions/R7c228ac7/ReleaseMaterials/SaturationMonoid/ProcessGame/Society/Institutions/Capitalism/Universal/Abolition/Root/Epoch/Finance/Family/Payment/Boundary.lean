import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance.Family.Invariants

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance.Family

open ResponsibilityLifecycle
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root

noncomputable section

variable {Party Good Port Technology Instrument Index : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (sources : Index → ProgrammeSource.Input Party Good Port Technology Instrument)
  (depths counts : Index → Nat)

def reviewBoundary (obligation : AdmittedObligation (vocabulary sources depths counts))
    (coherent : Coherent sources depths counts obligation)
    (receipt : Review sources depths counts obligation.content) (cap : ℚ)
    (nonnegative : ∀ holder, 0 ≤ obligation.residual holder) (available : 0 ≤ cap)
    (within : cap ≤ receipt.movement.quantity) : Boundary sources depths counts obligation where
  event := .review obligation.content receipt obligation.residual cap
  lawful := ⟨nonnegative, available, within⟩
  content_eq := rfl
  before_eq := rfl
  owns := {
    anchor_eq := by
      change MinimalRegistrableSourceAnchor.canonical
        (claimOrigin sources depths counts obligation.content) (claimOrigin sources depths counts obligation.content) =
        MinimalRegistrableSourceAnchor.canonical
          (claimOrigin sources depths counts (obligation.admission.sourceEvent.claim sources depths counts))
          (claimOrigin sources depths counts (obligation.admission.sourceEvent.claim sources depths counts))
      rw [coherent.1]
    incidence_eq := by
      change claimOrigin sources depths counts obligation.content =
        claimOrigin sources depths counts (obligation.admission.sourceEvent.claim sources depths counts)
      rw [coherent.1] }
  scope_eq := coherent.2.1

theorem boundary_claim {obligation : AdmittedObligation (vocabulary sources depths counts)}
    (boundary : Boundary sources depths counts obligation) :
    slotClaim sources depths counts (boundaryDisposition sources depths counts boundary).targetSlot = obligation.content := by
  unfold boundaryDisposition
  split <;> rfl

theorem cross_retains_all_claims (state : (process sources depths counts).GeneratedState)
    (position : Fin state.current.slots.length) (obligation : AdmittedObligation (vocabulary sources depths counts))
    (present : state.current.slots.get position = .live obligation)
    (boundary : Boundary sources depths counts obligation) :
    (state.step (process sources depths counts) (.cross position obligation present boundary)).current.slots.map
      (slotClaim sources depths counts) = state.current.slots.map (slotClaim sources depths counts) := by
  change (state.current.slots.set position (boundaryDisposition sources depths counts boundary).targetSlot).map _ = _
  rw [List.map_set, boundary_claim]
  apply List.ext_getElem
  · simp
  · intro index left right
    rw [List.getElem_set]
    split
    · rename_i same
      subst index
      simpa only [List.getElem_map, List.get_eq_getElem, slotClaim, slotObligation] using
        (congrArg (slotClaim sources depths counts) present).symm
    · rfl

#print axioms reviewBoundary

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance.Family
