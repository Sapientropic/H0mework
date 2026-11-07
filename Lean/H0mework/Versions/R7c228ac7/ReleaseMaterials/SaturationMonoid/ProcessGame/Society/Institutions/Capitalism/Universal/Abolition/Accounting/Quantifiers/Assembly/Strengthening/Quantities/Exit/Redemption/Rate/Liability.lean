import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance.Family.Allocation.Scan

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Exit.Redemption.Rate

open ResponsibilityLifecycle Abolition.Root
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Epoch.Finance.Family

noncomputable section

variable {Party Good Port Technology Instrument Index : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (sources : Index → ProgrammeSource.Input Party Good Port Technology Instrument)
  (depths counts : Index → Nat)

theorem an_actual_movement_at_a_changed_rate_cannot_review_the_original_claim
    (claim : Claim sources depths counts) (origin : ActualItem sources depths counts)
    (movement : Epoch.Finance.Movement (sources origin.1) (depths origin.1) (counts origin.1) origin.2)
    (actual : Epoch.Finance.readMovement (sources origin.1) (depths origin.1) (counts origin.1) origin.2 = some movement)
    (mismatch : (sources origin.1).law.settlementRate movement.instrument ≠
      (sources claim.1).law.settlementRate movement.instrument) :
    readReview sources depths counts claim origin = none := by
  unfold readReview
  rw [actual]
  dsimp only
  split
  · split
    · split
      · rfl
      · rfl
    · rfl
  · rfl

/-- The original live slot retains the same obligation and the attempted
movement keeps its unused quota at that slot. -/
theorem a_changed_rate_preserves_the_exact_original_slot_and_unused_quota
    (state : (process sources depths counts).GeneratedState) (position : Fin state.current.slots.length)
    (old : AdmittedObligation (vocabulary sources depths counts)) (original : state.current.slots.get position = .live old)
    (origin : ActualItem sources depths counts)
    (movement : Epoch.Finance.Movement (sources origin.1) (depths origin.1) (counts origin.1) origin.2)
    (actual : Epoch.Finance.readMovement (sources origin.1) (depths origin.1) (counts origin.1) origin.2 = some movement)
    (mismatch : (sources origin.1).law.settlementRate movement.instrument ≠
      (sources old.content.1).law.settlementRate movement.instrument) (quota : ℚ) (nonnegative : 0 ≤ quota) :
    let allocation := allocateAt sources depths counts origin state position.val quota nonnegative
    allocation.after = state ∧ allocation.remaining = quota := by
  have refused := an_actual_movement_at_a_changed_rate_cannot_review_the_original_claim
    sources depths counts old.content origin movement actual mismatch
  dsimp only
  have idle : allocateAt sources depths counts origin state position.val quota nonnegative =
      Allocation.idle sources depths counts state quota nonnegative := by
    unfold allocateAt
    rw [dif_pos position.isLt]
    split
    · rfl
    · rename_i obligation present
      have same : obligation = old := ObligationSlot.live.inj (present.symm.trans original)
      subst obligation
      rw [refused]
  rw [idle]
  exact ⟨rfl, rfl⟩

end

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Exit.Redemption.Rate
