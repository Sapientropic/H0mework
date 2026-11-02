import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Family.Migration.Posting.Balance

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Family.Migration.Share
open ResponsibilityLifecycle
variable {Party Good Port Technology Instrument Index : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (sources : Index → ProgrammeSource.Input Party Good Port Technology Instrument)

structure Split (balance : Shares (Party := Party)) where
  selected : Shares (Party := Party)
  remainder : Shares (Party := Party)
  selected_nonnegative : ∀ party, 0 ≤ selected party
  remainder_nonnegative : ∀ party, 0 ≤ remainder party
  exact : selected + remainder = balance

namespace Split
variable {sources} {balance : Shares (Party := Party)} (split : Split balance)

omit [DecidableEq Party] in
theorem pointwise (party : Party) : split.selected party + split.remainder party = balance party :=
  congrArg (fun shares : Shares (Party := Party) => shares party) split.exact

omit [DecidableEq Party] in
theorem nonnegative (split : Split balance) (party : Party) : 0 ≤ balance party := by
  rw [← split.pointwise party]
  exact add_nonneg (split.selected_nonnegative party) (split.remainder_nonnegative party)

def used (_split : Split balance) (sender : Party) (cap : ℚ) : ℚ := min cap (balance sender)

/-- This is a refinement of the fixed actual allocation, not another allocator.
Selected shares are transported first; the independent remainder pays the rest. -/
def selectedUsed (sender : Party) (cap : ℚ) : ℚ := min (split.used sender cap) (split.selected sender)
def remainderUsed (sender : Party) (cap : ℚ) : ℚ := split.used sender cap - split.selectedUsed sender cap

omit [DecidableEq Party] in
theorem quota (sender : Party) (cap : ℚ) :
    split.selectedUsed sender cap + split.remainderUsed sender cap = split.used sender cap := by
  unfold remainderUsed; ring

omit [DecidableEq Party] in
theorem covered (sender : Party) (cap : ℚ) (available : 0 ≤ cap) :
    0 ≤ split.selectedUsed sender cap ∧ split.selectedUsed sender cap ≤ split.selected sender ∧
      0 ≤ split.remainderUsed sender cap ∧ split.remainderUsed sender cap ≤ split.remainder sender := by
  have positive : 0 ≤ split.used sender cap := le_min available (split.nonnegative sender)
  have bounded : split.used sender cap ≤ balance sender := min_le_right _ _
  have original := split.pointwise sender
  refine ⟨le_min positive (split.selected_nonnegative sender), min_le_right _ _,
    sub_nonneg.mpr (min_le_left _ _), ?_⟩
  rcases le_total (split.used sender cap) (split.selected sender) with left | right
  · simp only [remainderUsed, selectedUsed, min_eq_left left, sub_self]
    exact split.remainder_nonnegative sender
  · simp only [remainderUsed, selectedUsed, min_eq_right right]
    linarith

def move (claim : Claim sources) (review : Review sources claim) (shares : Shares (Party := Party))
    (quantity : ℚ) : Shares (Party := Party) :=
  match review.kind with
  | .payment => pay (sources claim.1) shares review.sender quantity
  | .assignment => assign (sources claim.1) shares review.sender review.recipient quantity

def step {claim : Claim sources} (review : Review sources claim) (cap : ℚ) (available : 0 ≤ cap) :
    Split (review.after sources balance cap) where
  selected := move claim review split.selected (split.selectedUsed review.sender cap)
  remainder := move claim review split.remainder (split.remainderUsed review.sender cap)
  selected_nonnegative := by
    have bounded := split.covered review.sender cap available
    cases kind : review.kind <;> simp only [move,kind]
    · exact pay_nonnegative (sources claim.1) _ _ _ split.selected_nonnegative bounded.2.1
    · exact assign_nonnegative (sources claim.1) _ _ _ _ split.selected_nonnegative bounded.1 bounded.2.1
  remainder_nonnegative := by
    have bounded := split.covered review.sender cap available
    cases kind : review.kind <;> simp only [move,kind]
    · exact pay_nonnegative (sources claim.1) _ _ _ split.remainder_nonnegative bounded.2.2.2
    · exact assign_nonnegative (sources claim.1) _ _ _ _ split.remainder_nonnegative bounded.2.2.1 bounded.2.2.2
  exact := by
    apply Finsupp.ext
    intro party
    have original := split.pointwise party
    have quantity := split.quota review.sender cap
    cases kind : review.kind <;>
      simp only [move, Review.after, kind, Finsupp.add_apply, pay_apply, assign_apply] <;>
      split_ifs <;> dsimp only [used] at quantity <;> linarith

def retired (reviewKind : MovementKind) (quantity : ℚ) : ℚ :=
  match reviewKind with | .payment => quantity | .assignment => 0

omit [DecidableEq Port] in
theorem selected_conservation {claim : Claim sources} (review : Review sources claim)
    (cap : ℚ) (available : 0 ≤ cap) (input : Index) :
    Financial.total (sources input) (split.step review cap available).selected +
      retired review.kind (split.selectedUsed review.sender cap) = Financial.total (sources input) split.selected := by
  cases kind : review.kind <;> simp only [step,move,kind,retired]
  · change Financial.total (sources claim.1) (pay (sources claim.1) _ _ _) + _ = Financial.total (sources claim.1) _
    rw [Financial.pay_total]; ring
  · change Financial.total (sources claim.1) (assign (sources claim.1) _ _ _ _) + 0 = Financial.total (sources claim.1) _
    rw [Financial.assign_total, add_zero]

omit [DecidableEq Port] in
theorem remainder_conservation {claim : Claim sources} (review : Review sources claim)
    (cap : ℚ) (available : 0 ≤ cap) (input : Index) :
    Financial.total (sources input) (split.step review cap available).remainder +
      retired review.kind (split.remainderUsed review.sender cap) = Financial.total (sources input) split.remainder := by
  cases kind : review.kind <;> simp only [step,move,kind,retired]
  · change Financial.total (sources claim.1) (pay (sources claim.1) _ _ _) + _ = Financial.total (sources claim.1) _
    rw [Financial.pay_total]; ring
  · change Financial.total (sources claim.1) (assign (sources claim.1) _ _ _ _) + 0 = Financial.total (sources claim.1) _
    rw [Financial.assign_total, add_zero]

def reindex {other : Shares (Party := Party)} (same : balance = other) : Split other :=
  ⟨split.selected,split.remainder,split.selected_nonnegative,split.remainder_nonnegative,split.exact.trans same⟩

end Split

structure Flow {first last : ObligationSlot (vocabulary sources)}
    (path : Path sources first last) (initial : Split (slotBalance sources first)) where
  final : Split (slotBalance sources last)
  selectedPaid : ℚ
  remainderPaid : ℚ
  selectedPaid_nonnegative : 0 ≤ selectedPaid
  remainderPaid_nonnegative : 0 ≤ remainderPaid
  paid_exact : selectedPaid + remainderPaid = path.paid sources
  selected_conservation : ∀ input, Financial.total (sources input) final.selected + selectedPaid =
    Financial.total (sources input) initial.selected
  remainder_conservation : ∀ input, Financial.total (sources input) final.remainder + remainderPaid =
    Financial.total (sources input) initial.remainder

def transport {first last : ObligationSlot (vocabulary sources)}
    (path : Path sources first last) (initial : Split (slotBalance sources first)) : Flow sources path initial :=
  match path with
  | .nil _ => ⟨initial,0,0,le_rfl,le_rfl,by simp [Path.paid,Path.events],fun _ => add_zero _,fun _ => add_zero _⟩
  | .snoc prior boundary => by
    let previous := transport prior initial
    let next := previous.final.step boundary.receipt boundary.cap boundary.available
    have exactBalance := boundary_balance sources boundary
    let final : Split (slotBalance sources (Boundary.disposition sources boundary).targetSlot) :=
      next.reindex exactBalance.symm
    let paid := Split.retired boundary.receipt.kind (previous.final.selectedUsed boundary.receipt.sender boundary.cap)
    let rest := Split.retired boundary.receipt.kind (previous.final.remainderUsed boundary.receipt.sender boundary.cap)
    have quota := previous.final.quota boundary.receipt.sender boundary.cap
    have covered := previous.final.covered boundary.receipt.sender boundary.cap boundary.available
    refine ⟨final,previous.selectedPaid + paid,previous.remainderPaid + rest,?_,?_,?_,?_,?_⟩
    · apply add_nonneg previous.selectedPaid_nonnegative
      cases kind : boundary.receipt.kind <;> simp only [paid,Split.retired,kind]
      · exact covered.1
      · exact le_rfl
    · apply add_nonneg previous.remainderPaid_nonnegative
      cases kind : boundary.receipt.kind <;> simp only [rest,Split.retired,kind]
      · exact covered.2.2.1
      · exact le_rfl
    · have old := previous.paid_exact
      change _ = ((prior.events sources ++ [boundary.event sources]).map (retired sources)).sum
      simp only [List.map_append,List.sum_append,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero]
      change _ = prior.paid sources + retired sources (boundary.event sources)
      dsimp only [Split.used,slotBalance] at quota
      cases kind : boundary.receipt.kind <;> simp only [paid,rest,Split.retired,kind,retired,Boundary.event]
      · calc
          _ = (previous.selectedPaid + previous.remainderPaid) +
              (previous.final.selectedUsed boundary.receipt.sender boundary.cap +
                previous.final.remainderUsed boundary.receipt.sender boundary.cap) := by ring
          _ = _ := congrArg₂ (fun a b : ℚ => a + b) old quota
      · simpa only [add_zero] using old
    · intro input
      have old := previous.selected_conservation input
      have step := previous.final.selected_conservation boundary.receipt boundary.cap boundary.available input
      have same : final.selected = next.selected := by rfl
      rw [same]; change Financial.total (sources input) next.selected + (previous.selectedPaid + paid) = _
      linarith
    · intro input
      have old := previous.remainder_conservation input
      have step := previous.final.remainder_conservation boundary.receipt boundary.cap boundary.available input
      have same : final.remainder = next.remainder := by rfl
      rw [same]; change Financial.total (sources input) next.remainder + (previous.remainderPaid + rest) = _
      linarith

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Family.Migration.Share
