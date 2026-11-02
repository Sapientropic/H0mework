import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Family.Migration.AssignedFinancing

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 1200000

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Family.Migration.AssignedFinancing.Joint
open ResponsibilityLifecycle
variable {Party Good Port Technology Instrument Index : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (sources : Index → ProgrammeSource.Input Party Good Port Technology Instrument)

variable {obligation : AdmittedObligation (vocabulary sources)} (boundary : Boundary sources obligation)
  (before : Share.Split obligation.residual)

/-- Reacquired shares already selected at the sender are transported, not
selected a second time. Only the actual transferred remainder changes cohort. -/
def promote (origin : Open sources boundary) :
    Share.Split (slotBalance sources (Boundary.disposition sources boundary).targetSlot) := by
  let m := before.selectedUsed boundary.receipt.sender boundary.cap
  let q := before.remainderUsed boundary.receipt.sender boundary.cap
  have covered := before.covered boundary.receipt.sender boundary.cap boundary.available
  refine Share.Split.reindex (balance := (boundary.event sources).after sources)
    ⟨pay (sources obligation.content.1)
      (assign (sources obligation.content.1) before.selected boundary.receipt.sender boundary.receipt.recipient m)
      boundary.receipt.recipient (-q),
      pay (sources obligation.content.1) before.remainder boundary.receipt.sender q,?_,?_,?_⟩
    (boundary_balance sources boundary).symm
  · intro party
    have positive := assign_nonnegative (sources obligation.content.1) before.selected boundary.receipt.sender boundary.receipt.recipient m before.selected_nonnegative covered.1 covered.2.1
    apply pay_nonnegative (sources obligation.content.1) _ _ _ positive _ party
    have retained := positive boundary.receipt.recipient
    linarith [covered.2.2.1]
  · exact pay_nonnegative (sources obligation.content.1) _ _ _ before.remainder_nonnegative covered.2.2.2
  · apply Finsupp.ext
    intro party
    have original := before.pointwise party
    have quota := before.quota boundary.receipt.sender boundary.cap
    dsimp only [Share.Split.used] at quota
    simp only [Finsupp.add_apply,assign_apply,pay_apply,
      Family.Event.after,Boundary.event,Review.after,origin.assignment]
    split_ifs <;> (try dsimp only [m,q]) <;> linarith

structure Step where
  private mk ::
  final : Share.Split (slotBalance sources (Boundary.disposition sources boundary).targetSlot)
  fresh : ℚ
  fresh_nonnegative : 0 ≤ fresh
  fresh_le : fresh ≤ before.remainderUsed boundary.receipt.sender boundary.cap
  fresh_source : 0 < fresh → Nonempty (Open sources boundary)
  selected_conservation : ∀ input, Financial.total (sources input) final.selected +
    Share.Split.retired boundary.receipt.kind (before.selectedUsed boundary.receipt.sender boundary.cap) =
      Financial.total (sources input) before.selected + fresh
  remainder_conservation : ∀ input, Financial.total (sources input) final.remainder +
    Share.Split.retired boundary.receipt.kind (before.remainderUsed boundary.receipt.sender boundary.cap) + fresh =
      Financial.total (sources input) before.remainder

def withExplanations (explanations : List (Open sources boundary)) : Step sources boundary before :=
  match explanations with
  | [] =>
    ⟨(before.step boundary.receipt boundary.cap boundary.available).reindex (boundary_balance sources boundary).symm,
      0,le_rfl,(before.covered boundary.receipt.sender boundary.cap boundary.available).2.2.1,
      fun impossible => False.elim (lt_irrefl 0 impossible),
      fun input => by simpa only [Share.Split.reindex,add_zero] using before.selected_conservation boundary.receipt boundary.cap boundary.available input,
      fun input => by simpa only [Share.Split.reindex,add_zero] using before.remainder_conservation boundary.receipt boundary.cap boundary.available input⟩
  | origin :: _ => by
    let q := before.remainderUsed boundary.receipt.sender boundary.cap
    refine ⟨promote sources boundary before origin,q,
      (before.covered boundary.receipt.sender boundary.cap boundary.available).2.2.1,le_rfl,
      fun _ => ⟨origin⟩,?_,?_⟩
    · intro input
      change Financial.total (sources input)
        (pay (sources obligation.content.1)
          (assign (sources obligation.content.1) before.selected boundary.receipt.sender boundary.receipt.recipient
            (before.selectedUsed boundary.receipt.sender boundary.cap)) boundary.receipt.recipient (-q)) + _ = _
      simp only [origin.assignment,Share.Split.retired,add_zero]
      change Financial.total (sources obligation.content.1) (pay (sources obligation.content.1) _ _ _) =
        Financial.total (sources obligation.content.1) before.selected + q
      rw [Financial.pay_total,Financial.assign_total]
      dsimp only [Financial.total]
      ring
    · intro input
      change Financial.total (sources input)
        (pay (sources obligation.content.1) before.remainder boundary.receipt.sender q) + _ + q = _
      simp only [origin.assignment,Share.Split.retired,add_zero]
      change Financial.total (sources obligation.content.1) (pay (sources obligation.content.1) _ _ _) + q =
        Financial.total (sources obligation.content.1) before.remainder
      rw [Financial.pay_total]
      dsimp only [Financial.total]
      ring

def step : Step sources boundary before := withExplanations sources boundary before (origins sources boundary)

theorem duplicate_explanations_do_not_change_the_joint_step (explanations : List (Open sources boundary)) :
    withExplanations sources boundary before (explanations ++ explanations) =
      withExplanations sources boundary before explanations := by
  cases explanations <;> rfl

structure Entry where
  private mk ::
  obligation : AdmittedObligation (vocabulary sources)
  boundary : Boundary sources obligation
  before : Share.Split obligation.residual

namespace Entry

def ofBoundary {obligation : AdmittedObligation (vocabulary sources)}
    (boundary : Boundary sources obligation) (before : Share.Split obligation.residual) : Entry sources :=
  ⟨obligation,boundary,before⟩

variable {sources} (entry : Entry sources)
def event : Family.Event sources := entry.boundary.event sources
def result := step sources entry.boundary entry.before
def selectedPaid : ℚ := Share.Split.retired entry.boundary.receipt.kind
  (entry.before.selectedUsed entry.boundary.receipt.sender entry.boundary.cap)
def remainderPaid : ℚ := Share.Split.retired entry.boundary.receipt.kind
  (entry.before.remainderUsed entry.boundary.receipt.sender entry.boundary.cap)

theorem paid_exact : entry.selectedPaid + entry.remainderPaid = retired sources entry.event := by
  have quota := entry.before.quota entry.boundary.receipt.sender entry.boundary.cap
  dsimp only [Share.Split.used] at quota
  cases kind : entry.boundary.receipt.kind <;>
    simp only [selectedPaid,remainderPaid,Share.Split.retired,retired,event,Boundary.event,kind]
  · exact quota
  · exact add_zero 0

theorem paid_nonnegative : 0 ≤ entry.selectedPaid ∧ 0 ≤ entry.remainderPaid := by
  have covered := entry.before.covered entry.boundary.receipt.sender entry.boundary.cap entry.boundary.available
  cases kind : entry.boundary.receipt.kind <;> simp only [selectedPaid,remainderPaid,Share.Split.retired,kind]
  · exact ⟨covered.1,covered.2.2.1⟩
  · exact ⟨le_rfl,le_rfl⟩
end Entry

def selectedPaid (entries : List (Entry sources)) : ℚ := (entries.map Entry.selectedPaid).sum
def remainderPaid (entries : List (Entry sources)) : ℚ := (entries.map Entry.remainderPaid).sum
def acquired (entries : List (Entry sources)) : ℚ := (entries.map fun entry => entry.result.fresh).sum

structure Flow {first last : ObligationSlot (vocabulary sources)}
    (path : Path sources first last) (initial : Share.Split (slotBalance sources first)) where
  private mk ::
  final : Share.Split (slotBalance sources last)
  entries : List (Entry sources)
  events_exact : entries.map Entry.event = path.events sources
  selected_conservation : ∀ input, Financial.total (sources input) final.selected + selectedPaid sources entries =
    Financial.total (sources input) initial.selected + acquired sources entries
  remainder_conservation : ∀ input, Financial.total (sources input) final.remainder + remainderPaid sources entries + acquired sources entries =
    Financial.total (sources input) initial.remainder

def fold {first last : ObligationSlot (vocabulary sources)}
    (path : Path sources first last) (initial : Share.Split (slotBalance sources first)) : Flow sources path initial :=
  match path with
  | .nil _ => ⟨initial,[],rfl,fun _ => by simp [selectedPaid,acquired],fun _ => by simp [remainderPaid,acquired]⟩
  | .snoc prior boundary => by
    let previous := fold prior initial
    let entry : Entry sources := ⟨_,boundary,previous.final⟩
    refine ⟨entry.result.final,previous.entries ++ [entry],?_,?_,?_⟩
    · simp only [List.map_append,List.map_cons,List.map_nil,previous.events_exact,Path.events]
      rfl
    · intro input
      have old := previous.selected_conservation input
      have next := entry.result.selected_conservation input
      simp only [selectedPaid,acquired,List.map_append,List.map_cons,List.map_nil,
        List.sum_append,List.sum_cons,List.sum_nil,add_zero]
      change Financial.total (sources input) entry.result.final.selected +
        (selectedPaid sources previous.entries + entry.selectedPaid) =
          Financial.total (sources input) initial.selected + (acquired sources previous.entries + entry.result.fresh)
      change Financial.total (sources input) entry.result.final.selected + entry.selectedPaid =
        Financial.total (sources input) previous.final.selected + entry.result.fresh at next
      linarith
    · intro input
      have old := previous.remainder_conservation input
      have next := entry.result.remainder_conservation input
      simp only [remainderPaid,acquired,List.map_append,List.map_cons,List.map_nil,
        List.sum_append,List.sum_cons,List.sum_nil,add_zero]
      change Financial.total (sources input) entry.result.final.remainder +
        (remainderPaid sources previous.entries + entry.remainderPaid) +
        (acquired sources previous.entries + entry.result.fresh) = Financial.total (sources input) initial.remainder
      change Financial.total (sources input) entry.result.final.remainder + entry.remainderPaid + entry.result.fresh =
        Financial.total (sources input) previous.final.remainder at next
      linarith

namespace Flow
variable {sources} {first last : ObligationSlot (vocabulary sources)}
  {path : Path sources first last} {initial : Share.Split (slotBalance sources first)}
  (flow : Flow sources path initial)

theorem paid_exact : selectedPaid sources flow.entries + remainderPaid sources flow.entries = path.paid sources := by
  rw [Path.paid,← flow.events_exact,List.map_map]
  unfold selectedPaid remainderPaid
  induction flow.entries with
  | nil => exact add_zero 0
  | cons entry rest ih =>
    simp only [List.map_cons,List.sum_cons,Function.comp_apply]
    have head := entry.paid_exact
    linarith

theorem each_entry_is_an_actual_original_event (entry : Entry sources) (member : entry ∈ flow.entries) :
    entry.event ∈ path.events sources := by
  rw [← flow.events_exact]
  exact List.mem_map.mpr ⟨entry,member,rfl⟩
end Flow

def initial (claim : Claim sources) : Share.Split (initialBalance (sources claim.1) claim.2) :=
  ⟨0,initialBalance (sources claim.1) claim.2,fun _ => le_rfl,initial_nonnegative _ _,zero_add _⟩

def atBirth {first last : ResponsibilityState (vocabulary sources)}
    {run : (process sources).Run first last} (birth : Exposure.Birth sources run) :=
  fold sources birth.follow.path (initial sources birth.claim)

theorem canonical_acquisitions_and_original_principal_conserve
    {first last : ResponsibilityState (vocabulary sources)} {run : (process sources).Run first last}
    (birth : Exposure.Birth sources run) :
    Financial.total (sources birth.claim.1) (atBirth sources birth).final.selected + selectedPaid sources (atBirth sources birth).entries =
        acquired sources (atBirth sources birth).entries ∧
    Financial.total (sources birth.claim.1) (atBirth sources birth).final.remainder + remainderPaid sources (atBirth sources birth).entries +
        acquired sources (atBirth sources birth).entries = birth.claim.2.quantity := by
  constructor
  · simpa only [initial,Finsupp.sum_zero_index,Financial.total,zero_add] using
      (atBirth sources birth).selected_conservation birth.claim.1
  · exact ((atBirth sources birth).remainder_conservation birth.claim.1).trans (Financial.initial_total _ _)

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Family.Migration.AssignedFinancing.Joint
