import H0mework.Versions.Rcb211392.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Regeneration.Supply.Material.Productive.Synthesis.Settlement.Stream.Resume.Runtime

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Regeneration.Supply.Productive.Synthesis.Settlement.Stream.Resume.Regen

open Institutions.Capitalism.Universal.Source.Program

/-- The provider-side donor and the audit-side release holder keep their
original distinct material addresses. -/
theorem donor_is_not_the_release_holder : Refeed.donor ≠ receiver := by decide

inductive Authority where
  | original
  | refusedSigner
  deriving DecidableEq

def Authority.mode : Authority → Supply.Mode
  | .original => .refeed
  | .refusedSigner => .denyRecycling

def liveDemand (seed : Seed) (requests : Requests.Source) (frame : Frame seed.basis) : Bool :=
  match frame.protocol.pending with
  | some window => decide (frame.raw.clock + 1 ≤ window.task.deadline)
  | none =>
    match requests frame.protocol.received frame.raw.round with
    | none => false
    | some submission => decide (Requests.Shape submission frame.raw) && seed.role.isSome

def needsOriginalRefeed (seed : Seed) (requests : Requests.Source) (ordinal : Nat)
    (frame : Frame seed.basis) : Bool :=
  ordinal != 0 && liveDemand seed requests frame &&
    decide (frame.raw.stock receiver .energy < 2 ∧ frame.raw.stock supplier .feed < 1 ∧
      frame.raw.stock Refeed.donor .feed < 1)

def materialWord (scope : Scope) (authority : Authority) (raw : Current) : List JointAction :=
  Supply.lot scope raw authority.mode

def word (seed : Seed) (requests : Requests.Source) (authority : Authority) (ordinal : Nat)
    (frame : Frame seed.basis) : List JointAction :=
  if needsOriginalRefeed seed requests ordinal frame then materialWord seed.basis.origin.scope authority frame.raw
  else Resume.word seed requests .normal ordinal frame

def step (seed : Seed) (requests : Requests.Source) (authority : Authority) (ordinal : Nat)
    (frame : Frame seed.basis) : Frame seed.basis :=
  if needsOriginalRefeed seed requests ordinal frame then
    ⟨Supply.initialMemo ((law seed.basis.origin.scope).next frame.raw (materialWord seed.basis.origin.scope authority frame.raw)),
      frame.protocol⟩
  else Resume.step seed requests .normal ordinal frame

theorem original_repair_holds_the_request_and_its_deadline
    (seed : Seed) (requests : Requests.Source) (authority : Authority) (ordinal : Nat)
    (frame : Frame seed.basis) (repair : needsOriginalRefeed seed requests ordinal frame = true) :
    (step seed requests authority ordinal frame).protocol = frame.protocol := by
  simp only [step, repair, if_true]

theorem step_uses_the_selected_actual_word
    (seed : Seed) (requests : Requests.Source) (authority : Authority) (ordinal : Nat)
    (frame : Frame seed.basis) :
    (step seed requests authority ordinal frame).raw =
      (law seed.basis.origin.scope).next frame.raw (word seed requests authority ordinal frame) := by
  unfold step word
  split
  · exact Supply.initialMemo_exact _
  · exact Supply.initialMemo_exact _

abbrev Item := ExecutionItem Actor Good Port Technology Instrument

def firstRefusal (scope : Scope) (items : List Item) :
    Option {row : Item // row ∈ items ∧ ¬ (law scope).Valid row.before row.request} :=
  items.attach.findSome? fun row =>
    if refused : ¬ (law scope).Valid row.val.before row.val.request then
      some ⟨row.val, row.property, refused⟩
    else none

def refusal? (scope : Scope) (before : Current) (actions : List JointAction) :=
  firstRefusal scope ((law scope).rawItems before actions)

theorem no_refusal_iff_every_original_row_is_paid (scope : Scope) (items : List Item) :
    firstRefusal scope items = none ↔ ∀ row ∈ items, (law scope).Valid row.before row.request := by
  unfold firstRefusal
  rw [List.findSome?_eq_none_iff]
  constructor
  · intro noRefusal row member
    by_contra refused
    have inspected := noRefusal ⟨row, member⟩ (by simp)
    simp [dif_pos refused] at inspected
  · intro paid row _member
    exact dif_neg (fun refused => refused (paid row.val row.property))

structure MaterialShortage (scope : Scope) (row : Item) where
  private mk ::
  bearer : Actor
  good : Good
  originalDebit : ∃ quantity, ((bearer, good), quantity) ∈ (law scope).debit row.before row.request
  missing : row.before.stock bearer good < flowAt ((law scope).debit row.before row.request) bearer good

def MaterialShortage.amount {scope : Scope} {row : Item} (shortage : MaterialShortage scope row) : ℚ :=
  flowAt ((law scope).debit row.before row.request) shortage.bearer shortage.good -
    row.before.stock shortage.bearer shortage.good

def materialShortage? (scope : Scope) (row : Item) : Option (MaterialShortage scope row) :=
  ((law scope).debit row.before row.request).attach.findSome? fun entry => by
    rcases entry with ⟨⟨⟨bearer, good⟩, quantity⟩, present⟩
    exact if missing : row.before.stock bearer good < flowAt ((law scope).debit row.before row.request) bearer good then
      some ⟨bearer, good, ⟨quantity, present⟩, missing⟩
    else none

theorem MaterialShortage.refuses_the_original_action {scope : Scope} {row : Item}
    (shortage : MaterialShortage scope row) : ¬ (law scope).Valid row.before row.request := by
  intro paid
  obtain ⟨quantity, debit⟩ := shortage.originalDebit
  exact (not_le_of_gt shortage.missing) (paid.2.2.2.2.2 ((shortage.bearer, shortage.good), quantity) debit)

theorem no_material_shortage_iff_every_original_debit_is_funded (scope : Scope) (row : Item) :
    materialShortage? scope row = none ↔
      ∀ entry ∈ (law scope).debit row.before row.request,
        flowAt ((law scope).debit row.before row.request) entry.1.1 entry.1.2 ≤ row.before.stock entry.1.1 entry.1.2 := by
  unfold materialShortage?
  rw [List.findSome?_eq_none_iff]
  constructor
  · rintro noShortage ⟨⟨bearer, good⟩, quantity⟩ member
    apply le_of_not_gt
    intro missing
    have inspected := noShortage ⟨((bearer, good), quantity), member⟩ (by simp)
    simp [dif_pos missing] at inspected
  · rintro funded ⟨⟨⟨bearer, good⟩, quantity⟩, member⟩ _
    exact dif_neg (not_lt_of_ge (funded ((bearer, good), quantity) member))

end SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Regeneration.Supply.Productive.Synthesis.Settlement.Stream.Resume.Regen
