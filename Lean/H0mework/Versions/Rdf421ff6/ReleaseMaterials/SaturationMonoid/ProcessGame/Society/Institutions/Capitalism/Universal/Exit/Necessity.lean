import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.Program.JointAuthority

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Exit.Necessity

open Source.Program

universe u
variable {Party Good Port Technology Instrument : Type u}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]

def UseMatches (operation : Operation Party Good Technology Instrument)
    (party : Party) (goods : Bundle Good) (purpose : Use) : Prop :=
  match operation with
  | .use bearer paid kind => bearer = party ∧ paid = goods ∧ kind = purpose
  | _ => False

instance (operation : Operation Party Good Technology Instrument)
    (party : Party) (goods : Bundle Good) (purpose : Use) :
    Decidable (UseMatches operation party goods purpose) := by
  unfold UseMatches
  cases operation <;> infer_instance

omit [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument] in
theorem useMatches_iff (operation : Operation Party Good Technology Instrument)
    (party : Party) (goods : Bundle Good) (purpose : Use) :
    UseMatches operation party goods purpose ↔ operation = .use party goods purpose := by
  cases operation <;> simp [UseMatches]

variable (law : RawLaw Party Good Port Technology Instrument)
  (current : RawCurrent Party Good Technology Instrument)

/-- Zero demand needs no fictitious payment event.  Nonempty demand requires
an accepted original use of the entire source bundle. -/
def BundlePaid (word : RawEvent Party Good Port Technology Instrument)
    (party : Party) (goods : Bundle Good) (purpose : Use) : Prop :=
  goods = [] ∨ ∃ item ∈ law.rawItems current word,
    law.Valid item.before item.request ∧ UseMatches item.request.operation party goods purpose

instance (word : RawEvent Party Good Port Technology Instrument)
    (party : Party) (goods : Bundle Good) (purpose : Use) :
    Decidable (BundlePaid law current word party goods purpose) := by
  unfold BundlePaid
  infer_instance

def AllNeedsPaid (group : List Party) (word : RawEvent Party Good Port Technology Instrument) : Prop :=
  ∀ party ∈ group,
    BundlePaid law current word party (law.necessities current party) .necessity ∧
    BundlePaid law current word party (law.mandatoryMaintenance current party) .maintenance

instance (group : List Party) (word : RawEvent Party Good Port Technology Instrument) :
    Decidable (AllNeedsPaid law current group word) := by unfold AllNeedsPaid; infer_instance

theorem bundlePaid_reauthorization (original alternative : RawEvent Party Good Port Technology Instrument)
    (same : alternative.map Request.operation = original.map Request.operation)
    (valid : ∀ item ∈ law.rawItems current alternative, law.Valid item.before item.request)
    (party : Party) (goods : Bundle Good) (purpose : Use)
    (paid : BundlePaid law current original party goods purpose) :
    BundlePaid law current alternative party goods purpose := by
  rcases paid with empty | ⟨item, member, _accepted, matched⟩
  · exact Or.inl empty
  · right
    have submitted : item.request ∈ original := by
      have mapped : item.request ∈ (law.rawItems current original).map ExecutionItem.request :=
        List.mem_map.mpr ⟨item, member, rfl⟩
      rwa [RawLaw.rawItems, RawLaw.inventory_requests_exact] at mapped
    have operation : item.request.operation ∈ alternative.map Request.operation := by
      rw [same]
      exact List.mem_map.mpr ⟨item.request, submitted, rfl⟩
    obtain ⟨request, inside, sameOperation⟩ := List.mem_map.mp operation
    have emitted : request ∈ (law.rawItems current alternative).map ExecutionItem.request := by
      rw [RawLaw.rawItems, RawLaw.inventory_requests_exact]
      exact inside
    obtain ⟨actual, actualMember, sameRequest⟩ := List.mem_map.mp emitted
    refine ⟨actual, actualMember, valid actual actualMember, ?_⟩
    rw [sameRequest, sameOperation]
    exact matched

theorem allNeedsPaid_jointWord (group : List Party)
    (original alternative : RawEvent Party Good Port Technology Instrument)
    (generated : law.jointWord group current original = some alternative)
    (paid : AllNeedsPaid law current group original) :
    AllNeedsPaid law current group alternative := by
  have sound := law.jointWord_sound group current original alternative generated 0
  have valid : ∀ item ∈ law.rawItems current alternative, law.Valid item.before item.request :=
    fun item member => (sound.2.1 item member).1
  intro party inside
  exact ⟨bundlePaid_reauthorization law current original alternative sound.2.2 valid
      party _ .necessity (paid party inside).1,
    bundlePaid_reauthorization law current original alternative sound.2.2 valid
      party _ .maintenance (paid party inside).2⟩

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Exit.Necessity
