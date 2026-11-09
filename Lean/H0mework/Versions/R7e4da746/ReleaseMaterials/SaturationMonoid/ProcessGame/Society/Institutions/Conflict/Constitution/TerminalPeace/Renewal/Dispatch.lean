import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Installation.Refusal
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Renewal.Service
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Supply.Exit

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Renewal

open Capitalism.Universal.Abolition.Accounting.Root
open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening
open Capitalism.Universal.Abolition.Material (ActualAndIndependent)
open Installation (Live Effect)
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion

noncomputable section

abbrev Ready (history : Original.Word) := { live : Live history // Supply.Stocked live.native.raw }

abbrev Submitted (before : Native) := (request : Request) × Replies before request

variable {history : Original.Word}

def write (prior : Ready history) (request : Request) {answers : Replies prior.val.native request}
    (approved : Admission prior.val.native request answers) : Ready history :=
  ⟨prior.val.step request approved,
    (congrArg (fun effect : Effect => Supply.Stocked effect.native.raw)
      (prior.val.step_reads_its_exact_material_effect request approved)).mpr approved.stocked⟩

theorem write_reads (prior : Ready history) (request : Request) {answers : Replies prior.val.native request}
    (approved : Admission prior.val.native request answers) :
    (write prior request approved).val.effect = ⟨prior.val.native, request⟩ :=
  prior.val.step_reads_its_exact_material_effect request approved

theorem write_keeps_the_original_balances (prior : Ready history) (request : Request)
    {answers : Replies prior.val.native request} (approved : Admission prior.val.native request answers) :
    (write prior request approved).val.state.stack.balances = prior.val.state.stack.balances :=
  congrArg _ (prior.val.step_keeps_the_exact_original_stack request approved)

theorem write_is_the_original_whole_successor (prior : Ready history) (request : Request)
    {answers : Replies prior.val.native request} (approved : Admission prior.val.native request answers) :
    (⟨prior.val.state.world,
      (prior.val.stepAction request approved).target.targetAnswerAndNext.nextCurrent⟩ :
        AnyAuthoritativeRootCurrent) = (write prior request approved).val.state.resident.erase :=
  prior.val.step_is_the_canonical_whole_write request approved

theorem write_pays_any_crossed_hour (prior : Ready history) (request : Request)
    {answers : Replies prior.val.native request} (approved : Admission prior.val.native request answers) :
    paidCrossing prior.val.native.raw (write prior request approved).val.native.raw
      (write prior request approved).val.items := by
  change paidCrossing prior.val.native.raw (write prior request approved).val.effect.native.raw
    (write prior request approved).val.effect.items
  rw [write_reads]
  exact approved.pays

theorem write_has_no_cross_boundary_damage (prior : Ready history) (request : Request)
    {answers : Replies prior.val.native request} (approved : Admission prior.val.native request answers)
    (item : Original.Item) (written : item ∈ (write prior request approved).val.effect.items)
    (key : Reparation.Key Bool Bool) :
    Reparation.loss Supply.physical Original.community item key = 0 := by
  change item ∈ (write prior request approved).val.effect.items at written
  rw [write_reads] at written
  obtain ⟨index, inside, same⟩ := List.mem_iff_getElem.mp written
  exact (same ▸ (approved.owns ⟨index, inside⟩).1).no_damage key

theorem write_preserves_the_material_principal (prior : Ready history) (request : Request)
    {answers : Replies prior.val.native request} (approved : Admission prior.val.native request answers) :
    (write prior request approved).val.native.raw.claims = prior.val.native.raw.claims := by
  change (write prior request approved).val.effect.native.raw.claims = _
  rw [write_reads]
  exact approved.principal.matrix

/-- The dispatch result distinguishes the exact refused input from an
actual whole-ledger action. A refusal has no material successor to spend. -/
def refuse (prior : Ready history) (request : Request) {answers : Replies prior.val.native request}
    (issue : Refusal prior.val.native request answers) : Ready history :=
  ⟨prior.val.reject request issue, prior.property⟩

def dispatch (prior : Ready history) (submitted : Submitted prior.val.native) : Ready history :=
  match inspect prior.val.native submitted.1 submitted.2 with
  | .inl issue => refuse prior submitted.1 issue
  | .inr approved => write prior submitted.1 approved.down

theorem dispatch_refusal (prior : Ready history) (submitted : Submitted prior.val.native)
    (issue : Refusal prior.val.native submitted.1 submitted.2)
    (disposition : inspect prior.val.native submitted.1 submitted.2 = .inl issue) :
    dispatch prior submitted = refuse prior submitted.1 issue := by
  unfold dispatch
  rw [disposition]

theorem dispatch_admission (prior : Ready history) (submitted : Submitted prior.val.native)
    (approved : Admission prior.val.native submitted.1 submitted.2) :
    dispatch prior submitted = write prior submitted.1 approved := by
  obtain ⟨checked, disposition⟩ :=
    inspect_covers_all_admitted_original_effects _ _ approved
  unfold dispatch
  rw [disposition]

def dispatchWhole (prior : Ready history) (submitted : Submitted prior.val.native) :
    AnyAuthoritativeRootCurrent :=
  match inspect prior.val.native submitted.1 submitted.2 with
  | .inl issue =>
    ⟨prior.val.state.world, (prior.val.rejectAction submitted.1 issue).target.targetAnswerAndNext.nextCurrent⟩
  | .inr approved =>
    ⟨prior.val.state.world, (prior.val.stepAction submitted.1 approved.down).target.targetAnswerAndNext.nextCurrent⟩

theorem dispatch_is_the_original_whole_successor (prior : Ready history) (submitted : Submitted prior.val.native) :
    dispatchWhole prior submitted = (dispatch prior submitted).val.state.resident.erase := by
  unfold dispatchWhole dispatch
  cases inspect prior.val.native submitted.1 submitted.2
  · exact prior.val.reject_is_the_canonical_whole_write _ _
  · exact prior.val.step_is_the_canonical_whole_write _ _

theorem dispatch_keeps_original_balances (prior : Ready history) (submitted : Submitted prior.val.native) :
    (dispatch prior submitted).val.state.stack.balances = prior.val.state.stack.balances := by
  unfold dispatch
  cases inspect prior.val.native submitted.1 submitted.2
  · rfl
  · exact write_keeps_the_original_balances prior submitted.1 _

theorem dispatch_keeps_material_principal (prior : Ready history) (submitted : Submitted prior.val.native) :
    (dispatch prior submitted).val.native.raw.claims = prior.val.native.raw.claims := by
  unfold dispatch
  cases inspect prior.val.native submitted.1 submitted.2
  · rfl
  · exact write_preserves_the_material_principal prior submitted.1 _

theorem dispatch_never_rolls_back_the_original_clock (prior : Ready history) (submitted : Submitted prior.val.native) :
    prior.val.native.raw.clock ≤ (dispatch prior submitted).val.native.raw.clock := by
  unfold dispatch
  cases inspect prior.val.native submitted.1 submitted.2
  · exact le_rfl
  · exact (write_pays_any_crossed_hour prior submitted.1 _).clock_mono

theorem dispatch_has_its_original_clock_cell (prior : Ready history) (submitted : Submitted prior.val.native) :
    (dispatch prior submitted).val.native.raw.clock = prior.val.native.raw.clock ∨
    (dispatch prior submitted).val.native.raw.clock = prior.val.native.raw.clock + 1 := by
  unfold dispatch
  cases inspect prior.val.native submitted.1 submitted.2 with
  | inl issue => exact Or.inl rfl
  | inr approved =>
    rcases write_pays_any_crossed_hour prior submitted.1 approved.down with same | later
    · exact Or.inl same.1
    · exact Or.inr later.1

theorem dispatch_pays_every_elapsed_hour (prior : Ready history) (submitted : Submitted prior.val.native)
    (elapsed : prior.val.native.raw.clock < (dispatch prior submitted).val.native.raw.clock) (person : Bool) :
    1 ≤ foodPaid (dispatch prior submitted).val.items person := by
  cases disposition : inspect prior.val.native submitted.1 submitted.2 with
  | inl issue =>
    rw [dispatch_refusal prior submitted issue disposition] at elapsed
    exact (lt_irrefl prior.val.native.raw.clock elapsed).elim
  | inr approved =>
    rw [dispatch_admission prior submitted approved.down] at elapsed ⊢
    exact (write_pays_any_crossed_hour prior submitted.1 approved.down).every_advance_pays_each_person elapsed person

def NoNewDamage (live : Live history) : Prop :=
  ∀ item ∈ live.items, ∀ key, Reparation.loss Supply.physical Original.community item key = 0

theorem write_has_no_new_damage (prior : Ready history) (request : Request)
    {answers : Replies prior.val.native request} (approved : Admission prior.val.native request answers) :
    NoNewDamage (write prior request approved).val := by
  intro item written key
  exact write_has_no_cross_boundary_damage prior request approved item written key

theorem dispatch_has_no_new_damage (prior : Ready history) (submitted : Submitted prior.val.native) :
    NoNewDamage (dispatch prior submitted).val := by
  cases disposition : inspect prior.val.native submitted.1 submitted.2 with
  | inl issue =>
    rw [dispatch_refusal prior submitted issue disposition]
    intro item written
    exact (List.not_mem_nil written).elim
  | inr approved =>
    rw [dispatch_admission prior submitted approved.down]
    exact write_has_no_new_damage prior submitted.1 approved.down

def ItemExits (items : List Original.Item) : Prop :=
  ∀ item ∈ items, ∀ person,
    ActualAndIndependent Supply.revisedInput item.before (Supply.personalWord person) ∧
    ActualAndIndependent Supply.revisedInput
      (Supply.physical.step item.before item.request) (Supply.personalWord person)

theorem admitted_items_have_independent_exits (before : Native) (request : Request)
    {answers : Replies before request} (approved : Admission before request answers) :
    ItemExits (readAction before request).execution.items := by
  intro item written person
  obtain ⟨index, inside, same⟩ := List.mem_iff_getElem.mp written
  have reserve : Supply.Stocked item.before ∧ Supply.Stocked (Supply.physical.step item.before item.request) :=
    same ▸ (approved.owns ⟨index, inside⟩).2.2
  exact ⟨Supply.the_personal_exit_passes_the_original_independence_checker
    _ person (reserve.1 person).1 (reserve.1 person).2,
    Supply.the_personal_exit_passes_the_original_independence_checker
      _ person (reserve.2 person).1 (reserve.2 person).2⟩

theorem dispatch_keeps_every_item_exit (prior : Ready history) (submitted : Submitted prior.val.native) :
    ItemExits (dispatch prior submitted).val.items := by
  cases disposition : inspect prior.val.native submitted.1 submitted.2 with
  | inl issue =>
    rw [dispatch_refusal prior submitted issue disposition]
    intro item written
    exact (List.not_mem_nil written).elim
  | inr approved =>
    rw [dispatch_admission prior submitted approved.down]
    exact admitted_items_have_independent_exits _ _ approved.down

theorem every_cut_has_a_personal_exit (prior : Ready history) (person : Bool) :
    ActualAndIndependent Supply.revisedInput prior.val.native.raw (Supply.personalWord person) :=
  Supply.the_personal_exit_passes_the_original_independence_checker
    prior.val.native.raw person (prior.property person).1 (prior.property person).2

def renew (prior : Ready history) (first : Bool) : Ready history :=
  write prior (orderedService first)
    (the_service_is_admitted_from_its_current_stock prior.val.native prior.property first)

theorem renew_raw (prior : Ready history) (first : Bool) :
    (renew prior first).val.native.raw =
      { prior.val.native.raw with clock := prior.val.native.raw.clock + 1, round := prior.val.native.raw.round + 1 } := by
  change (renew prior first).val.effect.native.raw = _
  unfold renew
  rw [write_reads]
  exact the_service_raw prior.val.native prior.property first

theorem renew_pays_each_person (prior : Ready history) (first person : Bool) :
    foodPaid (renew prior first).val.items person = 1 := by
  change foodPaid (renew prior first).val.effect.items person = 1
  unfold renew
  rw [write_reads]
  exact the_service_pays_exactly_one_to_each_original_person prior.val.native prior.property first person

theorem renew_keeps_original_balances (prior : Ready history) (first : Bool) :
    (renew prior first).val.state.stack.balances = prior.val.state.stack.balances :=
  write_keeps_the_original_balances prior (orderedService first) _

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Renewal
