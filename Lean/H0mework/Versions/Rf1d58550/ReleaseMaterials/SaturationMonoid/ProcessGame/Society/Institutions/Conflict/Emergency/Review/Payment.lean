import H0mework.Versions.Rf1d58550.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Emergency.Horizon
import H0mework.Versions.Rf1d58550.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Root.OriginalSlot

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Emergency

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Abolition.Root
open Capitalism.Universal.Abolition.Root.Registered
open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening
open PublicFunction.Mandate

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]

local notation "C" => Root.Cut Party Good Port (State Party Technology) Instrument
local notation "Raw" => RawCurrent Party Good (State Party Technology) Instrument
local notation "Word" => RawEvent Party Good Port (State Party Technology) Instrument
local notation "Req" => Request Party Good Port (State Party Technology) Instrument
local notation "Item" => ExecutionItem Party Good Port (State Party Technology) Instrument
local notation "Base" => RawLaw Party Good Port Technology Instrument
local notation "J" => Scope (Party := Party) (Good := Good) (Port := Port)

/-- The second signature is generated at the result of the first original
request. There is no supplied version, replacement payer, or newer deadline. -/
def reviewPair (base : Base) (scope : J) (cut : Raw) (first second : Party) : Word :=
  let head := request scope cut first .review
  [head, request scope ((law base scope).step cut head) second .review]

def reviewWord (base : Base) (scope : J) (cut : C) (first second : Party) (tail : Word) : Word :=
  reviewPair base scope cut.raw first second ++ tail

/-- The tail settles local uses. It cannot refund the two reviewers, enter
another office grant, or discharge a financial slot under the review label. -/
def KeepsReview (request : Req) : Prop :=
  match request.operation with
  | .use bearer .. => bearer = request.signer
  | .present => True
  | _ => False

instance (request : Req) : Decidable (KeepsReview request) := by
  unfold KeepsReview
  cases request.operation <;> infer_instance

def LocalTail (tail : Word) : Prop := ∀ request ∈ tail, KeepsReview request

instance (tail : Word) : Decidable (LocalTail tail) := by
  unfold LocalTail
  infer_instance

theorem original_execution {cut : C} {base : Base} {scope : J}
    (original : Installed cut base scope) {word : Word} (paid : Root.Paid cut word) :
    (Physical.Public.interpreter cut.native.input).execute cut.raw 0 word =
      (law base scope).execute cut.raw 0 word := by
  have same := PublicFunction.execute_physical_of_authorized cut.native.input.law cut.raw 0 word
    (fun item member => PublicFunction.valid_physical _ _ _ (paid.authorized item member))
    (fun item member => paid.authorized item member)
  rw [← original]
  exact same.symm

theorem original_review_items {cut : C} {base : Base} {scope : J}
    (original : Installed cut base scope) {first second : Party} {tail : Word}
    (paid : Root.Paid cut (reviewWord base scope cut first second tail)) :
    let head := request scope cut.raw first .review
    let middle := (law base scope).step cut.raw head
    let independent := request scope middle second .review
    (law base scope).Valid cut.raw head ∧ (law base scope).Valid middle independent := by
  let head := request scope cut.raw first .review
  let middle := (law base scope).step cut.raw head
  let independent := request scope middle second .review
  have exactItems := congrArg (fun result => result.items) (original_execution original paid)
  have recorded : ∀ item ∈ ((law base scope).execute cut.raw 0
      (reviewWord base scope cut first second tail)).items, (law base scope).Valid item.before item.request := by
    intro item present
    have accepted := paid.authorized item (by unfold RawLaw.rawItems; rwa [exactItems])
    rwa [original] at accepted
  exact ⟨recorded (⟨0, cut.raw, head⟩ : Item) List.mem_cons_self,
    recorded (⟨1, middle, independent⟩ : Item) (List.mem_cons_of_mem _ List.mem_cons_self)⟩

omit [DecidableEq Instrument] in
theorem reviewer_debit (base : Base) (scope : J) (cut : Raw) (reviewer : Party)
    (accepted : (law base scope).Valid cut (request scope cut reviewer .review)) :
    (law base scope).actualDebit cut (request scope cut reviewer .review) = locate reviewer scope.revisionCost := by
  rw [RawLaw.actualDebit, if_pos accepted]
  rfl

theorem review_cost_at_original_address (base : Base) (scope : J) (cut : Raw) (reviewer : Party)
    (accepted : (law base scope).Valid cut (request scope cut reviewer .review)) (bearer : Party) (good : Good) :
    ((law base scope).step cut (request scope cut reviewer .review)).stock bearer good +
      flowAt (locate reviewer scope.revisionCost) bearer good = cut.stock bearer good := by
  have balance := (law base scope).material_step_balance cut (request scope cut reviewer .review) bearer good
  rw [reviewer_debit base scope cut reviewer accepted] at balance
  have noCredit : (law base scope).actualCredit cut (request scope cut reviewer .review) = [] := by
    rw [RawLaw.actualCredit, if_pos accepted]
    rfl
  simpa [noCredit, flowAt, amount] using balance

theorem flow_at_own_address (bundle : Bundle Good) (party : Party) (good : Good) :
    flowAt (locate party bundle) party good = amount Good bundle good := by
  unfold flowAt locate amount
  rw [List.map_map]
  simp [Function.comp_def]

theorem nonfinancial_review_word (base : Base) (scope : J) (cut : C) (first second : Party)
    {tail : Word} (localTail : LocalTail tail) :
    Settlement.NonFinancial (reviewWord base scope cut first second tail) := by
  intro req present
  simp only [reviewWord, reviewPair, List.cons_append, List.nil_append, List.mem_cons] at present
  rcases present with rfl | rfl | later
  · trivial
  · trivial
  · have keep := localTail req later
    unfold Settlement.NonFinancialRequest
    cases observed : req.operation <;> simp_all [KeepsReview]

theorem review_word_has_no_transfer (base : Base) (scope : J) (cut : C) (first second : Party)
    {tail : Word} (localTail : LocalTail tail) :
    ∀ request ∈ reviewWord base scope cut first second tail, ∀ sender receiver bundle,
      request.operation ≠ .transfer sender receiver bundle := by
  intro req present sender receiver bundle
  simp only [reviewWord, reviewPair, List.cons_append, List.nil_append, List.mem_cons] at present
  rcases present with rfl | rfl | later
  · intro impossible; cases impossible
  · intro impossible; cases impossible
  · intro same
    have keep := localTail req later
    simp only [KeepsReview, same] at keep

omit [DecidableEq Party] [DecidableEq Good] in
private theorem locate_owns_every_debit (party : Party) (bundle : Bundle Good)
    {item : (Party × Good) × ℚ} (member : item ∈ locate party bundle) : item.1.1 = party := by
  obtain ⟨_, _, rfl⟩ := List.mem_map.mp member
  rfl

/-- The entire reviewed word charges only the actual signers, including the
local necessity and maintenance tail. -/
theorem review_word_debits_belong_to_their_signers (base : Base) (scope : J) (cut : C) (first second : Party)
    {tail : Word} (localTail : LocalTail tail)
    (before : Raw) (req : Req) (present : req ∈ reviewWord base scope cut first second tail)
    (item : (Party × Good) × ℚ) (charged : item ∈ (law base scope).actualDebit before req) :
    item.1.1 = req.signer := by
  unfold RawLaw.actualDebit at charged
  split at charged
  · simp only [reviewWord, reviewPair, List.cons_append, List.nil_append, List.mem_cons] at present
    rcases present with rfl | rfl | later
    · exact locate_owns_every_debit first scope.revisionCost charged
    · exact locate_owns_every_debit second scope.revisionCost charged
    · have keep := localTail req later
      cases observed : req.operation with
      | use bearer bundle purpose =>
        simp only [KeepsReview, observed] at keep
        rw [RawLaw.debit, observed] at charged
        exact (locate_owns_every_debit bearer bundle charged).trans keep
      | present => simp [RawLaw.debit, observed] at charged
      | produce | transfer | issue | assign | settle | revise =>
        simp only [KeepsReview, observed] at keep
  · exact (List.not_mem_nil charged).elim

end
end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Emergency
