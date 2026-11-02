import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Future
import Mathlib.Algebra.Order.Floor.Ring

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Future.Recovery
open Institutions.Capitalism.Universal.Source.Program

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]

abbrev Action (_ : Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)) :=
  Request Party Good Port (Mandate.State Party Technology) Instrument
abbrev Current (_ : Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)) :=
  RawCurrent Party Good (Mandate.State Party Technology) Instrument

namespace Search
variable (model : Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (before : Current model) (actor : Party) (original : List (Action model))

abbrev law := Mandate.law model.base model.scope

def work : Action model :=
  ⟨actor,[],(original.head?.map Request.purpose).getD model.scope.service,[],.produce actor⟩
def menu := model.source.code.actions.filter fun request =>
  decide (request.signer = actor ∧ ∀ consent ∈ request.consents,consent = actor)
def input (good : Good) := amount Good
  ((law model).technique before.technology actor).inputs good +
  amount Good ((law model).technique before.technology actor).maintenance good
def gain (good : Good) := amount Good
  ((law model).technique before.technology actor).outputs good-input model before actor good

def demand (good : Good) := (original.map fun request =>
  max 0 (flowAt ((law model).debit before (Mandate.Replay.rebase model.scope before request)) actor good)).sum

def needed : Nat := (model.source.code.goods.map fun good =>
  if 0 < gain model before actor good then
    ⌈max 0 (demand model before actor original good-before.stock actor good) / gain model before actor good⌉₊
  else 0).foldl max 0

/-- Production attempts are bounded by both task debit and actual source feedstock. -/
def limit : Nat := (model.source.code.goods.map fun good =>
  if 0 < input model before actor good then ⌊before.stock actor good/input model before actor good⌋₊
  else needed model before actor original).foldl min (needed model before actor original)

def repairs : List (List (Action model)) :=
  (List.range (limit model before actor original+1)).flatMap fun count =>
    (words (menu model actor) model.source.code.actionLimit).map fun tail =>
      List.replicate count (work model actor original) ++ tail

structure Proposal where
  preparation : List (Action model)

def Proposal.prepared (proposal : Proposal model) :=
  Mandate.Replay.compile model.base model.scope before proposal.preparation

def Proposal.staged (proposal : Proposal model) :=
  ((law model).execute before 0 (proposal.prepared model before).output).final

def Proposal.retry (proposal : Proposal model) :=
  Mandate.Replay.compile model.base model.scope (proposal.staged model before) original

def Proposal.quality (proposal : Proposal model) : Nat :=
  if (proposal.prepared model before).succeeded then (proposal.retry model before original).consumed.length else 0

def Proposal.word (proposal : Proposal model) :=
  (proposal.prepared model before).output ++ (proposal.retry model before original).output

def baseline : Proposal model := ⟨[]⟩
def prefer (left right : Proposal model) :=
  if left.quality model before original < right.quality model before original then right else left

def proposals := (repairs model before actor original).map (Proposal.mk (model := model))
def selected := (proposals model before actor original).foldl (prefer model before original) (baseline model)

theorem every_registered_repair_is_personally_signed (request : Action model)
    (inside : request ∈ menu model actor) :
    request.signer = actor ∧ ∀ consent ∈ request.consents,consent = actor := by
  exact of_decide_eq_true (List.mem_filter.mp inside).2

private theorem quality_left (left right : Proposal model) :
    left.quality model before original ≤ (prefer model before original left right).quality model before original := by
  unfold prefer;split
  next strict => exact Nat.le_of_lt strict
  next => exact le_refl _

private theorem quality_right (left right : Proposal model) :
    right.quality model before original ≤ (prefer model before original left right).quality model before original := by
  unfold prefer;split
  next => exact le_refl _
  next notStrict => exact Nat.le_of_not_gt notStrict

private theorem quality_fold (rows : List (Proposal model)) (start : Proposal model) :
    start.quality model before original ≤
      (rows.foldl (prefer model before original) start).quality model before original := by
  induction rows generalizing start with
  | nil => exact le_refl _
  | cons head tail ih => exact (quality_left model before original start head).trans (ih _)

theorem selected_maximal (proposal : Proposal model)
    (registered : proposal ∈ proposals model before actor original) :
    proposal.quality model before original ≤ (selected model before actor original).quality model before original := by
  have bound (rows : List (Proposal model)) (start : Proposal model) (p : Proposal model) (inside : p ∈ rows) :
      p.quality model before original ≤ (rows.foldl (prefer model before original) start).quality model before original := by
    induction rows generalizing start with
    | nil => cases inside
    | cons head tail ih =>
      rcases List.mem_cons.mp inside with rfl | rest
      · exact (quality_right model before original start p).trans (quality_fold model before original tail _)
      · exact ih _ rest
  exact bound _ _ proposal registered

private theorem positive_quality_has_paid_preparation (proposal : Proposal model)
    (positive : 0 < proposal.quality model before original) :
    (proposal.prepared model before).succeeded = true := by
  unfold Proposal.quality at positive
  split at positive
  next paid => exact paid
  next => omega

theorem selected_preparation_is_legal :
    ((selected model before actor original).prepared model before).succeeded = true := by
  have keep (rows : List (Proposal model)) (start : Proposal model)
      (paid : (start.prepared model before).succeeded = true) :
      ((rows.foldl (prefer model before original) start).prepared model before).succeeded = true := by
    induction rows generalizing start with
    | nil => exact paid
    | cons head tail ih =>
      apply ih
      by_cases strict : start.quality model before original < head.quality model before original
      · rw [prefer,if_pos strict]
        exact positive_quality_has_paid_preparation model before original head (by omega)
      · rw [prefer,if_neg strict];exact paid
  exact keep _ _ rfl

theorem selected_is_unchanged_or_registered :
    selected model before actor original = baseline model ∨
      selected model before actor original ∈ proposals model before actor original := by
  have member (rows : List (Proposal model)) (start : Proposal model) :
      rows.foldl (prefer model before original) start = start ∨
        rows.foldl (prefer model before original) start ∈ rows := by
    induction rows generalizing start with
    | nil => exact Or.inl rfl
    | cons head tail ih =>
      rcases ih (prefer model before original start head) with same | inside
      · rw [List.foldl_cons,same]
        unfold prefer;split
        next => exact Or.inr List.mem_cons_self
        next => exact Or.inl rfl
      · exact Or.inr (List.mem_cons_of_mem _ inside)
  exact member _ _

theorem every_preparation_is_generated_from_real_material_and_registered_own_work
    (preparation : List (Action model)) (inside : preparation ∈ repairs model before actor original) :
    ∃ count tail, count ≤ limit model before actor original ∧
      tail ∈ words (menu model actor) model.source.code.actionLimit ∧
      preparation = List.replicate count (work model actor original) ++ tail := by
  obtain ⟨count,listed,tail⟩ := List.mem_flatMap.mp inside
  obtain ⟨rest,registered,same⟩ := List.mem_map.mp tail
  exact ⟨count,rest,Nat.le_of_lt_succ (List.mem_range.mp listed),registered,same.symm⟩

theorem every_generated_preparation_preserves_personal_signature_control
    (preparation : List (Action model)) (inside : preparation ∈ repairs model before actor original) :
    Mandate.Replay.Personal actor preparation := by
  obtain ⟨count,tail,_,registered,rfl⟩ :=
    every_preparation_is_generated_from_real_material_and_registered_own_work model before actor original preparation inside
  intro request present
  rcases List.mem_append.mp present with supply | work
  · have same := List.eq_of_mem_replicate supply
    subst request
    exact ⟨rfl,fun _ impossible => by cases impossible⟩
  · exact every_registered_repair_is_personally_signed model actor request
      (((mem_words_iff _ _ _).mp registered).2 request work)

theorem selected_preparation_is_personally_signed :
    Mandate.Replay.Personal actor ((selected model before actor original).prepared model before).output := by
  apply Mandate.Replay.Path.output_preserves_personal_signature_control
  rcases selected_is_unchanged_or_registered model before actor original with same | registered
  · rw [same]
    intro _ impossible;cases impossible
  · obtain ⟨preparation,inside,same⟩ := List.mem_map.mp registered
    rw [←same]
    exact every_generated_preparation_preserves_personal_signature_control model before actor original preparation inside

private theorem consumed_at_most (path : Mandate.Replay.Path model.base model.scope before original) :
    path.consumed.length ≤ original.length := by
  have length := congrArg List.length path.original_split
  simp only [List.length_append] at length;omega

theorem no_residual_after_success {state : Current model} {word : List (Action model)}
    (path : Mandate.Replay.Path model.base model.scope state word) (paid : path.succeeded = true) : path.residual = [] := by
  induction path
  next => rfl
  next => cases paid
  next _ _ _ _ _ ih => exact ih paid

theorem any_registered_complete_recovery_is_found (proposal : Proposal model)
    (registered : proposal ∈ proposals model before actor original)
    (prepared : (proposal.prepared model before).succeeded = true)
    (complete : (proposal.retry model before original).succeeded = true) :
    ((selected model before actor original).retry model before original).succeeded = true := by
  have length : (proposal.retry model before original).consumed.length = original.length := by
    have split := (proposal.retry model before original).original_split
    rw [no_residual_after_success model _ complete,List.append_nil] at split
    exact congrArg List.length split
  have maximal := selected_maximal model before actor original proposal registered
  simp only [Proposal.quality,prepared,selected_preparation_is_legal,if_true] at maximal
  rw [length] at maximal
  cases finished : ((selected model before actor original).retry model before original).succeeded with
  | true => rfl
  | false =>
    obtain ⟨paidPrefix,head,tail,split,_,_,_,_,_⟩ :=
      ((selected model before actor original).retry model before original).failed_output_ends_at_its_actual_first_refusal finished
    have size := congrArg List.length split
    simp only [List.length_append,List.length_cons] at size
    omega

theorem failed_selection_retains_every_registered_complete_obstruction
    (failed : ((selected model before actor original).retry model before original).succeeded = false)
    (proposal : Proposal model) (registered : proposal ∈ proposals model before actor original)
    (paid : (proposal.prepared model before).succeeded = true) :
    (proposal.retry model before original).succeeded = false := by
  cases result : (proposal.retry model before original).succeeded with
  | false => rfl
  | true =>
    have complete := any_registered_complete_recovery_is_found model before actor original proposal registered paid result
    rw [failed] at complete;cases complete

end Search
end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Future.Recovery
