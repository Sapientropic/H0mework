import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Future.Recovery.Search

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Future.Recovery.Search.Billing
open Institutions.Capitalism.Universal.Source.Program
variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]

variable (model : Context (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument))
  (before : Current model) (original : List (Action model))

def IsFee (actor : Party) (request : Action model) : Prop :=
  request.signer = actor ∧ (∀ consent ∈ request.consents,consent = actor) ∧
  ¬ Mandate.TaskUse model.scope request ∧
  match request.operation with
  | .use bearer bundle .external => bearer = actor ∧ NonnegativeBundle Good bundle ∧
      ∃ good ∈ model.goods,0 < amount Good bundle good
  | _ => False

instance (actor : Party) (request : Action model) : Decidable (IsFee model actor request) := by
  unfold IsFee
  cases request.operation <;> try infer_instance
  rename_i bearer bundle purpose
  cases purpose <;> infer_instance

def tariffs (actor : Party) : List (Action model) :=
  model.actions.filter (fun request => decide (IsFee model actor request))

def comparisonUnits {α : Type} (pending : List α) (catalogue : List (List α)) : Nat :=
  1 + catalogue.length + pending.length +
    (catalogue.map fun preparation => 3*preparation.length+pending.length).sum

structure Ranked where
  proposal : Search.Proposal model
  value : Nat
  exact : value = proposal.quality model before original

def rank (preparation : List (Action model)) : Ranked model before original :=
  let proposal : Search.Proposal model := ⟨preparation⟩
  ⟨proposal,proposal.quality model before original,rfl⟩

def prefer {model : Context (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)}
    {before : Current model} {original : List (Action model)} (left right : Ranked model before original) : Ranked model before original :=
  if left.value < right.value then right else left

/-- Scores are computed once after reservation; selection compares stored Nats. -/
def choose (catalogue : List (List (Action model))) :=
  ((catalogue.map (rank model before original)).foldl prefer (rank model before original [])).proposal

theorem chosen_is_baseline_or_registered (catalogue : List (List (Action model))) :
    (choose model before original catalogue).preparation = [] ∨ (choose model before original catalogue).preparation ∈ catalogue := by
  have member (rows : List (Ranked model before original)) (start : Ranked model before original) :
      rows.foldl prefer start = start ∨ rows.foldl prefer start ∈ rows := by
    induction rows generalizing start with
    | nil => exact Or.inl rfl
    | cons head tail ih =>
      rcases ih (prefer start head) with same | inside
      · rw [List.foldl_cons,same]
        unfold prefer;split
        next => exact Or.inr List.mem_cons_self
        next => exact Or.inl rfl
      · exact Or.inr (List.mem_cons_of_mem _ inside)
  rcases member (catalogue.map (rank model before original)) (rank model before original []) with same | inside
  · exact Or.inl (congrArg (fun row : Ranked model before original => row.proposal.preparation) same)
  · obtain ⟨preparation,registered,same⟩ := List.mem_map.mp inside
    apply Or.inr
    change ((catalogue.map (rank model before original)).foldl prefer (rank model before original [])).proposal.preparation ∈ catalogue
    rw [←same]
    exact registered

theorem chosen_maximal (catalogue : List (List (Action model))) (preparation : List (Action model)) (inside : preparation ∈ catalogue) :
    (rank model before original preparation).value ≤ (choose model before original catalogue).quality model before original := by
  have left (a b : Ranked model before original) : a.value ≤ (prefer a b).value := by
    unfold prefer;split
    next strict => exact Nat.le_of_lt strict
    next => exact Nat.le_refl _
  have right (a b : Ranked model before original) : b.value ≤ (prefer a b).value := by
    unfold prefer;split
    next => exact Nat.le_refl _
    next notStrict => exact Nat.le_of_not_gt notStrict
  have initial (rows : List (Ranked model before original)) (start : Ranked model before original) : start.value ≤ (rows.foldl prefer start).value := by
    induction rows generalizing start with
    | nil => exact Nat.le_refl _
    | cons head tail ih => exact (left start head).trans (ih _)
  have bound (rows : List (Ranked model before original)) (start row : Ranked model before original) (present : row ∈ rows) :
      row.value ≤ (rows.foldl prefer start).value := by
    induction rows generalizing start with
    | nil => cases present
    | cons head tail ih =>
      rcases List.mem_cons.mp present with rfl | rest
      · exact (right start row).trans (initial tail _)
      · exact ih _ rest
  have result := bound _ (rank model before original []) (rank model before original preparation) (List.mem_map.mpr ⟨preparation,inside,rfl⟩)
  exact result.trans_eq ((catalogue.map (rank model before original)).foldl prefer (rank model before original [])).exact

theorem chosen_preparation_is_legal (catalogue : List (List (Action model))) :
    ((choose model before original catalogue).prepared model before).succeeded = true := by
  have keep (rows : List (Ranked model before original)) (start : Ranked model before original)
      (legal : (start.proposal.prepared model before).succeeded = true) :
      (((rows.foldl prefer start).proposal).prepared model before).succeeded = true := by
    induction rows generalizing start with
    | nil => exact legal
    | cons head tail ih =>
      apply ih
      by_cases strict : start.value < head.value
      · rw [prefer,if_pos strict]
        have positive : 0 < head.proposal.quality model before original := by
          rw [←head.exact];omega
        unfold Search.Proposal.quality at positive
        split at positive
        next paid => exact paid
        next => omega
      · rw [prefer,if_neg strict];exact legal
  exact keep _ _ rfl

def requestVisits (preparation : List (Action model)) : Nat :=
  let proposal : Search.Proposal model := ⟨preparation⟩
  3*(proposal.prepared model before).output.length +
    (proposal.retry model before original).output.length

theorem every_evaluated_request_visit_is_reserved (catalogue : List (List (Action model))) :
    requestVisits model before original [] + (catalogue.map (requestVisits model before original)).sum + catalogue.length <
      comparisonUnits original catalogue := by
  have each (preparation : List (Action model)) :
      requestVisits model before original preparation ≤ 3*preparation.length+original.length := by
    have prepared := (Search.Proposal.prepared model before
      (⟨preparation⟩ : Search.Proposal model)).output_is_bounded_by_the_original_word
    have retried := (Search.Proposal.retry model before original
      (⟨preparation⟩ : Search.Proposal model)).output_is_bounded_by_the_original_word
    change (Search.Proposal.prepared model before
      (⟨preparation⟩ : Search.Proposal model)).output.length ≤ preparation.length at prepared
    change requestVisits model before original preparation ≤ _
    dsimp only [requestVisits]
    omega
  have sum : (catalogue.map (requestVisits model before original)).sum ≤
      (catalogue.map fun preparation => 3*preparation.length+original.length).sum := by
    induction catalogue with
    | nil => exact Nat.le_refl _
    | cons head tail ih =>
      simp only [List.map_cons,List.sum_cons]
      exact Nat.add_le_add (each head) ih
  have baseline := each []
  simp only [List.length_nil,Nat.mul_zero,Nat.zero_add] at baseline
  unfold comparisonUnits
  omega

end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Future.Recovery.Search.Billing
