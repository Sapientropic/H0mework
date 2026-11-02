import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Future.Recovery.Source.Cursor

import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Replay.Program.Session
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Future.Recovery.Metering
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  {old : Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)}
  {oldDepth : Nat} {word : List (Action old)}

/-- Construction/metering is one registered service unit. Comparison reserves
one request-interpreter visit per potential check (including the baseline),
three preparation passes, and one selection comparison per catalogue entry. -/
def comparisonUnits (pending : List (Action old)) (catalogue : List (List (Action old))) : Nat :=
  1 + catalogue.length + pending.length +
    (catalogue.map fun preparation => 3*preparation.length+pending.length).sum

structure Ranked (stage : Recovery.Cursor old oldDepth word) where
  proposal : Search.Proposal stage.model
  value : Nat
  exact : value = proposal.quality stage.model stage.before stage.residual

def rank (stage : Recovery.Cursor old oldDepth word) (preparation : List (Action old)) : Ranked stage :=
  let proposal : Search.Proposal stage.model := ⟨preparation⟩
  ⟨proposal,proposal.quality stage.model stage.before stage.residual,rfl⟩

def prefer {stage : Recovery.Cursor old oldDepth word} (left right : Ranked stage) : Ranked stage :=
  if left.value < right.value then right else left

/-- Scores are computed once after reservation; selection compares stored Nats. -/
def choose (stage : Recovery.Cursor old oldDepth word) (catalogue : List (List (Action old))) :=
  ((catalogue.map (rank stage)).foldl prefer (rank stage [])).proposal

theorem chosen_is_baseline_or_registered (stage : Recovery.Cursor old oldDepth word)
    (catalogue : List (List (Action old))) :
    (choose stage catalogue).preparation = [] ∨ (choose stage catalogue).preparation ∈ catalogue := by
  have member (rows : List (Ranked stage)) (start : Ranked stage) :
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
  rcases member (catalogue.map (rank stage)) (rank stage []) with same | inside
  · exact Or.inl (congrArg (fun row : Ranked stage => row.proposal.preparation) same)
  · obtain ⟨preparation,registered,same⟩ := List.mem_map.mp inside
    apply Or.inr
    change ((catalogue.map (rank stage)).foldl prefer (rank stage [])).proposal.preparation ∈ catalogue
    rw [←same]
    exact registered

theorem chosen_maximal (stage : Recovery.Cursor old oldDepth word)
    (catalogue : List (List (Action old))) (preparation : List (Action old)) (inside : preparation ∈ catalogue) :
    (rank stage preparation).value ≤ (choose stage catalogue).quality stage.model stage.before stage.residual := by
  have left (a b : Ranked stage) : a.value ≤ (prefer a b).value := by
    unfold prefer;split
    next strict => exact Nat.le_of_lt strict
    next => exact Nat.le_refl _
  have right (a b : Ranked stage) : b.value ≤ (prefer a b).value := by
    unfold prefer;split
    next => exact Nat.le_refl _
    next notStrict => exact Nat.le_of_not_gt notStrict
  have initial (rows : List (Ranked stage)) (start : Ranked stage) : start.value ≤ (rows.foldl prefer start).value := by
    induction rows generalizing start with
    | nil => exact Nat.le_refl _
    | cons head tail ih => exact (left start head).trans (ih _)
  have bound (rows : List (Ranked stage)) (start row : Ranked stage) (present : row ∈ rows) :
      row.value ≤ (rows.foldl prefer start).value := by
    induction rows generalizing start with
    | nil => cases present
    | cons head tail ih =>
      rcases List.mem_cons.mp present with rfl | rest
      · exact (right start row).trans (initial tail _)
      · exact ih _ rest
  have result := bound _ (rank stage []) (rank stage preparation) (List.mem_map.mpr ⟨preparation,inside,rfl⟩)
  exact result.trans_eq ((catalogue.map (rank stage)).foldl prefer (rank stage [])).exact

theorem chosen_preparation_is_legal (stage : Recovery.Cursor old oldDepth word)
    (catalogue : List (List (Action old))) :
    ((choose stage catalogue).prepared stage.model stage.before).succeeded = true := by
  have keep (rows : List (Ranked stage)) (start : Ranked stage)
      (legal : (start.proposal.prepared stage.model stage.before).succeeded = true) :
      (((rows.foldl prefer start).proposal).prepared stage.model stage.before).succeeded = true := by
    induction rows generalizing start with
    | nil => exact legal
    | cons head tail ih =>
      apply ih
      by_cases strict : start.value < head.value
      · rw [prefer,if_pos strict]
        have positive : 0 < head.proposal.quality stage.model stage.before stage.residual := by
          rw [←head.exact];omega
        unfold Search.Proposal.quality at positive
        split at positive
        next paid => exact paid
        next => omega
      · rw [prefer,if_neg strict];exact legal
  exact keep _ _ rfl

def requestVisits (stage : Recovery.Cursor old oldDepth word) (preparation : List (Action old)) : Nat :=
  let proposal : Search.Proposal stage.model := ⟨preparation⟩
  3*(proposal.prepared stage.model stage.before).output.length +
    (proposal.retry stage.model stage.before stage.residual).output.length

theorem every_evaluated_request_visit_is_reserved (stage : Recovery.Cursor old oldDepth word)
    (catalogue : List (List (Action old))) :
    requestVisits stage [] + (catalogue.map (requestVisits stage)).sum + catalogue.length <
      comparisonUnits stage.residual catalogue := by
  have each (preparation : List (Action old)) :
      requestVisits stage preparation ≤ 3*preparation.length+stage.residual.length := by
    have prepared := (Search.Proposal.prepared stage.model stage.before
      (⟨preparation⟩ : Search.Proposal stage.model)).output_is_bounded_by_the_original_word
    have retried := (Search.Proposal.retry stage.model stage.before stage.residual
      (⟨preparation⟩ : Search.Proposal stage.model)).output_is_bounded_by_the_original_word
    change (Search.Proposal.prepared stage.model stage.before
      (⟨preparation⟩ : Search.Proposal stage.model)).output.length ≤ preparation.length at prepared
    change requestVisits stage preparation ≤ _
    dsimp only [requestVisits]
    omega
  have sum : (catalogue.map (requestVisits stage)).sum ≤
      (catalogue.map fun preparation => 3*preparation.length+stage.residual.length).sum := by
    induction catalogue with
    | nil => exact Nat.le_refl _
    | cons head tail ih =>
      simp only [List.map_cons,List.sum_cons]
      exact Nat.add_le_add (each head) ih
  have baseline := each []
  simp only [List.length_nil,Nat.mul_zero,Nat.zero_add] at baseline
  unfold comparisonUnits
  omega

def restored (stage : Recovery.Cursor old oldDepth word) (catalogue : List (List (Action old))) :
    Recovery.Cursor old oldDepth word := stage.replayPreparation (choose stage catalogue).preparation

end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Future.Recovery.Metering
