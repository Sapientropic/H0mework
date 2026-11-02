import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Future.Recovery.Metering.Selection
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Future.Recovery.Metering.SearchSource
open Institutions.Capitalism.Universal.Source.Program
variable {P G O T I : Type} [DecidableEq P] [DecidableEq G] [DecidableEq O] [DecidableEq T] [DecidableEq I]
  {old : Authority.Bound (Party := P) (Good := G) (Port := O) (Technology := T) (Instrument := I)}
  {oldDepth : Nat} {word : List (Action old)}
abbrev Point := Recovery.Cursor old oldDepth word
variable (stage : Point (old := old) (oldDepth := oldDepth) (word := word))
def retryPoint (preparation : List (Action old))
    (first : Mandate.Replay.Materialized old.base old.scope stage.before preparation) : Current stage.model :=
  ((Search.law stage.model).execute stage.before 0 first.output).final
structure Scored (preparation : List (Action old)) where
  private mk ::
  prepared : Mandate.Replay.Materialized old.base old.scope stage.before preparation
  retried : Mandate.Replay.Materialized old.base old.scope (retryPoint stage preparation prepared) stage.residual
variable {stage} {preparation : List (Action old)}
theorem Scored.prepared_output (made : Scored stage preparation) :
    made.prepared.output = (Search.Proposal.prepared stage.model stage.before ⟨preparation⟩).output := by
  rw [made.prepared.output_exact,made.prepared.path_exact];rfl
theorem Scored.prepared_paid (made : Scored stage preparation) :
    made.prepared.succeeded = (Search.Proposal.prepared stage.model stage.before ⟨preparation⟩).succeeded := by
  rw [made.prepared.succeeded_exact,made.prepared.path_exact];rfl
theorem Scored.retry_output (made : Scored stage preparation) :
    made.retried.output = (Search.Proposal.retry stage.model stage.before stage.residual ⟨preparation⟩).output := by
  rw [made.retried.output_exact,made.retried.path_exact]
  dsimp only [retryPoint,Search.Proposal.retry,Search.Proposal.staged]
  rw [made.prepared_output]
theorem Scored.retry_consumed (made : Scored stage preparation) :
    made.retried.consumed = (Search.Proposal.retry stage.model stage.before stage.residual ⟨preparation⟩).consumed := by
  rw [made.retried.consumed_exact,made.retried.path_exact]
  dsimp only [retryPoint,Search.Proposal.retry,Search.Proposal.staged]
  rw [made.prepared_output]
theorem Scored.retry_residual (made : Scored stage preparation) :
    made.retried.residual = (Search.Proposal.retry stage.model stage.before stage.residual ⟨preparation⟩).residual := by
  rw [made.retried.residual_exact,made.retried.path_exact]
  dsimp only [retryPoint,Search.Proposal.retry,Search.Proposal.staged]
  rw [made.prepared_output]
def Scored.row (made : Scored stage preparation) : Ranked stage :=
  ⟨⟨preparation⟩,if made.prepared.succeeded then made.retried.consumed.length else 0,by
    rw [made.prepared_paid,made.retry_consumed];rfl⟩
theorem Scored.row_exact (made : Scored stage preparation) : made.row = rank stage preparation := by
  unfold Scored.row rank
  congr 1
  rw [made.prepared_paid,made.retry_consumed];rfl

def Scored.endpoint (made : Scored stage preparation) : Point (old := old) (oldDepth := oldDepth) (word := word) :=
  stage.emit (made.prepared.output++made.retried.output) made.retried.consumed made.retried.residual (by
    rw [made.retried.consumed_exact,made.retried.residual_exact];exact made.retried.path.original_split)
theorem Scored.endpoint_exact (made : Scored stage preparation) : made.endpoint = stage.replayPreparation preparation := by
  unfold Scored.endpoint Recovery.Cursor.replayPreparation
  simp only [Search.Proposal.word,made.prepared_output,made.retry_output,made.retry_consumed,made.retry_residual]
  rfl
variable {R S : Type} {depth : Nat}
def mapResult (f : R → S) : {depth : Nat} → Mandate.Replay.Program.Code old.base old.scope R depth → Mandate.Replay.Program.Code old.base old.scope S depth
  | _,.done value => .done (f value)
  | _,.replay before requests next => .replay before requests (fun cache => mapResult f (next cache))
termination_by depth _ => depth
inductive Scores (stage : Point (old := old) (oldDepth := oldDepth) (word := word)) : List (List (Action old)) → Type
  | nil : Scores stage []
  | cons {head tail} (scored : Scored stage head) (rest : Scores stage tail) : Scores stage (head::tail)
def layers : List (List (Action old)) → Nat
  | [] => 0
  | _::tail => layers tail+2
variable (stage)
def compile : (preparations : List (List (Action old))) →
    Mandate.Replay.Program.Code old.base old.scope (Scores stage preparations) (layers preparations)
  | [] => .done .nil
  | head::tail => .replay stage.before head fun first =>
      .replay (retryPoint stage head first) stage.residual fun second =>
        mapResult (fun rest => Scores.cons (⟨first,second⟩ : Scored stage head) rest) (compile tail)
structure Winner where
  preparation : List (Action old)
  scored : Scored stage preparation
variable {stage}
def Winner.row (winner : Winner stage) := winner.scored.row
def Winner.prefer (left right : Winner stage) : Winner stage :=
  if left.row.value < right.row.value then right else left
theorem Winner.prefer_row (left right : Winner stage) : (left.prefer right).row = Metering.prefer left.row right.row := by
  unfold Winner.prefer Metering.prefer;split <;> rfl
def Scores.fold : {preparations : List (List (Action old))} → Scores stage preparations → Winner stage → Winner stage
  | _,.nil,start => start
  | _,.cons head tail,start => tail.fold (start.prefer ⟨_,head⟩)
theorem Scores.fold_exact {preparations : List (List (Action old))} (scores : Scores stage preparations) (start : Winner stage) :
    (scores.fold start).row = (preparations.map (rank stage)).foldl Metering.prefer start.row := by
  induction scores generalizing start with
  | nil => rfl
  | cons scored rest ih =>
    rw [Scores.fold,ih,Winner.prefer_row]
    simp only [List.map_cons,List.foldl_cons,Winner.row,scored.row_exact]
def Scores.winner {catalogue : List (List (Action old))} : Scores stage ([]::catalogue) → Winner stage
  | .cons baseline tail => tail.fold ⟨[],baseline⟩
theorem Scores.winner_exact {catalogue : List (List (Action old))} (scores : Scores stage ([]::catalogue)) :
    scores.winner.row = (catalogue.map (rank stage)).foldl Metering.prefer (rank stage []) := by
  cases scores with
  | cons baseline tail =>
    rw [Scores.winner,Scores.fold_exact]
    simp only [Winner.row,baseline.row_exact]
variable (stage) (catalogue : List (List (Action old)))
abbrev program := compile stage ([]::catalogue)
abbrev Execution := Mandate.Replay.Program.Execution (program stage catalogue)
abbrev Session := Mandate.Replay.Program.Session (program stage catalogue)
def execute : Execution stage catalogue := Mandate.Replay.Program.execute (program stage catalogue)
variable {stage catalogue}
def Execution.winner (execution : Execution stage catalogue) : Winner stage := execution.value.winner
def Execution.endpoint (execution : Execution stage catalogue) := execution.winner.scored.endpoint
theorem Execution.chosen (execution : Execution stage catalogue) : execution.winner.row.proposal = choose stage catalogue :=
  congrArg Ranked.proposal execution.value.winner_exact
theorem Execution.endpoint_exact (execution : Execution stage catalogue) : execution.endpoint = restored stage catalogue := by
  unfold Execution.endpoint
  rw [execution.winner.scored.endpoint_exact]
  have chosen := congrArg Search.Proposal.preparation execution.chosen
  change execution.winner.preparation = (choose stage catalogue).preparation at chosen
  rw [chosen];rfl
structure Archive (old : Authority.Bound (Party := P) (Good := G) (Port := O) (Technology := T) (Instrument := I)) (oldDepth : Nat) (word : List (Action old)) where
  stage : Recovery.Cursor old oldDepth word
  catalogue : List (List (Action old))
  execution : Execution stage catalogue
def Archive.endpoint (archive : Archive old oldDepth word) := archive.execution.endpoint
end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Future.Recovery.Metering.SearchSource
