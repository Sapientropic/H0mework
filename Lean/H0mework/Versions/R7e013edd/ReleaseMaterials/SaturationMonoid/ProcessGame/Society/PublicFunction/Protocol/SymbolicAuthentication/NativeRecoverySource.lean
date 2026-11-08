import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.NativeRecoveryMaterial

set_option autoImplicit false
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.NativeRecoverySource
open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Distributed.Recall.Information.Agency.Protocol Continuation

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (model : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (start : Cursor model.source.code) (past : NativeReviewRun.Stages model)
  (material : NativeRecoveryMaterial.Ready model start past)

abbrev full := NativeRecoveryMaterial.full model start past material
abbrev row := NativeRecoveryMaterial.row model start past material
abbrev native := IncidentChallenge.native model start (full model start past material)
abbrev family := IncidentChallenge.family model start (full model start past material)
abbrev sourceIndex := IncidentChallenge.sourceIndex model start (full model start past material)
abbrev depth := IncidentChallenge.depth model start (full model start past material)
abbrev ordinal := EventStep.boundary (NativeRecoveryMaterial.current model start past)

theorem the_actual_row_is_in_the_complete_source :
    row model start past material ∈ StageTrace.records start (full model start past material) := by
  rw [full, NativeRecoveryMaterial.full, StageQueue.records_append]
  exact List.mem_append_right _ List.mem_cons_self

def position (index : Fin 2) : Mandate.Challenge.Position (family model start past material) (sourceIndex model start past material) :=
  IncidentChallenge.position model start (full model start past material) (row model start past material)
    (the_actual_row_is_in_the_complete_source model start past material)
    ⟨index.val, by rw [NativeRecoveryMaterial.the_actual_row_has_exactly_two_items]; exact index.isLt⟩

theorem the_two_positions_are_the_complete_actual_visit :
    Mandate.Challenge.positionsAt (family model start past material) (sourceIndex model start past material)
      (ordinal model start past) = [position model start past material 0, position model start past material 1] := by
  apply ReconfirmationClosure.two_positions_are_the_complete_actual_visit
    (family model start past material) (sourceIndex model start past material)
    (position model start past material 0) (position model start past material 1) rfl rfl rfl
  have actual := IncidentChallenge.actual_trace_items model start (full model start past material)
    (row model start past material) (the_actual_row_is_in_the_complete_source model start past material)
  exact (congrArg List.length actual).trans (NativeRecoveryMaterial.the_actual_row_has_exactly_two_items model start past material)

abbrev Original := Native.Authority.Challenge (native model start past material)
def originals : List (Original model start past material) :=
  (NativeReview.inventory model start (full model start past material)).map Sigma.fst
abbrev before (original : Original model start past material) :=
  Mandate.Challenge.through (family model start past material) (sourceIndex model start past material) original (ordinal model start past)
abbrev history (original : Original model start past material) :=
  Mandate.Challenge.through (family model start past material) (sourceIndex model start past material) original (depth model start past material + 2)

def stale (original : Original model start past material) : Bool :=
  match before model start past material original with
  | .closed .. => false
  | .pending target .. => decide ((target.claim _ _).snapshot _ _ ≠
      (EventStep.seed (NativeRecoveryMaterial.current model start past)).current.technology)

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.NativeRecoverySource
