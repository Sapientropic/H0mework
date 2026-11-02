import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.StageAccountabilityRuntime

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.IncidentChallenge

open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Institutions.Capitalism.Universal.Source.ProgrammeFace
open Distributed.Recall.Information.Agency.Protocol Continuation

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (model : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (start : Cursor model.source.code) (stages : List (EventHistory.Stage (code := model.source.code)))

abbrev final := EventHistory.execute start stages
abbrev native := LocalContentRuntime.native model (final model start stages)
abbrev family := Native.Authority.programme (native model start stages)
abbrev sourceIndex := Native.Authority.sourceIndex (native model start stages)
abbrev depth := (final model start stages).source.history.length + 1 + (final model start stages).cut

theorem actual_trace_items (row : StageTrace.Record (code := model.source.code))
    (inside : row ∈ StageTrace.records start stages) :
    Registered.traceItems (final model start stages).source.input
      (ProgrammeHistory.visitAt (final model start stages).source.input (EventStep.boundary row.cursor)).current = StageTrace.items row := by
  have actual := StageTrace.every_record_is_a_completed_occurrence_of_the_final_source start stages row inside
  change model.source.code.law.rawItems ((final model start stages).source.currentAt _)
    (ProgrammeSource.rawEvent (final model start stages).source.input _) = _
  rw [← actual.1, ← actual.2.1]
  rfl

def position (row : StageTrace.Record (code := model.source.code))
    (inside : row ∈ StageTrace.records start stages) (index : Fin (StageTrace.items row).length) :
    Mandate.Challenge.Position (family model start stages) (sourceIndex model start stages) :=
  ⟨EventStep.boundary row.cursor, ⟨index.val, by
    change index.val < (Registered.traceItems (final model start stages).source.input
      (ProgrammeHistory.visitAt (final model start stages).source.input (EventStep.boundary row.cursor)).current).length
    rw [actual_trace_items model start stages row inside]
    exact index.isLt⟩⟩

private theorem get_same {α : Type} (left right : List α) (same : left = right) (index : Fin right.length) :
    left.get ⟨index.val, by rw [same]; exact index.isLt⟩ = right.get index := by subst left; rfl

theorem position_item_is_the_actual_item (row : StageTrace.Record (code := model.source.code))
    (inside : row ∈ StageTrace.records start stages) (index : Fin (StageTrace.items row).length) :
    (position model start stages row inside index).item (family model start stages) (sourceIndex model start stages) =
      (StageTrace.items row).get index :=
  get_same _ _ (actual_trace_items model start stages row inside) index

theorem execution_advances_the_actual_boundary (cursor : Cursor model.source.code)
    (tail : List (EventHistory.Stage (code := model.source.code))) :
    EventStep.boundary (EventHistory.execute cursor tail) = EventStep.boundary cursor + tail.length := by
  induction tail generalizing cursor with
  | nil => simp [EventHistory.execute]
  | cons stage tail ih =>
    rcases stage with ⟨protocol, rival⟩
    rw [EventHistory.execute, ih]
    change EventStep.boundary cursor + 1 + tail.length = EventStep.boundary cursor + ((protocol, rival) :: tail).length
    simp only [List.length_cons]
    omega

theorem actual_item_is_before_the_native_inventory (row : StageTrace.Record (code := model.source.code))
    (inside : row ∈ StageTrace.records start stages) :
    EventStep.boundary row.cursor < depth model start stages + 2 := by
  have before : EventStep.boundary row.cursor < EventStep.boundary (final model start stages) := by
    induction stages generalizing start with
    | nil => simp [StageTrace.records] at inside
    | cons stage tail ih =>
      rcases stage with ⟨protocol, rival⟩
      rcases List.mem_cons.mp inside with same | later
      · subst row
        rw [execution_advances_the_actual_boundary]
        change EventStep.boundary start < EventStep.boundary start + ((protocol, rival) :: tail).length
        simp
      · exact ih (start.after protocol rival) later
  dsimp [depth, EventStep.boundary] at before ⊢
  omega

def read (row : StageTrace.Record (code := model.source.code))
    (inside : row ∈ StageTrace.records start stages) (index : Fin (StageTrace.items row).length) :=
  Mandate.Challenge.read (family model start stages) (sourceIndex model start stages)
    (position model start stages row inside index)

theorem actual_signed_active_item_generates_a_native_claim
    (row : StageTrace.Record (code := model.source.code)) (inside : row ∈ StageTrace.records start stages)
    (index : Fin (StageTrace.items row).length)
    (signed : Mandate.Challenge.Submission (scope := model.scope) ((StageTrace.items row).get index).request)
    (valid : model.source.code.law.Valid ((StageTrace.items row).get index).before ((StageTrace.items row).get index).request)
    (active : ((StageTrace.items row).get index).before.technology.holder.isSome = true ∨
      ((StageTrace.items row).get index).before.technology.offered.isSome = true) :
    ∃ claim, read model start stages row inside index = some claim ∧
      claim.position = position model start stages row inside index ∧
      (⟨claim, Mandate.Challenge.through (family model start stages) (sourceIndex model start stages) claim
        (depth model start stages + 2)⟩ : Sigma fun original => Native.Authority.ChallengeHistory (native model start stages) original) ∈
          (Native.Authority.fullGenerate (native model start stages) (depth model start stages)).challenges := by
  let pos := position model start stages row inside index
  have original := position_item_is_the_actual_item model start stages row inside index
  have signedAt : Mandate.Challenge.Submission (scope := model.scope) (pos.item (family model start stages) (sourceIndex model start stages)).request := by
    rw [original]; exact signed
  have validAt : (Mandate.law model.base model.scope).Valid
      (pos.item (family model start stages) (sourceIndex model start stages)).before
      (pos.item (family model start stages) (sourceIndex model start stages)).request := by
    rw [original, ← model.law_exact]; exact valid
  have activeAt : (pos.item (family model start stages) (sourceIndex model start stages)).before.technology.holder.isSome = true ∨
      (pos.item (family model start stages) (sourceIndex model start stages)).before.technology.offered.isSome = true := by
    rw [original]; exact active
  have existsClaim : ∃ claim, read model start stages row inside index = some claim := by
    unfold read Mandate.Challenge.read
    split
    · exact ⟨_, rfl⟩
    · rename_i unsigned
      exact False.elim (unsigned signedAt)
  obtain ⟨claim, decoded⟩ := existsClaim
  exact ⟨claim, decoded, Mandate.Challenge.read_position _ _ _ claim decoded,
    Native.Authority.every_actual_signed_challenge_is_natively_admitted (native model start stages) pos claim decoded
      (depth model start stages) (actual_item_is_before_the_native_inventory model start stages row inside)⟩

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.IncidentChallenge
