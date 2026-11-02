import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.Budget.Escrow.Capacity
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2500000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.QuotaJoint
open Institutions.Capitalism.Universal.Source.Program
variable {P G O T I : Type} [DecidableEq P] [DecidableEq G] [DecidableEq O] [DecidableEq T] [DecidableEq I]
  {seed : Authority.Bound (Party := P) (Good := G) (Port := O) (Technology := T) (Instrument := I)}
  {driver : Feedback.Input seed.source.code} {cursor : Cursor seed driver}
  {pricing : Future.Recovery.Pricing (Future.Recovery.Action cursor.model)}
  {n : Nat} {reference : Term cursor} {actor : P} {position : Nat}
abbrev SourceScope := Scope cursor pricing n reference actor position
variable (scopes : List (SourceScope (cursor := cursor) (pricing := pricing) (n := n) (reference := reference) (actor := actor) (position := position)))

def frames := scopes.flatMap Whole.frames
abbrev Table := Feedback.Residual.Joint.Table cursor.source.val.code (frames scopes)
def tables := Feedback.Residual.Joint.tables cursor.source.val.code (frames scopes)
abbrev opponent (table : Table scopes) := Feedback.Residual.Joint.respond cursor.source.val.code (frames scopes) table
abbrev restrict (rival : Opponent cursor.source.val.code) := Feedback.Residual.Joint.restrict cursor.source.val.code (frames scopes) rival

theorem restriction_is_generated (rival : Opponent cursor.source.val.code) : restrict scopes rival ∈ tables scopes :=
  Feedback.Residual.Joint.restriction_is_generated _ _ _

theorem frame_included (scope : SourceScope (cursor := cursor) (pricing := pricing) (n := n) (reference := reference) (actor := actor) (position := position))
    (member : scope ∈ scopes) (frame : Feedback.Residual.Joint.Frame cursor.source.val.code)
    (listed : frame ∈ Whole.frames scope) : frame ∈ frames scopes := List.mem_flatMap.mpr ⟨scope,member,listed⟩

omit [DecidableEq O] [DecidableEq T] in
private theorem forecast_suffix (code : Code P G O (Mandate.State P T) I)
    (schedule : Feedback.Residual.Schedule code) (input : Feedback.Input code) (state : Feedback.State code) (horizon : Nat) :
    forecastWords code schedule input state horizon =
      (Feedback.Residual.run code schedule input state horizon).history.drop state.history.length := by
  rw [forecast_is_the_generated_history_suffix,List.drop_append_of_le_length (Nat.le_refl _),List.drop_length,List.nil_append]

variable {scopes} (scope : SourceScope (cursor := cursor) (pricing := pricing) (n := n) (reference := reference) (actor := actor) (position := position))
  (member : scope ∈ scopes) (span : Nat)
include scope member in
private theorem initial_words (term : Term cursor) (rival : Opponent cursor.source.val.code)
    (bounded : span ≤ cursor.state.remaining) :
    forecastWords cursor.source.val.code (schedule cursor term) ⟨opponent scopes (restrict scopes rival),cursor.input.budget⟩ cursor.state span =
      forecastWords cursor.source.val.code (schedule cursor term) ⟨rival,cursor.input.budget⟩ cursor.state span := by
  have run := Feedback.Residual.Joint.one_table_preserves_each_full_run cursor.source.val.code (frames scopes)
    ⟨cursor.state,Planning.programs cursor⟩ (frame_included scopes scope member _ (by simp [Whole.frames]))
    (schedule cursor term) (schedule_is_generated cursor term) ⟨rival,cursor.input.budget⟩ span bounded
  rw [forecast_suffix,forecast_suffix,run]
include member in
private theorem paid_words (term : Whole.Continuation scope) (rival : Opponent cursor.source.val.code)
    (bounded : n ≤ (comparisonPoint scope).state.remaining) :
    forecastWords cursor.source.val.code (schedule term.point term.term)
        ⟨opponent scopes (restrict scopes rival),term.point.input.budget⟩ term.point.state n =
      forecastWords cursor.source.val.code (schedule term.point term.term)
        ⟨rival,term.point.input.budget⟩ term.point.state n := by
  have run := Feedback.Residual.Joint.one_table_preserves_each_full_run cursor.source.val.code (frames scopes)
    ⟨term.point.state,Planning.programs term.point⟩ (frame_included scopes scope member _ (Whole.every_continuation_frame_is_generated scope term))
    (schedule term.point term.term) (schedule_is_generated term.point term.term) ⟨rival,term.point.input.budget⟩ n bounded
  exact (forecast_suffix _ _ _ _ _).trans ((congrArg (fun state => state.history.drop term.point.state.history.length) run).trans (forecast_suffix _ _ _ _ _).symm)

include member in
theorem same_table_preserves_each_own_target (intent : Intent scope)
    (rival : Opponent cursor.source.val.code) (oldBound : span ≤ cursor.state.remaining)
    (paidBound : n ≤ (comparisonPoint scope).state.remaining) :
    Whole.target scope span intent (opponent scopes (restrict scopes rival)) = Whole.target scope span intent rival := by
  apply Subtype.ext
  cases intent with
  | keep => exact congrArg cursor.install (initial_words scope member span reference rival oldBound)
  | paid term => exact congrArg term.point.install (paid_words scope member term rival paidBound)

include member in
theorem same_table_preserves_the_complete_initial_cut_tensor (intent : Intent scope)
    (rival : Opponent cursor.source.val.code) (oldBound : span ≤ cursor.state.remaining)
    (paidBound : n ≤ (comparisonPoint scope).state.remaining) :
    Whole.tensor scope span intent (opponent scopes (restrict scopes rival)) = Whole.tensor scope span intent rival := by
  have same := same_table_preserves_each_own_target scope member span intent rival oldBound paidBound
  unfold Whole.tensor
  exact congrArg (fun (source : Future.Recovery.SameCodeTarget cursor.model) =>
    let bound : Authority.Bound (Party := P) (Good := G) (Port := O) (Technology := T) (Instrument := I) :=
      ⟨seed.base,seed.scope,source.val,source.indexed.property.1,source.indexed.property.2⟩
    (⟨source.property ▸ Window.evaluate bound cursor.depth (Whole.extent scope span intent),
      Whole.restoration (pricing := pricing) source (Whole.count scope span intent)⟩ : Planning.Tensor cursor)) same

variable (scopes)
theorem finite_comparison_iff_every_same_adaptive_opponent
    (first second : SourceScope (cursor := cursor) (pricing := pricing) (n := n) (reference := reference) (actor := actor) (position := position))
    (firstIn : first ∈ scopes) (secondIn : second ∈ scopes) (left : Intent first) (right : Intent second)
    (oldBound : span ≤ cursor.state.remaining)
    (firstBound : n ≤ (comparisonPoint first).state.remaining) (secondBound : n ≤ (comparisonPoint second).state.remaining)
    (relation : Planning.Tensor cursor → Planning.Tensor cursor → Prop) :
    (∀ table ∈ tables scopes,relation (Whole.tensor first span left (opponent scopes table))
      (Whole.tensor second span right (opponent scopes table))) ↔
      ∀ rival : Opponent cursor.source.val.code,relation (Whole.tensor first span left rival) (Whole.tensor second span right rival) := by
  constructor
  · intro all rival
    have tested := all (restrict scopes rival) (restriction_is_generated scopes rival)
    rw [same_table_preserves_the_complete_initial_cut_tensor first firstIn span left rival oldBound firstBound,
      same_table_preserves_the_complete_initial_cut_tensor second secondIn span right rival oldBound secondBound] at tested
    exact tested
  · intro all table _;exact all _
end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.QuotaJoint
