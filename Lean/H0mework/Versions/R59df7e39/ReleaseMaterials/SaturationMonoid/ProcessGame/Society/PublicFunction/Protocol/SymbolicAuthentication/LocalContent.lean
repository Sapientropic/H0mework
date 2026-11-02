import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.CursorSettlement

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.LocalContent

open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Distributed.Recall.Information.Agency.Protocol
open Continuation

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (code : Code Party Good Port (Mandate.State Party Technology) Instrument)
  (domain : List (Cursor code))

abbrev Point := Fin domain.length
abbrev cursor (point : Point code domain) := domain[point.val]

def fibre (site : Fin code.sites) (reading : Fin code.signals) : List (Point code domain) :=
  (List.finRange domain.length).filter fun point => CursorSettlement.observation (cursor code domain point) site = reading

theorem mem_fibre_iff (site : Fin code.sites) (reading : Fin code.signals) (point : Point code domain) :
    point ∈ fibre code domain site reading ↔ CursorSettlement.observation (cursor code domain point) site = reading := by
  simp [fibre]

inductive ResultData (Point Body : Type) where
  | unseen
  | missing (point : Point)
  | ambiguous (first second : Point)
  | available (body : Body)
  deriving DecidableEq

abbrev Result := ResultData (Point code domain)
  (Settlement.Statement (Party := Party) (Good := Good) (Instrument := Instrument))

/-- The body is chosen from the public observation fibre. The actual world is
not an input, and the evaluator is the retained source's completed execution. -/
def produce (site : Fin code.sites) (reading : Fin code.signals) (scope : Scope) : Result code domain :=
  match fibre code domain site reading with
  | [] => .unseen
  | first :: rest =>
    match CursorSettlement.quote (cursor code domain first) scope with
    | none => .missing first
    | some body => match rest.find? (fun point => decide (CursorSettlement.quote (cursor code domain point) scope ≠ some body)) with
      | some other => .ambiguous first other
      | none => .available body

theorem available_is_nonempty_and_correct_at_every_compatible_point
    (site : Fin code.sites) (reading : Fin code.signals) (scope : Scope)
    (body : Settlement.Statement (Party := Party) (Good := Good) (Instrument := Instrument))
    (known : produce code domain site reading scope = .available body) :
    (∃ point, point ∈ fibre code domain site reading) ∧
      ∀ point ∈ fibre code domain site reading, CursorSettlement.quote (cursor code domain point) scope = some body := by
  unfold produce at known
  split at known <;> try contradiction
  rename_i first rest actual
  split at known <;> try contradiction
  rename_i generated quoted
  split at known <;> try contradiction
  rename_i absent
  cases known
  refine ⟨by rw [actual]; exact ⟨first, List.mem_cons_self⟩, ?_⟩
  intro point inside
  rw [actual] at inside
  rcases List.mem_cons.mp inside with same | later
  · exact same ▸ quoted
  · have denied := List.find?_eq_none.mp absent point later
    simpa using denied

theorem missing_retains_a_generated_compatible_point_without_a_body
    (site : Fin code.sites) (reading : Fin code.signals) (scope : Scope) (point : Point code domain)
    (blocked : produce code domain site reading scope = .missing point) :
    point ∈ fibre code domain site reading ∧ CursorSettlement.quote (cursor code domain point) scope = none := by
  unfold produce at blocked
  split at blocked <;> try contradiction
  rename_i first rest actual
  split at blocked
  · cases blocked
    exact ⟨by rw [actual]; exact List.mem_cons_self, by assumption⟩
  · split at blocked <;> contradiction

theorem a_nonempty_constant_fibre_generates_the_available_body
    (site : Fin code.sites) (reading : Fin code.signals) (scope : Scope)
    (body : Settlement.Statement (Party := Party) (Good := Good) (Instrument := Instrument))
    (inhabited : ∃ point, point ∈ fibre code domain site reading)
    (constant : ∀ point ∈ fibre code domain site reading, CursorSettlement.quote (cursor code domain point) scope = some body) :
    produce code domain site reading scope = .available body := by
  unfold produce
  cases actual : fibre code domain site reading with
  | nil => obtain ⟨point, impossible⟩ := inhabited; simp [actual] at impossible
  | cons first rest =>
    have head := constant first (by rw [actual]; exact List.mem_cons_self)
    dsimp only
    have absent : rest.find? (fun point => decide (CursorSettlement.quote (cursor code domain point) scope ≠ some body)) = none := by
      apply List.find?_eq_none.mpr
      intro point inside
      simp [constant point (by rw [actual]; exact List.mem_cons_of_mem _ inside)]
    simp only [head, absent]

theorem ambiguity_retains_two_generated_equal_observations_with_different_contents
    (site : Fin code.sites) (reading : Fin code.signals) (scope : Scope) (first second : Point code domain)
    (blocked : produce code domain site reading scope = .ambiguous first second) :
    first ∈ fibre code domain site reading ∧ second ∈ fibre code domain site reading ∧
      CursorSettlement.quote (cursor code domain first) scope ≠ CursorSettlement.quote (cursor code domain second) scope := by
  unfold produce at blocked
  split at blocked <;> try contradiction
  rename_i head rest actual
  split at blocked <;> try contradiction
  rename_i body quoted
  split at blocked <;> try contradiction
  rename_i other selected
  cases blocked
  refine ⟨by rw [actual]; exact List.mem_cons_self, ?_, ?_⟩
  · rw [actual]
    exact List.mem_cons_of_mem _ (List.mem_of_find?_eq_some selected)
  · have different := of_decide_eq_true (List.find?_some (p := fun point => decide
      (CursorSettlement.quote (cursor code domain point) scope ≠ some body)) selected)
    rw [quoted]
    exact Ne.symm different

theorem equal_local_observations_get_the_same_generated_result
    (site : Fin code.sites) (first second : Point code domain) (scope : Scope)
    (same : CursorSettlement.observation (cursor code domain first) site = CursorSettlement.observation (cursor code domain second) site) :
    produce code domain site (CursorSettlement.observation (cursor code domain first) site) scope =
      produce code domain site (CursorSettlement.observation (cursor code domain second) site) scope := by rw [same]

theorem available_is_correct_for_every_compatible_cursor
    (site : Fin code.sites) (reading : Fin code.signals) (scope : Scope)
    (body : Settlement.Statement (Party := Party) (Good := Good) (Instrument := Instrument))
    (known : produce code domain site reading scope = .available body)
    (actual : Cursor code) (inside : actual ∈ domain)
    (same : CursorSettlement.observation actual site = reading) : CursorSettlement.quote actual scope = some body := by
  obtain ⟨point, actualAt⟩ := List.mem_iff_get.mp inside
  have pointSame : cursor code domain point = actual := actualAt
  have quote := (available_is_nonempty_and_correct_at_every_compatible_point code domain site reading scope body known).2 point
    ((mem_fibre_iff code domain site reading point).mpr (by rw [pointSame]; exact same))
  simpa only [pointSame] using quote

variable (model : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)) (budget : Nat) (installed : List (Rule model.source.code))

abbrev publicDomain := Continuation.history model budget installed

/-- Public generation fixes the domain before any actual-point query. -/
def generate (site : Fin model.source.code.sites) (reading : Fin model.source.code.signals) (scope : Scope) :=
  produce model.source.code (publicDomain model budget installed) site reading scope

theorem a_generated_local_query_recovers_the_original_financial_occurrence
    (site : Fin model.source.code.sites) (point : Point model.source.code (publicDomain model budget installed))
    (scope : Scope) (body : Settlement.Statement (Party := Party) (Good := Good) (Instrument := Instrument))
    (known : generate model budget installed site
      (CursorSettlement.observation (cursor model.source.code (publicDomain model budget installed) point) site) scope = .available body) :
    CursorSettlement.quote (cursor model.source.code (publicDomain model budget installed) point) scope = some body := by
  exact (available_is_nonempty_and_correct_at_every_compatible_point model.source.code (publicDomain model budget installed)
    site _ scope body known).2 point ((mem_fibre_iff _ _ _ _ _).mpr rfl)

omit installed in
theorem the_first_actual_local_query_is_correct_for_any_adaptive_external_input
    (world : Distributed.Recall.Information.World model budget) (protocol : Rule model.source.code)
    (rival : Opponent model.source.code) (site : Fin model.source.code.sites) (scope : Scope)
    (body : Settlement.Statement (Party := Party) (Good := Good) (Instrument := Instrument))
    (known : generate model budget [protocol] site
      (CursorSettlement.observation ((ofWorld model budget world).after protocol rival) site) scope = .available body) :
    CursorSettlement.quote ((ofWorld model budget world).after protocol rival) scope = some body := by
  let original := ofWorld model budget world
  let represented := original.after protocol (finiteRival original rival)
  have inside : represented ∈ publicDomain model budget [protocol] :=
    every_generated_table_produces_its_own_successor model.source.code (initial model budget) protocol original
      (every_original_world_is_in_the_initial_domain model budget world) (externalTable original rival)
      (Residual.restriction_is_generated _ _ _ rival)
  have stateEq := one_original_external_table_preserves_every_actual_ordinal_state original protocol rival 1
  have same := congrArg (fun state : State model.source.code => state.frame.inbox site) stateEq
  change CursorSettlement.observation represented site = CursorSettlement.observation (original.after protocol rival) site at same
  have quoted := available_is_correct_for_every_compatible_cursor model.source.code (publicDomain model budget [protocol]) site _ scope
    body known represented inside same
  rw [CursorSettlement.actual_successor_quote_is_preserved_by_the_generated_external_table original protocol rival scope] at quoted
  exact quoted

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.LocalContent
