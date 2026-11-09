import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Revision.InstalledTheory
import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Actual.Run.Disposition

set_option autoImplicit false

open private consumeItems from
  H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Actual.Run.Receipts

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Revision

open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Quantities.Execution (endAt next query)
open Reparation.Actual Reparation.Actual.Allocation

noncomputable section

variable {Party Good Port Technology Instrument Community : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Instrument] [DecidableEq Community]
  {seed : Root.Cut Party Good Port Technology Instrument} {community : Party → Community}

private abbrev HasSemanticSurface {cut : Root.Cut Party Good Port Technology Instrument}
    (state : StateAt seed community cut) : Prop :=
  state.resident.root.toAuthoritativeRoot.source.lawSurface = TheoryState.rootSemantic state.world

private theorem rebase_keeps_semantic_surface
    {cut other : Root.Cut Party Good Port Technology Instrument}
    (state : StateAt seed community cut) (same : cut = other)
    (installed : HasSemanticSurface state) : HasSemanticSurface (state.rebase same) := by
  cases same
  exact installed

variable {past : Script Party Good Port Technology Instrument} (input : Input Party Good Port Technology Instrument)

private theorem posted_has_semantic_surface (state : State seed community past) :
    HasSemanticSurface (posted state input) := by
  have same (safe : Reparation.History.NoFinancialBirth (query (endAt seed past) input)) :
      HasSemanticSurface (sameNext state input safe) := by
    change (samePrepared state input safe).entered.root.toAuthoritativeRoot.source.lawSurface = _
    unfold samePrepared
    apply filing_preserves_the_root_semantic_surface
    rfl
  unfold posted
  split
  · exact same _
  · exact same _
  · rename_i work registered selected _
    exact rebase_keeps_semantic_surface _ _ rfl

private theorem receipt_items_keep_semantic_surface
    {positions : List (Position seed past input)} {rows : List (Occurrence seed community × Balance)}
    (trace : ItemWrites (community := community) past input positions rows)
    (state : StateAt seed community (next (endAt seed past) input))
    (same : state.stack.balances = rows) (installed : HasSemanticSurface state) :
    HasSemanticSurface (consumeItems past input trace state same).val := by
  induction trace generalizing state with
  | nil => exact installed
  | next tail ih => exact ih _ _ rfl

/-- Every original write reuses the root-semantic compiler, including
native accounting, financial registration and partial receipts. -/
theorem the_original_runtime_reinstalls_semantic_theory (state : State seed community past) :
    let reached := advance state input
    reached.resident.root.toAuthoritativeRoot.source.lawSurface =
      TheoryState.rootSemantic reached.world :=
  rebase_keeps_semantic_surface _ _
    (receipt_items_keep_semantic_surface input _ _ rfl (posted_has_semantic_surface input state))

theorem every_nonempty_original_run_installs_semantic_theory
    (history : Script Party Good Port Technology Instrument) (nonempty : history ≠ []) :
    let reached := run seed community history
    reached.resident.root.toAuthoritativeRoot.source.lawSurface =
      TheoryState.rootSemantic reached.world := by
  change HasSemanticSurface (run seed community history)
  induction history using List.reverseRecOn with
  | nil => exact (nonempty rfl).elim
  | append_singleton earlier next _ =>
    rw [run_snoc]
    exact the_original_runtime_reinstalls_semantic_theory next (run seed community earlier)

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Revision
