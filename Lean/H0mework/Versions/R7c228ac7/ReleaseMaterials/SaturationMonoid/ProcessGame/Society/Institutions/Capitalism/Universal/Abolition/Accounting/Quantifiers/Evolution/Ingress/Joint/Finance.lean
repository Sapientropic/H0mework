import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Background
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance.Installation.Enter

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Background

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Source.Program Innovation

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  {mechanism : Trials.Mechanism Party Good Port Technology Instrument}
  {past : List (RawEvent Party Good Port Technology Instrument)} {nature : mechanism.Nature}
  {response : Control.HistoryResponse (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)}
  (seed : Global.Seed (mechanism := mechanism) (past := past) (nature := nature) (response := response))

def shape := Abolition.Root.Epoch.Finance.Installation.Generated.shape seed.input seed.depth seed.count

theorem actual_visit_is_the_native_compilers_exact_target :
    (visit seed).current = (original seed).native.V.nativeTarget
      ((original seed).native.program.emit (original seed).visit.current).write := by
  exact Option.some.inj ((successor seed).next_eq.symm.trans
    (congrArg EvolutionAt.nextCurrent?
      ((original seed).native.program.emit (original seed).visit.current).structural_eq))

theorem the_actual_cursor_is_the_original_next_cursor :
    cursor seed = Financial.Installation.Cursor.next seed.input ((original seed).cursor seed.input) :=
  (congrArg (original seed).native.cursor (actual_visit_is_the_native_compilers_exact_target seed)).trans
    ((original seed).native.next_exact (original seed).visit.current)

theorem the_productive_row_and_the_actual_background_visit_have_the_same_support :
    (Abolition.Accounting.Root.Reentry.Frame.support seed.claim seed.current).1 =
      (original seed).native.root.toAuthoritativeRoot.toRoot.supportAt (visit seed).current := by
  let selected := (original seed).native.program.emit (original seed).visit.current
  have same := Financial.Installation.Admission.successor_support_eq_of_native
    _ selected.write selected.structural_eq selected.targetOccurrence selected.evolution selected.generated_eq (successor seed)
  have emitted := congrArg (original seed).native.root.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.account.supportOf
    selected.target_emitted
  have current := congrArg (original seed).native.root.toAuthoritativeRoot.toRoot.supportAt
    (actual_visit_is_the_native_compilers_exact_target seed).symm
  exact (the_live_productive_row_keeps_the_actual_background_support seed).trans (same.trans (emitted.trans current))

theorem all_existing_native_rows_are_registered_at_this_actual_visit :
    (shape seed).Ready seed.input (visit seed).current := by
  rw [actual_visit_is_the_native_compilers_exact_target seed]
  exact Abolition.Root.Epoch.Finance.Installation.Shape.ready_next seed.input (shape seed)
    (original seed).visit.current
    (Abolition.Root.Epoch.Finance.Installation.Generated.all_registered_rows_are_at_the_actual_current
      seed.input seed.depth seed.count)

def world := (shape seed).world seed.input seed.depth seed.count
def translation := (shape seed).translation seed.input seed.depth seed.count
def nativeAccount := Abolition.Root.Epoch.Finance.Legacy.generated seed.input seed.depth seed.count (account seed)

def enterEvolution := (shape seed).enterEvolution seed.input seed.depth seed.count (visit seed).current
  (all_existing_native_rows_are_registered_at_this_actual_visit seed)

theorem every_original_financial_row_reads_one_actual_current_account :
    (shape seed).AllRead seed.input seed.depth seed.count (nativeAccount seed)
      ((shape seed).enteredSupport seed.input seed.depth seed.count (visit seed).current) :=
  (shape seed).entry_reads_one_unchanged_account seed.input seed.depth seed.count (visit seed).current
    (all_existing_native_rows_are_registered_at_this_actual_visit seed)

theorem reentering_does_not_change_any_original_claim_or_its_budget
    (row : OpenResponsibilityAt (world seed)
      ((shape seed).mappedSupport seed.input seed.depth seed.count (visit seed).current)) :
    ((enterEvolution seed).destination row).1.claim = row.claim ∧
      ((enterEvolution seed).destination row).1.progressBudget = row.progressBudget :=
  ⟨((enterEvolution seed).destination row).2.toDebtLineage.claim_eq.symm,
    (shape seed).enterEvolution_preserves_budget seed.input seed.depth seed.count (visit seed).current
      (all_existing_native_rows_are_registered_at_this_actual_visit seed) row⟩

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Background
