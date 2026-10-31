import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Admission.Context
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Joint.Planning.Report

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open Source.Program Innovation Quantifiers.Joint
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument] [DecidableEq Technology]
  {mechanism : Trials.Mechanism Party Good Port Technology Instrument}
  {past : List (RawEvent Party Good Port Technology Instrument)} {nature : mechanism.Nature}
  {response : Control.HistoryResponse (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)}
  (seed : Global.Seed (mechanism := mechanism) (past := past) (nature := nature) (response := response))
  (claim : Entitlement.Source.Claim (Quantifiers.Joint.window seed))

def shared := Admission.declaredShared seed claim
def current := Admission.current seed claim
def word := Planning.selected seed claim (shared seed claim)
def report := Planning.report seed claim (shared seed claim)

/-- Code for this inquiry, compiled from its actual active faces. Its
financial execution must still be consumed by the original whole account. -/
def input : ProgrammeSource.Input Party Good Port Technology Instrument where
  law := Factory.Context.readLaw (current seed claim)
  initial := Factory.Context.readRaw (current seed claim)
  instructions := word seed claim

theorem the_programme_reads_the_actual_active_interpreter :
    (input seed claim).law = actualLaw seed := Factory.Context.readLaw_eq (current seed claim)

theorem the_programme_simultaneously_excludes_every_capital_relation :
    Global.NoCapital (input seed claim).law :=
  Eq.mpr (congrArg Global.NoCapital (the_programme_reads_the_actual_active_interpreter seed claim)) seed.noCapital

theorem the_programme_reads_the_actual_single_material_cursor :
    (input seed claim).initial = (shared seed claim).raw := Factory.Context.readRaw_eq (current seed claim)

theorem the_programme_is_the_source_selected_payable_prefix :
    (input seed claim).instructions = Planning.selected seed claim (shared seed claim) := rfl

theorem every_compiled_original_item_is_valid :
    ∀ item ∈ (input seed claim).law.rawItems (input seed claim).initial (input seed claim).instructions,
      (input seed claim).law.Valid item.before item.request := by
  rw [the_programme_reads_the_actual_active_interpreter,the_programme_reads_the_actual_single_material_cursor]
  exact Planning.every_selected_original_inventory_item_is_actual seed claim (shared seed claim)

theorem original_resources_force_the_actual_shared_payment
    (enough : Planning.Enough seed claim (shared seed claim)) :
    Planning.ActualSuccess seed claim (shared seed claim) (input seed claim).instructions :=
  Planning.sufficient_source_resources_force_the_actual_shared_payment seed claim (shared seed claim) enough

omit [DecidableEq Technology] in
theorem the_original_root_still_owns_both_compiled_material_rows :
    (Factory.Context.support (current seed claim)).1.2 = some (.current (shared seed claim)) ∧
      (Factory.Context.support (current seed claim)).2 = some (shared seed claim) :=
  Admission.both_original_material_rows_point_to_the_same_declared_current seed claim

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material
