import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Finance
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance.Future.Continuation.Installed

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

/-- The original financial shape at the actual background visit, rather
than the earlier factory cut. Its argument is always the one existing GS. -/
def family : Abolition.Root.Epoch.Finance.Future.Continuation.AccountFamily
    seed.input seed.depth seed.count (world seed) (nativeAccount seed) where
  support := fun target tail => (shape seed).support seed.input seed.depth seed.count (visit seed).current target tail
  owner := fun target tail => (shape seed).currentOwner seed.input seed.depth seed.count (visit seed).current target tail
  itemEvolution := fun target tail item => (shape seed).continueItemEvolution seed.input seed.depth seed.count
    (visit seed).current (all_existing_native_rows_are_registered_at_this_actual_visit seed) target tail item
  item_keys := fun target tail item => Abolition.Root.Epoch.Finance.Future.Structure.shape_evolution_keys
    seed.input seed.depth seed.count (shape seed) (visit seed).current
    (all_existing_native_rows_are_registered_at_this_actual_visit seed) target tail item
  entries_finite := fun target tail => Abolition.Root.Epoch.Finance.Future.Finiteness.shape_support_finite
    seed.input seed.depth seed.count (shape seed) (visit seed).current target tail
  open_fibres := Abolition.Root.Epoch.Finance.Future.Structure.shape_fibres
    seed.input seed.depth seed.count (shape seed)
  entry := Abolition.Root.Epoch.Finance.Future.Foundation.actualEntry seed.input seed.depth seed.count (shape seed)
  entry_key := Abolition.Root.Epoch.Finance.Future.Foundation.actualEntry_key seed.input seed.depth seed.count (shape seed)
  disposition := Abolition.Root.Epoch.Finance.Future.Foundation.actualDisposition seed.input seed.depth seed.count (shape seed)

theorem the_family_starts_at_the_actual_background_account :
    (family seed).initial = nativeAccount seed ∧
      (family seed).currentSupport = (shape seed).enteredSupport seed.input seed.depth seed.count (visit seed).current :=
  ⟨rfl,rfl⟩

theorem all_original_rows_of_the_family_read_one_current_account :
    (shape seed).AllRead seed.input seed.depth seed.count (nativeAccount seed) (family seed).currentSupport :=
  every_original_financial_row_reads_one_actual_current_account seed

theorem every_actual_item_keeps_each_original_financial_identity
    (target : (Abolition.Root.Epoch.Finance.process seed.input seed.depth seed.count).GeneratedState)
    (native : Abolition.Root.Epoch.Finance.Future.Continuation.NativeTail seed.input seed.depth seed.count
      (nativeAccount seed) target)
    (item : Abolition.Root.Epoch.Finance.ActualItem seed.input seed.depth seed.count)
    (row : OpenResponsibilityAt (world seed) ((family seed).support target native)) :
    (((family seed).itemEvolution target native item).destination row).1.1 = row.1 ∧
      (((family seed).itemEvolution target native item).destination row).1.claim = row.claim :=
  (family seed).every_item_carries_the_original_responsibility target native item row

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Background
