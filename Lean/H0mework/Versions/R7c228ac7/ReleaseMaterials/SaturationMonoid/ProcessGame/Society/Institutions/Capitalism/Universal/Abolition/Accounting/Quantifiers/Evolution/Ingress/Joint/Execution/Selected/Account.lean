import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Execution.Selected.Actual
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Family

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Execution.Selected

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root Source.Program Innovation Quantifiers.Joint

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument] [DecidableEq Technology]
  {mechanism : Trials.Mechanism Party Good Port Technology Instrument}
  {past : List (RawEvent Party Good Port Technology Instrument)} {nature : mechanism.Nature}
  {response : Control.HistoryResponse (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)}
  (seed : Global.Seed (mechanism := mechanism) (past := past) (nature := nature) (response := response))
  (claim : Entitlement.Source.Claim (window seed))

def before := Background.nativeAccount seed

def after := Epoch.Finance.consumeVisit seed.input seed.depth seed.count
  (tag seed claim) (visit seed claim) (before seed)

def nativeRun : (Epoch.Finance.process seed.input seed.depth seed.count).Run (before seed).current
    (after seed claim).current :=
  Epoch.Finance.consumeVisit_run seed.input seed.depth seed.count (tag seed claim) (visit seed claim) (before seed)

def family := (Background.family seed).after (after seed claim) ⟨nativeRun seed claim⟩

theorem every_original_slot_keeps_its_claim_at_the_original_address :
    (before seed).current.slots.map (Epoch.Finance.slotClaim seed.input seed.depth seed.count) <+:
      (after seed claim).current.slots.map (Epoch.Finance.slotClaim seed.input seed.depth seed.count) := by
  unfold after
  exact Epoch.Finance.consumeVisit_preserves_original_claims seed.input seed.depth seed.count
    (tag seed claim) (visit seed claim) (before seed)

theorem the_entire_original_ordered_lifecycle_history_is_retained :
    (before seed).current.history <+: (after seed claim).current.history := by
  rw [(nativeRun seed claim).history_eq]
  exact List.prefix_append _ _

theorem the_financial_family_reads_one_actual_next_account :
    (family seed claim).initial = after seed claim ∧
      (family seed claim).N = Background.world seed := ⟨rfl,rfl⟩

omit [DecidableEq Technology] in
theorem the_original_pending_queue_is_not_reconsumed_as_representation :
    Background.pending seed = Financial.Installation.Cursor.pending seed.input (Background.cursor seed) := rfl

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Execution.Selected
