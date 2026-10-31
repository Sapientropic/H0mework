import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Runtime.Drain.Fold
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Clearing.Physical
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Clearing.Head
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Evolving.Native.Ordinary
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Evolving.Native.Raw

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Clearing

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion Source.Program
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root Abolition.Root.Registered Abolition.Root.Registered.Macro Evolution

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (current : Evolving.NativeCurrent (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (request : Request Party Good Port Technology Instrument)
  (selected : current.actual.proposal current.reader = .primitive request)

variable (complete : ¬ Public.Inquiry.HasWork current.frame current.actual.actual)
  (noConsents : request.consents = [])
  (valid : (Physical.Public.interpreter current.input).Valid
    (Public.Scope.actualState current.input current.depth current.count current.prefixLimit current.renewalLimit
      current.oldPast current.actual.snapshot).raw request)

local notation "body" => current.raw complete
local notation "items" => Public.Accounting.items current.input current.depth current.count current.prefixLimit
  current.renewalLimit current.oldPast (Factory.Direct.selectedStart current.full current.sourceActual current.reader)

include selected noConsents valid

theorem one_actual_native_step_consumes_the_whole_primitive_account :
    ((body).ordinary).actual.actual.account =
      Epoch.Finance.consumeVisit current.input current.depth current.count
        (Public.Accounting.tag (body).input (body).depth (body).count (body).prefixLimit
          (body).renewalLimit (body).oldPast (body).start)
        (Public.Accounting.visit (body).input (body).depth (body).count (body).prefixLimit
          (body).renewalLimit (body).oldPast (body).start) current.actual.actual.account := by
  obtain ⟨item,single,present⟩ := the_actual_primitive_has_its_own_financial_head current request selected complete noConsents valid
  change (Public.Accounting.nativeNext (body).input (body).depth (body).count (body).prefixLimit (body).renewalLimit
    (body).oldPast (body).start (body).actual.actual).account = _
  refine (Public.Accounting.every_actual_head_has_its_literal_source_account (body).input (body).depth (body).count
    (body).prefixLimit (body).renewalLimit (body).oldPast (body).start (body).actual.actual rfl item present).trans ?_
  change (Epoch.Finance.consume current.input current.depth current.count item current.actual.actual.account).next current.input current.depth current.count =
    Epoch.Finance.consumeVisit current.input current.depth current.count
      (Public.Accounting.tag current.input current.depth current.count current.prefixLimit current.renewalLimit
        current.oldPast (Factory.Direct.selectedStart current.full current.sourceActual current.reader))
      (Public.Accounting.visit current.input current.depth current.count current.prefixLimit current.renewalLimit
        current.oldPast (Factory.Direct.selectedStart current.full current.sourceActual current.reader)) current.actual.actual.account
  rw [Evolution.Ingress.Joint.Material.Runtime.Drain.the_original_financial_consumption_is_its_same_ordered_fold]
  change _ = (items).foldl _ current.actual.actual.account
  rw [single]
  rfl

theorem the_consumed_primitive_is_ready_for_its_next_actual_request :
    ¬ Public.Inquiry.HasWork ((body).ordinary).frame ((body).ordinary).actual.actual := by
  obtain ⟨item,single,present⟩ := the_actual_primitive_has_its_own_financial_head current request selected complete noConsents valid
  have stepped : Public.Accounting.nativeNext (body).input (body).depth (body).count (body).prefixLimit
      (body).renewalLimit (body).oldPast (body).start (body).actual.actual =
        (body).actual.actual.afterItem rfl item := by
    unfold Public.Accounting.nativeNext
    rw [dif_pos (body).bodyPaid]
    rw [present]
  have facts := Public.Accounting.Current.after_item_reads_the_source_generated_native_account (body).actual.actual rfl item
  change ¬ ((Public.Accounting.nativeNext (body).input (body).depth (body).count (body).prefixLimit (body).renewalLimit
      (body).oldPast (body).start (body).actual.actual).bodyPaid = false ∨
    (Public.Accounting.item? (body).input (body).depth (body).count (body).prefixLimit (body).renewalLimit
      (body).oldPast (body).start (Public.Accounting.nativeNext (body).input (body).depth (body).count (body).prefixLimit
        (body).renewalLimit (body).oldPast (body).start (body).actual.actual)).isSome = true)
  rw [stepped]
  simp only [facts.2.2,Bool.true_eq_false,Public.Accounting.item?,if_true,facts.2.1]
  change ¬ (False ∨ (items[1]?).isSome = true)
  rw [single]
  change ¬ (False ∨ false = true)
  simp

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Clearing
