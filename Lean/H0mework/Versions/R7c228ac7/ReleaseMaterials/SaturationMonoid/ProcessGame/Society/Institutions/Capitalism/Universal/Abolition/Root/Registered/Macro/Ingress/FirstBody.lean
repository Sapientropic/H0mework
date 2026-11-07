import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Ingress.Translation
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Accounting.State

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Ingress

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument) (depth sourceStart : Nat)
  (datum : Datum input depth sourceStart) (prefixLimit renewalLimit : Nat)
  (review : Option (ReviewPhase.ContextAt input) := none)

abbrev targetWorld := Accounting.N (review := review) input depth (cut input depth sourceStart) prefixLimit renewalLimit
  depth (cut input depth sourceStart) Physical.initial (proposal (review := review) input depth sourceStart datum prefixLimit renewalLimit) 0

abbrev bodyInitial := Accounting.initial (review := review) input depth (cut input depth sourceStart) prefixLimit renewalLimit
  depth (cut input depth sourceStart) Physical.initial (proposal (review := review) input depth sourceStart datum prefixLimit renewalLimit) 0

abbrev bodyNext := Accounting.next (review := review) input depth (cut input depth sourceStart) prefixLimit renewalLimit
  depth (cut input depth sourceStart) Physical.initial (proposal (review := review) input depth sourceStart datum prefixLimit renewalLimit) 0
  (bodyInitial (review := review) input depth sourceStart datum prefixLimit renewalLimit)

abbrev bodySupport := Accounting.supportAt (review := review) input depth (cut input depth sourceStart) prefixLimit renewalLimit
  depth (cut input depth sourceStart) Physical.initial (proposal (review := review) input depth sourceStart datum prefixLimit renewalLimit) 0

def originalSupport := (frame input depth sourceStart).native.root.toAuthoritativeRoot.toRoot.supportAt
  (frame input depth sourceStart).visit.current

abbrev translation := sourceTranslation input depth (cut input depth sourceStart) depth (cut input depth sourceStart)

theorem initial_support_is_the_translated_original_occurrence :
    bodySupport (review := review) input depth sourceStart datum prefixLimit renewalLimit
      (bodyInitial (review := review) input depth sourceStart datum prefixLimit renewalLimit) =
    (translation input depth sourceStart).support.forward (originalSupport input depth sourceStart) := rfl

def initialLedger : ConstructiveRetract
    (OpenResponsibilityAt (frame input depth sourceStart).native.N (originalSupport input depth sourceStart))
    (OpenResponsibilityAt (targetWorld (review := review) input depth sourceStart datum prefixLimit renewalLimit)
      (bodySupport (review := review) input depth sourceStart datum prefixLimit renewalLimit
        (bodyInitial (review := review) input depth sourceStart datum prefixLimit renewalLimit))) :=
  (translation input depth sourceStart).oldOpenLedger (originalSupport input depth sourceStart)

theorem initial_ledger_has_no_fresh_row
    (row : OpenResponsibilityAt (targetWorld (review := review) input depth sourceStart datum prefixLimit renewalLimit)
      (bodySupport (review := review) input depth sourceStart datum prefixLimit renewalLimit
        (bodyInitial (review := review) input depth sourceStart datum prefixLimit renewalLimit))) :
    (initialLedger (review := review) input depth sourceStart datum prefixLimit renewalLimit).forward
      ((initialLedger (review := review) input depth sourceStart datum prefixLimit renewalLimit).backward row) = row :=
  translated_ledger_has_no_fresh_rows input depth (cut input depth sourceStart) depth (cut input depth sourceStart) _ row

theorem the_first_body_keeps_the_actual_drained_account_and_full_inventory :
    (bodyNext (review := review) input depth sourceStart datum prefixLimit renewalLimit).position = 0 ∧
    (bodyNext (review := review) input depth sourceStart datum prefixLimit renewalLimit).account =
      Epoch.Finance.Legacy.generated input depth (cut input depth sourceStart) ((frame input depth sourceStart).cursor input).account ∧
    Accounting.pending (review := review) input depth (cut input depth sourceStart) prefixLimit renewalLimit depth (cut input depth sourceStart)
      Physical.initial (proposal (review := review) input depth sourceStart datum prefixLimit renewalLimit) 0
      (bodyNext (review := review) input depth sourceStart datum prefixLimit renewalLimit) =
        Inventory.items (review := review) input depth (cut input depth sourceStart) prefixLimit renewalLimit Physical.initial
          (proposal (review := review) input depth sourceStart datum prefixLimit renewalLimit) := ⟨rfl, rfl, rfl⟩

theorem body_physical_result_is_the_same_selected_source :
    Accounting.physical (review := review) input depth (cut input depth sourceStart) prefixLimit renewalLimit depth (cut input depth sourceStart)
      Physical.initial (proposal (review := review) input depth sourceStart datum prefixLimit renewalLimit) 0
      (bodyNext (review := review) input depth sourceStart datum prefixLimit renewalLimit) =
    Physical.stateAt input depth (cut input depth sourceStart) prefixLimit renewalLimit
      (Physical.next (Mandatory.executionCursor (review := review) input depth (cut input depth sourceStart) prefixLimit renewalLimit
        Physical.initial (proposal (review := review) input depth sourceStart datum prefixLimit renewalLimit))).past := rfl

theorem body_write_classification_is_the_original_physical_result :
    Accounting.writes (review := review) input depth (cut input depth sourceStart) prefixLimit renewalLimit depth (cut input depth sourceStart)
      Physical.initial (proposal (review := review) input depth sourceStart datum prefixLimit renewalLimit) 0
      (bodyInitial (review := review) input depth sourceStart datum prefixLimit renewalLimit) =
    Physical.materialWrite input depth (cut input depth sourceStart) prefixLimit renewalLimit
      (Mandatory.executionCursor (review := review) input depth (cut input depth sourceStart) prefixLimit renewalLimit
        Physical.initial (proposal (review := review) input depth sourceStart datum prefixLimit renewalLimit)) := rfl

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Ingress

#print axioms SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Ingress.initial_support_is_the_translated_original_occurrence
#print axioms SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Ingress.initial_ledger_has_no_fresh_row
#print axioms SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Ingress.the_first_body_keeps_the_actual_drained_account_and_full_inventory
#print axioms SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Ingress.body_physical_result_is_the_same_selected_source
#print axioms SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Ingress.body_write_classification_is_the_original_physical_result
