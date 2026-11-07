import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Runtime.Retirement.CompleteLedger.Word
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Runtime.Retirement.CompleteLedger.Fold
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.BalanceConservation.Readout

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Runtime.Retirement.CompleteLedger

open ResponsibilityLifecycle
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root.Epoch.Finance

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument) (depth count : Nat)

open Source.Program

def archiveRequest (law : RawLaw Party Good Port Technology Instrument)
    (obligation : AdmittedObligation (vocabulary input depth count)) : Request Party Good Port Technology Instrument :=
  ⟨obligation.content.debtor input depth count,[],law.issuerPort (obligation.content.instrument input depth count),[],
    .settle (obligation.content.instrument input depth count) (obligation.content.debtor input depth count)
      (obligation.content.debtor input depth count) 0⟩

def archiveWord (law : RawLaw Party Good Port Technology Instrument)
    (before : (process input depth count).GeneratedState) : RawEvent Party Good Port Technology Instrument :=
  before.current.slots.filterMap fun slot => match slot with
    | .live obligation => some (archiveRequest input depth count law obligation)
    | .terminal _ => none

def completeWord (law : RawLaw Party Good Port Technology Instrument)
    (before : (process input depth count).GeneratedState) : RawEvent Party Good Port Technology Instrument :=
  nativeWord input depth count law before ++ archiveWord input depth count law before

theorem the_original_live_row_generates_its_own_zero_boundary_request
    (law : RawLaw Party Good Port Technology Instrument) (before : (process input depth count).GeneratedState)
    (obligation : AdmittedObligation (vocabulary input depth count)) (listed : .live obligation ∈ before.current.slots) :
    archiveRequest input depth count law obligation ∈ archiveWord input depth count law before :=
  List.mem_filterMap.mpr ⟨.live obligation,listed,rfl⟩

theorem every_archive_request_is_an_actual_zero_settlement
    (law : RawLaw Party Good Port Technology Instrument) (before : (process input depth count).GeneratedState)
    (request : Request Party Good Port Technology Instrument) (listed : request ∈ archiveWord input depth count law before) :
    ∃ instrument debtor, request.operation = .settle instrument debtor debtor 0 ∧ request.consents = [] := by
  obtain ⟨slot,_,selected⟩ := List.mem_filterMap.mp listed
  cases slot with
  | terminal archive => cases selected
  | live obligation =>
      cases Option.some.inj selected
      exact ⟨_,_,rfl,rfl⟩

theorem archive_boundaries_do_not_request_principal_twice
    (law : RawLaw Party Good Port Technology Instrument) (before : (process input depth count).GeneratedState)
    (instrument : Instrument) (debtor holder : Party) :
    wordValue (archiveWord input depth count law before) instrument debtor holder = 0 := by
  apply List.sum_eq_zero
  intro amount listed
  obtain ⟨request,original,rfl⟩ := List.mem_map.mp listed
  obtain ⟨source,borrower,operation,_⟩ := every_archive_request_is_an_actual_zero_settlement input depth count law before request original
  simp only [requestValue,operation,ite_self]

theorem the_complete_source_word_has_exactly_the_original_principal
    (law : RawLaw Party Good Port Technology Instrument) (before : (process input depth count).GeneratedState)
    (instrument : Instrument) (debtor holder : Party) :
    wordValue (completeWord input depth count law before) instrument debtor holder =
      ledgerClaims input depth count before.current instrument debtor holder := by
  change ((nativeWord input depth count law before ++ archiveWord input depth count law before).map _).sum = _
  rw [List.map_append,List.sum_append]
  change wordValue (nativeWord input depth count law before) instrument debtor holder +
    wordValue (archiveWord input depth count law before) instrument debtor holder = _
  rw [the_native_settlement_word_contains_exactly_the_whole_current_ledger,archive_boundaries_do_not_request_principal_twice,add_zero]

theorem the_complete_source_word_is_a_nonnegative_payment_inventory
    (law : RawLaw Party Good Port Technology Instrument) (before : (process input depth count).GeneratedState) :
    PaymentWord (completeWord input depth count law before) := by
  intro request listed
  rcases List.mem_append.mp listed with positive | archive
  · exact every_generated_settlement_request_has_its_original_nonnegative_share input depth count law before request positive
  · obtain ⟨instrument,debtor,operation,_⟩ := every_archive_request_is_an_actual_zero_settlement input depth count law before request archive
    exact ⟨instrument,debtor,debtor,0,operation,le_refl _⟩

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Runtime.Retirement.CompleteLedger
