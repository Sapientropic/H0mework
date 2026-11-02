import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Control.Scenario.Source
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.ProgrammeControl.Kernel.Core

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Control.Scenario

open Source.Program Source.ProgrammeControl
open SaturationMonoid.ProcessGame.Society.PublicFunction

def capitalItem (index : Fin capitalWord.length) := itemAt law start capitalWord index

def capitalProposal : Kernel.Proposal law start capitalWord where
  access :=
    { access := capitalItem ⟨2,by decide +kernel⟩
      necessity := capitalItem ⟨2,by decide +kernel⟩
      mode := .used
      accessHolder := 0
      recipient := 0
      port := true
      accessGood := .life
      necessityGood := .life
      delivery := [] }
  reciprocity := .claim (capitalItem ⟨0,by decide +kernel⟩)
  disposal :=
    { position := capitalItem ⟨4,by decide +kernel⟩
      request := ownerConsume
      good := .material }

set_option maxHeartbeats 800000 in
theorem the_original_capital_constitution_is_actually_checked :
    capitalProposal.Checks law start capitalWord := by decide +kernel

def originalCapital : Kernel.CapitalRelationKernel law start capitalWord :=
  (Kernel.compile law start capitalWord capitalProposal).get (by
    simp only [Kernel.compile, dif_pos the_original_capital_constitution_is_actually_checked]
    rfl)

theorem the_old_control_is_an_original_capital_relation :
    Nonempty (Kernel.CapitalRelationKernel law start capitalWord) := ⟨originalCapital⟩

theorem the_controller_consents_only_to_the_rent_preserving_offer :
    ownerConsents (offeredRent 1) = [2] ∧ ownerConsents (offeredRent 2) = [] := by decide +kernel

theorem the_new_technology_attempt_has_no_controller_signature :
    (discovery 2).signer = 0 ∧ (discovery 2).consents = [] := by decide +kernel

set_option maxHeartbeats 800000 in
theorem the_private_rule_blocks_the_actual_funded_new_technology :
    ¬ law.Valid
      ((law.execute seed 0 ((mechanism false).funding ++ (mechanism false).investmentWord)).final)
      (discovery 2) := by decide +kernel

set_option maxHeartbeats 800000 in
theorem public_interpretation_executes_the_same_real_technology_attempt :
    openLaw.Valid
      ((openLaw.execute seed 0 ((mechanism true).funding ++ (mechanism true).investmentWord)).final)
      (discovery 2) := by decide +kernel

theorem the_actual_new_technology_was_not_in_the_quoted_menu :
    Distributed.Event.adversary (discovery 2) ∉ (code false).eventAlphabet := by
  simp [code, discovery, ownerConsents, offeredRent]

theorem the_open_rule_cannot_generate_another_full_capital_relation
    (current : Current) (word : RawEvent Party Good Bool Nat Unit) :
    ¬ Nonempty (Kernel.CapitalRelationKernel openLaw current word) := by
  rintro ⟨capital⟩
  have privatePhase := (capital.original_control_and_reproduced_phase openLaw current word).2.2.1
  have unavailable := privatePhase.2
  change true = false at unavailable
  cases unavailable

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Control.Scenario
