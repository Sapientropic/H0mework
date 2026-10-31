import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Entitlement.Source.Leg

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Entitlement.Source

open Universal.Source.Program Universal.Source.ProgrammeControl

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  {law : RawLaw Party Good Port Technology Instrument}
  {before : RawCurrent Party Good Technology Instrument}
  {word : RawEvent Party Good Port Technology Instrument}

def PrivateTaking (leg : Leg law before word) : Prop :=
  leg.item.val.request.signer = leg.recipient ∧ leg.sender ∉ leg.item.val.request.consents ∧
  ∃ port ∈ law.requiredPorts leg.item.val.before leg.item.val.request,
    law.controller leg.item.val.before.technology port = leg.recipient ∧
      PrivatePhase law leg.item.val.before port leg.sender

instance (leg : Leg law before word) : Decidable (PrivateTaking leg) := by
  unfold PrivateTaking
  infer_instance

structure ControlledReturn (leg : Leg law before word) : Prop where
  privateTaking : PrivateTaking leg
  actualCapital : Kernel.Discovery.ReturnIncidence.selected law before word leg.item.val.index = true

instance (leg : Leg law before word) : Decidable (ControlledReturn leg) := by
  exact decidable_of_iff (PrivateTaking leg ∧
    Kernel.Discovery.ReturnIncidence.selected law before word leg.item.val.index = true)
    ⟨fun source => ⟨source.1,source.2⟩,fun controlled => ⟨controlled.privateTaking,controlled.actualCapital⟩⟩

def inspectControl (leg : Leg law before word) : Option (PLift (ControlledReturn leg)) :=
  if privateTaking : PrivateTaking leg then
    if capital : Kernel.Discovery.ReturnIncidence.selected law before word leg.item.val.index = true then
      some ⟨⟨privateTaking,capital⟩⟩
    else none
  else none

theorem control_retains_the_original_capital_and_actual_item (leg : Leg law before word)
    (controlled : ControlledReturn leg) :
    ∃ kernel ∈ Kernel.Discovery.ReturnIncidence.kernels law before word,
      ∃ route ∈ Kernel.Discovery.ReturnIncidence.route law before word kernel,
        kernel.proposal.Checks law before word ∧ route.item.val ∈ law.rawItems before word ∧
          route.item.val.index = leg.item.val.index := by
  obtain ⟨kernel,member,route,inside,checked,_access,original,same,_operation⟩ :=
    Kernel.Discovery.ReturnIncidence.selected_payment_keeps_original_control_and_both_actual_items
      law before word leg.item.val.index controlled.actualCapital
  exact ⟨kernel,member,route,inside,checked,original,same⟩

theorem a_signed_gift_cannot_be_relabelled_as_this_private_taking (leg : Leg law before word)
    (signed : leg.item.val.request.signer = leg.sender) : ¬ ControlledReturn leg := by
  intro controlled
  exact leg.distinct (signed.symm.trans controlled.privateTaking.1)

theorem an_explicit_original_consent_is_not_erased (leg : Leg law before word)
    (consent : leg.sender ∈ leg.item.val.request.consents) : ¬ ControlledReturn leg :=
  fun controlled => controlled.privateTaking.2.1 consent

theorem the_public_reparation_interpreter_cannot_be_mistaken_for_private_taking
    (opened : ∀ technology port person, law.allowed technology port person = true)
    (leg : Leg law before word) : ¬ ControlledReturn leg := by
  rintro ⟨⟨_,_,port,_,_,phase⟩,_⟩
  have denied := phase.2
  rw [opened] at denied
  cases denied

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Entitlement.Source
