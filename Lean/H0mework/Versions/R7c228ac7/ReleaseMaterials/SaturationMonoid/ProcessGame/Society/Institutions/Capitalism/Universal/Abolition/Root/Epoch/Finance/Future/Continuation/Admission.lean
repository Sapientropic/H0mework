import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance.Future.Continuation.Family
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance.Future.Structure
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance.Future.Finiteness

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance.Future.Continuation

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot DebtActivationWorld
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  {input : ProgrammeSource.Input Party Good Port Technology Instrument} {depth count : Nat}
  {world : WorldRelationNetwork} {anchor : (process input depth count).GeneratedState}
  (family : AccountFamily input depth count world anchor)
  (before : (process input depth count).GeneratedState)
  (prior : NativeTail input depth count family.initial before)
  (claim : Claim input depth count)

/-- A born source row already carries its native path from the original
admission. This read family retains that row without admitting it again. -/
def registeredFamily
    (registered : NativeTail input depth count (Activation.admitted input depth count before claim) anchor) :
    AccountFamily input depth count
    (ExtendedNetwork family.N (Activation.law input depth count before claim))
    anchor where
  support := fun account native =>
    ⟨family.support account native, some (.registered account (appendTail input depth count registered native))⟩
  owner := fun account native => oldEntry (family.owner account native)
  itemEvolution := fun account native item => Financial.Installation.wholeTransport
    (family.itemEvolution account native item)
    (family.owner account native)
    (Activation.SameDebtTransport.actualInstruction (input := input) (depth := depth) (count := count)
      (before := before) (claim := claim) account (appendTail input depth count registered native) item)
  item_keys := fun account native item => Financial.Installation.wholeTransport_keeps_keys _ _ _
    (family.item_keys account native item)
  entries_finite := fun account native => Finiteness.active_finite _ (family.entries_finite account native)
  open_fibres := Structure.extended_subsingleton _ family.open_fibres
  entry := fun support => oldEntry (state? := support.2) (family.entry support.1)
  entry_key := fun left right => congrArg Sum.inl (family.entry_key left.1 right.1)
  disposition := fun support kind => match kind with
    | .supportSettlement => family.disposition support.1 .supportSettlement
    | .transfer => .inl (family.disposition support.1 .transfer)
    | .lawSurfaceExtension => .inl (family.disposition support.1 .lawSurfaceExtension)

include prior in
private theorem registeredTail : NativeTail input depth count family.initial
    (Activation.admitted input depth count before claim) :=
  appendTail input depth count prior ⟨.step .nil (.admit (P := process input depth count) claim)⟩

/-- The first-write consumer owns the admission step. The resulting family
is a restriction of the same whole account, with its new row retained. -/
def admittedFamily : AccountFamily input depth count
    (ExtendedNetwork family.N (Activation.law input depth count before claim))
    (Activation.admitted input depth count before claim) :=
  registeredFamily
    (family.after (Activation.admitted input depth count before claim) (registeredTail family before prior claim))
    before claim ⟨.nil⟩

theorem admission_continuation_is_the_same_registered_world :
    (admittedFamily family before prior claim).N =
      ExtendedNetwork family.N (Activation.law input depth count before claim) ∧
      (admittedFamily family before prior claim).initial = Activation.admitted input depth count before claim :=
  ⟨rfl, rfl⟩

theorem admission_continuation_does_not_clear_the_original_principal :
    (admittedFamily family before prior claim).initial.current.slots[before.current.slots.length]? =
      some (.live (admission input depth count claim).toObligation) :=
  Activation.first_slot_is_the_actual_original_loan input depth count before claim

#print axioms admittedFamily
#print axioms registeredFamily
#print axioms admission_continuation_does_not_clear_the_original_principal

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance.Future.Continuation
