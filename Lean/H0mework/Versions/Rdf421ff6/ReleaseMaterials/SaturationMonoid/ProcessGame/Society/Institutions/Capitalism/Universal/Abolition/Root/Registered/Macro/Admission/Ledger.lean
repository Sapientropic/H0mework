import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Admission.Source
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Installation.Admission.Casts

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Admission

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot DebtActivationWorld DebtActivationLedger
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  {input : ProgrammeSource.Input Party Good Port Technology Instrument}
  {depth count prefixLimit renewalLimit sourceDepth sourceCount : Nat}
  {start : Physical.Cursor Party Good Port Technology Instrument}
  {proposal : Compile.RawInput Party Good Port Technology Instrument} {sourcePosition : Nat}
  {review : Option (ReviewPhase.ContextAt input)}
  (frame : NativeFrame (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition)
  {origin : frame.V.Current}
  (registered : HeadRegistration (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition frame origin)

def actionEvolution (current : Current frame registered) :
    LedgerWriteEvolutionAt (N frame registered)
      (activeLedger (frame.sourceSupport current.1) (state frame registered current.2))
      (activeLedger (frame.sourceSupport (frame.next current.1)) (actionTarget frame registered current.2)) :=
  match actionReceipt frame registered current.2 with
  | .inl paid => jointStepLedgerEvolution (frame.wholeEvolution current.1) (frame.entry current.1) paid
  | .inr carried => Financial.Installation.wholeTransport (frame.wholeEvolution current.1) (frame.entry current.1) carried

def wholeEvolution (current : Current frame registered) :
    LedgerWriteEvolutionAt (N frame registered) ⟨supportAt frame registered current⟩
      ⟨supportAt frame registered (next frame registered current)⟩ :=
  Eq.mp (congrArg (fun target => LedgerWriteEvolutionAt (N frame registered)
    (activeLedger (frame.sourceSupport current.1) (state frame registered current.2))
    (activeLedger (frame.sourceSupport (frame.next current.1)) target))
      (next_state frame registered current.2).symm) (actionEvolution frame registered current)

theorem first_destination_is_original_admission :
    HEq (wholeEvolution frame registered (initial frame registered)).destination
      (jointStepLedgerEvolution (frame.successor origin).ledgerEvolution
        (frame.entry origin) registered.firstStep.step).destination := by
  unfold wholeEvolution actionEvolution
  dsimp only [initial, state, actionReceipt]
  refine HEq.trans (b := (jointStepLedgerEvolution (frame.wholeEvolution origin)
      (frame.entry origin) registered.firstStep.step).destination) ?_ ?_
  · exact Financial.Installation.Admission.destination_cast_heq
      (fun target => activeLedger (frame.sourceSupport (frame.next origin)) target)
      (next_state frame registered EventAt.pending).symm _
  · exact Financial.Installation.Admission.joint_destination_cast_heq
      (congrArg frame.root.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.account.supportOf
        (frame.target_occurrence origin)) (frame.successor origin).ledgerEvolution _ _

theorem entry_finite (current : Current frame registered) :
    Finite (OpenResponsibilityAt (N frame registered) (supportAt frame registered current)) := by
  let oldFinite : Finite (OpenResponsibilityAt frame.N (frame.sourceSupport current.1)) := frame.entries_finite current.1
  let presentation := activeInventoryPresentation (N := frame.N) (law := registered.law)
    (state frame registered current.2) (ConstructivePresentation.refl
      (OpenResponsibilityAt frame.N (frame.sourceSupport current.1)))
  exact Finite.of_surjective presentation.forward
    (fun entry => ⟨presentation.backward entry, presentation.forward_backward entry⟩)

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Admission
