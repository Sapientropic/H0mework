import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Installation.Admission.Source
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Installation.Admission.Casts

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Installation.Admission

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open DebtActivationWorld DebtActivationLedger

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)
  (frame : NativeFrame input) {origin : frame.V.Current}
  (registered : Registration input frame origin)

def baseEvolution (current : Current input frame registered) :
    LedgerWriteEvolutionAt frame.N
      ⟨(supportAt input frame registered current).1⟩
      ⟨(supportAt input frame registered (next input frame registered current)).1⟩ := by
  have evolution := (frame.program.emit current.1).evolution
  rw [(frame.program.emit current.1).target_emitted] at evolution
  exact evolution

def actionEvolution (current : Current input frame registered) :
    LedgerWriteEvolutionAt (N input frame registered)
      (activeLedger (supportAt input frame registered current).1 (state input frame registered current.2))
      (activeLedger (supportAt input frame registered (next input frame registered current)).1
        (actionTarget input frame registered current.2)) :=
  match actionReceipt input frame registered current.2 with
  | .inl paid => jointStepLedgerEvolution (baseEvolution input frame registered current)
      (frame.entrySupport (supportAt input frame registered current).1) paid
  | .inr carried => wholeTransport (baseEvolution input frame registered current)
      (frame.entrySupport (supportAt input frame registered current).1) carried

def wholeEvolution (current : Current input frame registered) :
    LedgerWriteEvolutionAt (N input frame registered)
      ⟨supportAt input frame registered current⟩ ⟨supportAt input frame registered (next input frame registered current)⟩ :=
  Eq.mp (congrArg (fun target => LedgerWriteEvolutionAt (N input frame registered)
    (activeLedger (supportAt input frame registered current).1 (state input frame registered current.2))
    (activeLedger (supportAt input frame registered (next input frame registered current)).1 target))
      (next_state input frame registered current.2).symm)
    (actionEvolution input frame registered current)

theorem whole_next_keeps_original_claim (current : Current input frame registered)
    (entry : OpenResponsibilityAt (N input frame registered) (supportAt input frame registered current)) :
    ((wholeEvolution input frame registered current).destination entry).1.claim = entry.claim :=
  ((wholeEvolution input frame registered current).destination entry).2.toDebtLineage.claim_eq.symm

theorem first_destination_is_original_joint_admission :
    HEq (wholeEvolution input frame registered (initial input frame registered)).destination
      (jointStepLedgerEvolution (frame.program.emit origin).evolution
        (frame.entrySupport (supportAt input frame registered (initial input frame registered)).1)
        (registered.firstStep input frame).step).destination := by
  unfold wholeEvolution actionEvolution
  dsimp only [initial, state, actionReceipt]
  refine HEq.trans (b := (jointStepLedgerEvolution
    (baseEvolution input frame registered (initial input frame registered))
    (frame.entrySupport (supportAt input frame registered (initial input frame registered)).1)
    (registered.firstStep input frame).step).destination) ?_ ?_
  · exact destination_cast_heq
      (fun target => activeLedger
        (supportAt input frame registered (next input frame registered (initial input frame registered))).1 target)
      (next_state input frame registered EventAt.pending).symm _
  · exact joint_destination_cast_heq
      (congrArg frame.root.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.account.supportOf
        (frame.program.emit origin).target_emitted)
      (frame.program.emit origin).evolution _ _

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Installation.Admission
