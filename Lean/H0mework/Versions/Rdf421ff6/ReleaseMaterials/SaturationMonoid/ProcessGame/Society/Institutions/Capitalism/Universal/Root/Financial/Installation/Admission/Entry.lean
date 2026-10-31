import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Installation.Admission.Living
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Installation.Entry

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Installation.Admission

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open DebtActivationWorld DebtActivationLedger

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)
  (frame : NativeFrame input) {origin : frame.V.Current}
  (registered : Registration input frame origin)

theorem whole_destination_old_heq (current : Current input frame registered)
    (entry : OpenResponsibilityAt frame.N (supportAt input frame registered current).1) :
    HEq ((wholeEvolution input frame registered current).destination
      (oldEntry (law := registered.law input frame) (state? := some (state input frame registered current.2)) entry)).1
      (oldEntry (law := registered.law input frame) (state? := some (actionTarget input frame registered current.2))
        ((baseEvolution input frame registered current).destination entry).1) := by
  unfold wholeEvolution
  refine HEq.trans (b := ((actionEvolution input frame registered current).destination
    (oldEntry (law := registered.law input frame) (state? := some (state input frame registered current.2)) entry)).1) ?_ ?_
  · exact destination_entry_cast_heq
      (fun target => activeLedger (supportAt input frame registered (next input frame registered current)).1 target)
      (next_state input frame registered current.2).symm _ _
  · unfold actionEvolution
    cases actionReceipt input frame registered current.2 <;> rfl

theorem base_canonical_entry (protocol : EntryProtocol input frame) (current : Current input frame registered) :
    ((baseEvolution input frame registered current).destination
      (frame.entrySupport (supportAt input frame registered current).1)).1 =
      frame.entrySupport (supportAt input frame registered (next input frame registered current)).1 := by
  apply eq_of_heq
  exact (destination_entry_cast_heq
    (fun occurrence =>
      ⟨frame.root.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.account.supportOf occurrence⟩)
    (frame.program.emit current.1).target_emitted (frame.program.emit current.1).evolution
    (frame.entrySupport (supportAt input frame registered current).1)).trans (protocol.entry_image current.1)

theorem whole_canonical_entry (protocol : EntryProtocol input frame) (current : Current input frame registered) :
    ((wholeEvolution input frame registered current).destination
      (entrySupport input frame registered (supportAt input frame registered current))).1 =
      entrySupport input frame registered (supportAt input frame registered (next input frame registered current)) := by
  apply eq_of_heq
  have old := whole_destination_old_heq input frame registered current
    (frame.entrySupport (supportAt input frame registered current).1)
  rw [base_canonical_entry input frame registered protocol current] at old
  exact old.trans (oldEntry_state_heq (next_state input frame registered current.2).symm
    (frame.entrySupport (supportAt input frame registered (next input frame registered current)).1))

theorem entryProtocol (protocol : EntryProtocol input frame) :
    EntryProtocol input (nativeFrame input frame registered) := by
  constructor
  · intro current
    change HEq ((patch input frame registered current).toLedgerWriteEvolution.destination
      (entrySupport input frame registered (supportAt input frame registered current))).1 _
    have selected := congrFun (patch_destination input frame registered current)
      (entrySupport input frame registered (supportAt input frame registered current))
    exact (heq_of_eq (congrArg Sigma.fst selected)).trans
      (heq_of_eq (whole_canonical_entry input frame registered protocol current))
  · intro current
    change ((patch input frame registered current).toLedgerWriteEvolution.destination
      (entrySupport input frame registered (supportAt input frame registered current))).1 = _
    have selected := congrFun (patch_destination input frame registered current)
      (entrySupport input frame registered (supportAt input frame registered current))
    exact (congrArg Sigma.fst selected).trans (whole_canonical_entry input frame registered protocol current)

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Installation.Admission
