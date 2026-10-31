import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Installation.Admission.Source
import Mathlib.Data.Fintype.EquivFin

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Installation.Admission

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open DebtActivationWorld

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)
  (frame : NativeFrame input) {origin : frame.V.Current}
  (registered : Registration input frame origin)

theorem entry_finite (current : Current input frame registered) :
    Finite (OpenResponsibilityAt (N input frame registered) (supportAt input frame registered current)) := by
  let image := frame.program.emit current.1
  have oldFinite : Finite (OpenResponsibilityAt frame.N
      (frame.root.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.account.supportOf
        (frame.root.emitted current.1))) :=
    Finite.of_surjective image.rows.sourceEntryAt
      (fun entry => ⟨image.coverage.destinationIndex entry, image.coverage.destination_sound entry⟩)
  let presentation := activeInventoryPresentation (N := frame.N) (law := registered.law input frame)
    (state input frame registered current.2) (ConstructivePresentation.refl
      (OpenResponsibilityAt frame.N
        (frame.root.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.account.supportOf
          (frame.root.emitted current.1))))
  exact Finite.of_surjective presentation.forward
    (fun entry => ⟨presentation.backward entry, presentation.forward_backward entry⟩)

@[instance_reducible] noncomputable def entryFintype (current : Current input frame registered) :
    Fintype (OpenResponsibilityAt (N input frame registered) (supportAt input frame registered current)) := by
  haveI : Finite (OpenResponsibilityAt (N input frame registered) (supportAt input frame registered current)) :=
    entry_finite input frame registered current
  exact Fintype.ofFinite _

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Installation.Admission
