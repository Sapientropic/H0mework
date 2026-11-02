import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Installation.Source
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Option

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Installation

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open DebtActivationWorld

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)

omit [DecidableEq Port] in
theorem base_finite (current : (ProgrammeSource.V input).Current) :
    Finite (OpenResponsibilityAt (ProgrammeSource.N input) (ProgrammeSource.supportAt input current)) := by
  apply Finite.of_surjective (fun index : Fin (ProgrammeSource.registrationSize input + 2) =>
    ProgrammeSource.sourceEntry input current (ProgrammeSource.rowAt input index))
  intro entry
  refine ⟨ProgrammeSource.rowIndex input entry.1, ?_⟩
  change ProgrammeSource.sourceEntry input current
    (ProgrammeSource.rowAt input (ProgrammeSource.rowIndex input entry.1)) = entry
  exact (congrArg (ProgrammeSource.sourceEntry input current)
    (ProgrammeSource.rowAt_index input entry.1)).trans (Cursor.sourceEntry_self input current entry)

theorem support_finite (raw : (ProgrammeSource.V input).Current) :
    {current : ResponsibilityState (vocabulary input)} →
    (run : (process input).Run (.empty (vocabulary input)) current) →
    (target : (process input).GeneratedState) →
    (tail : Nonempty ((process input).Run current target.current)) →
    Finite (OpenResponsibilityAt (world input (ProgrammeSource.N input) run)
      (support input (ProgrammeSource.N input) (ProgrammeSource.supportAt input raw) run target tail)) := by
  intro current run
  induction run with
  | nil =>
      intro target tail
      exact base_finite input raw
  | step prior edge ih =>
      intro target tail
      cases edge with
      | admit claim =>
          let oldTail := prependNative input (.admit claim) rfl tail
          have := ih target oldTail
          let presentation := activeInventoryPresentation
            (law := Activation.law input (generatedAccount input prior) claim)
            (.registered target tail) (ConstructivePresentation.refl
              (OpenResponsibilityAt (world input (ProgrammeSource.N input) prior)
                (support input (ProgrammeSource.N input) (ProgrammeSource.supportAt input raw)
                  prior target oldTail)))
          exact Finite.of_surjective presentation.forward
            (fun entry => ⟨presentation.backward entry, presentation.forward_backward entry⟩)
      | cross slot obligation present boundary =>
          exact ih target (prependNative input (.cross slot obligation present boundary) rfl tail)
      | reopen _ _ _ impossible => exact impossible.elim

namespace AccountSource

variable (start : Cursor.State input)

@[instance_reducible] noncomputable def entryFintype (current : Current input start) :
    Fintype (OpenResponsibilityAt (N input start) (supportAt input start current)) := by
  haveI : Finite (OpenResponsibilityAt (N input start) (supportAt input start current)) :=
    support_finite input (Cursor.physicalVisit input current.cursor).current
    start.account.generated current.cursor.account current.native
  exact Fintype.ofFinite _

end AccountSource

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Installation
