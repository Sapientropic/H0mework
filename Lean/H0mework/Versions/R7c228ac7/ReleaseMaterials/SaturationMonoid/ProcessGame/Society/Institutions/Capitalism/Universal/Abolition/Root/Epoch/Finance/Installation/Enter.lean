import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance.Installation.FirstWrite
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance.World.Enter

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance.Installation

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot DebtActivationWorld DebtActivationLedger
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root

noncomputable section

private def stationary (N : WorldRelationNetwork) (support : N.Support) :
    LedgerWriteEvolutionAt N ⟨support⟩ ⟨support⟩ where
  destination := fun entry => ⟨entry, .carried rfl HEq.rfl⟩
  origin := fun entry => ⟨entry, .carried rfl HEq.rfl⟩

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument) (epochDepth epochCount : Nat)

namespace Shape

def enteredSupport {native : Financial.Installation.NativeFrame input} (shape : Shape input native)
    (current : native.V.Current) : (shape.world input epochDepth epochCount).Support :=
  shape.support input epochDepth epochCount current
    (Legacy.generated input epochDepth epochCount (native.cursor current).account) ⟨.nil⟩

def enterEvolution : {native : Financial.Installation.NativeFrame input} → (shape : Shape input native) →
    (current : native.V.Current) → shape.Ready input current →
    LedgerWriteEvolutionAt (shape.world input epochDepth epochCount)
      ⟨shape.mappedSupport input epochDepth epochCount current⟩
      ⟨shape.enteredSupport input epochDepth epochCount current⟩
  | _, .base start _, current, _ =>
      World.enterEvolution input epochDepth epochCount
        (Financial.Installation.Ingress.identityTranslation (ProgrammeSource.N input))
        (Financial.Installation.Cursor.baseSupport input current.cursor)
        (Financial.Installation.Cursor.baseSupport input current.cursor)
        (stationary (ProgrammeSource.N input) (Financial.Installation.Cursor.baseSupport input current.cursor))
        (Financial.Installation.Cursor.baseOwner input current.cursor)
        start.account.generated current.cursor.account current.native
  | _, .born (old := old) prior registered, current, ready => by
      rcases current with ⟨current, event⟩
      cases event with
      | pending => exact ready.2.elim
      | registered native =>
          exact Financial.Installation.wholeTransport
            (enterEvolution prior current ready.1)
            ((prior.translation input epochDepth epochCount).oldOpenLedger _ |>.forward
              (old.entrySupport _))
            (World.LegacyLaw.Transport.enter (input := input) (depth := epochDepth) (count := epochCount)
              (before := registered.before input _) (claim := registered.claim) _ native)

theorem entry_reads_one_unchanged_account {native : Financial.Installation.NativeFrame input}
    (shape : Shape input native) (current : native.V.Current) (ready : shape.Ready input current) :
    shape.AllRead input epochDepth epochCount
      (Legacy.generated input epochDepth epochCount (native.cursor current).account)
      (shape.enteredSupport input epochDepth epochCount current) :=
  shape.ready_support_reads_one_whole_account input epochDepth epochCount current ready _ _

theorem enterEvolution_preserves_budget {native : Financial.Installation.NativeFrame input}
    (shape : Shape input native) (current : native.V.Current) (ready : shape.Ready input current)
    (entry : OpenResponsibilityAt (shape.world input epochDepth epochCount)
      (shape.mappedSupport input epochDepth epochCount current)) :
    ((shape.enterEvolution input epochDepth epochCount current ready).destination entry).1.progressBudget =
      entry.progressBudget := by
  induction shape with
  | base start positive =>
      exact World.enterEvolution_preserves_budget input epochDepth epochCount
        (Financial.Installation.Ingress.identityTranslation (ProgrammeSource.N input))
        (Financial.Installation.Cursor.baseSupport input current.cursor)
        (Financial.Installation.Cursor.baseSupport input current.cursor)
        (stationary (ProgrammeSource.N input) (Financial.Installation.Cursor.baseSupport input current.cursor))
        (Financial.Installation.Cursor.baseOwner input current.cursor) (fun _ => rfl)
        start.account.generated current.cursor.account current.native entry
  | born prior registered inherited =>
      rcases current with ⟨current, event⟩
      cases event with
      | pending => exact ready.2.elim
      | registered native =>
          rcases entry with ⟨responsibility, opened⟩
          cases responsibility with
          | inl original => exact inherited current ready.1 ⟨original, opened⟩
          | inr debt =>
              rcases opened with ⟨⟨same⟩⟩
              subst debt
              rfl

end Shape

namespace Generated

variable (sourceDepth sourceCount : Nat)

def enterEvolution :
    LedgerWriteEvolutionAt ((shape input sourceDepth sourceCount).world input epochDepth epochCount)
      ⟨(shape input sourceDepth sourceCount).mappedSupport input epochDepth epochCount
        (Financial.Installation.Runtime.frames input sourceDepth sourceCount).visit.current⟩
      ⟨(shape input sourceDepth sourceCount).enteredSupport input epochDepth epochCount
        (Financial.Installation.Runtime.frames input sourceDepth sourceCount).visit.current⟩ :=
  (shape input sourceDepth sourceCount).enterEvolution input epochDepth epochCount _
    (all_registered_rows_are_at_the_actual_current input sourceDepth sourceCount)

theorem all_actual_frame_debts_read_the_inherited_account :
    (shape input sourceDepth sourceCount).AllRead input epochDepth epochCount
      (Legacy.generated input epochDepth epochCount
        ((Financial.Installation.Runtime.frames input sourceDepth sourceCount).native.cursor
          (Financial.Installation.Runtime.frames input sourceDepth sourceCount).visit.current).account)
      ((shape input sourceDepth sourceCount).enteredSupport input epochDepth epochCount
        (Financial.Installation.Runtime.frames input sourceDepth sourceCount).visit.current) :=
  (shape input sourceDepth sourceCount).entry_reads_one_unchanged_account input epochDepth epochCount _
    (all_registered_rows_are_at_the_actual_current input sourceDepth sourceCount)

theorem entry_preserves_every_original_claim_and_budget
    (entry : OpenResponsibilityAt ((shape input sourceDepth sourceCount).world input epochDepth epochCount)
      ((shape input sourceDepth sourceCount).mappedSupport input epochDepth epochCount
        (Financial.Installation.Runtime.frames input sourceDepth sourceCount).visit.current)) :
    ((enterEvolution input epochDepth epochCount sourceDepth sourceCount).destination entry).1.claim = entry.claim ∧
      ((enterEvolution input epochDepth epochCount sourceDepth sourceCount).destination entry).1.progressBudget =
        entry.progressBudget :=
  ⟨((enterEvolution input epochDepth epochCount sourceDepth sourceCount).destination entry).2.toDebtLineage.claim_eq.symm,
    (shape input sourceDepth sourceCount).enterEvolution_preserves_budget input epochDepth epochCount _
      (all_registered_rows_are_at_the_actual_current input sourceDepth sourceCount) entry⟩

end Generated

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance.Installation

#print axioms SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance.Installation.Generated.enterEvolution
#print axioms SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance.Installation.Generated.all_actual_frame_debts_read_the_inherited_account
#print axioms SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance.Installation.Generated.entry_preserves_every_original_claim_and_budget
