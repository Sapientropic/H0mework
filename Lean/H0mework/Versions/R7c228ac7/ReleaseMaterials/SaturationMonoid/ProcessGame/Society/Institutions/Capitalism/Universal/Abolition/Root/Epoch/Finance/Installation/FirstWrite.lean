import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance.Installation.Ready

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance.Installation

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot DebtActivationWorld DebtActivationLedger
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root

noncomputable section

private def unchanged (N : WorldRelationNetwork) (support : N.Support) :
    LedgerWriteEvolutionAt N ⟨support⟩ ⟨support⟩ where
  destination := fun entry => ⟨entry, .carried rfl HEq.rfl⟩
  origin := fun entry => ⟨entry, .carried rfl HEq.rfl⟩

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument) (epochDepth epochCount : Nat)

private def registeredOwner {native : Financial.Installation.NativeFrame input} {origin : native.V.Current}
    (_registered : Financial.Installation.Registration input native origin) (current : native.V.Current) :
    OpenResponsibilityAt native.N (native.root.toAuthoritativeRoot.toRoot.supportAt current) :=
  native.entrySupport _

namespace Shape

def originalSupport {native : Financial.Installation.NativeFrame input} (_shape : Shape input native)
    (current : native.V.Current) : native.N.Support :=
  native.root.toAuthoritativeRoot.toRoot.supportAt current

def mappedSupport {native : Financial.Installation.NativeFrame input} (shape : Shape input native)
    (current : native.V.Current) : (shape.world input epochDepth epochCount).Support :=
  (shape.translation input epochDepth epochCount).support.forward (shape.originalSupport input current)

def itemTarget {native : Financial.Installation.NativeFrame input} (_shape : Shape input native)
    (current : native.V.Current) (item : ActualItem input epochDepth epochCount) :
    (process input epochDepth epochCount).GeneratedState :=
  (consume input epochDepth epochCount item
    (Legacy.generated input epochDepth epochCount (native.cursor current).account)).next input epochDepth epochCount

def itemSupport {native : Financial.Installation.NativeFrame input} (shape : Shape input native)
    (current : native.V.Current) (item : ActualItem input epochDepth epochCount) :
    (shape.world input epochDepth epochCount).Support :=
  shape.support input epochDepth epochCount current (shape.itemTarget input epochDepth epochCount current item)
    ⟨(consume input epochDepth epochCount item
      (Legacy.generated input epochDepth epochCount (native.cursor current).account)).transition input epochDepth epochCount⟩

/-- An actual item changes the financial restriction once. The original
physical source remains the separately accounted occurrence restriction. -/
def firstItemEvolution : {native : Financial.Installation.NativeFrame input} → (shape : Shape input native) →
    (current : native.V.Current) → shape.Ready input current → (item : ActualItem input epochDepth epochCount) →
    LedgerWriteEvolutionAt (shape.world input epochDepth epochCount)
      ⟨shape.mappedSupport input epochDepth epochCount current⟩ ⟨shape.itemSupport input epochDepth epochCount current item⟩
  | _, .base start _, current, _, item =>
      World.itemEvolution input epochDepth epochCount
        (Financial.Installation.Ingress.identityTranslation (ProgrammeSource.N input))
        (Financial.Installation.Cursor.baseSupport input current.cursor)
        (Financial.Installation.Cursor.baseSupport input current.cursor)
        (unchanged (ProgrammeSource.N input) (Financial.Installation.Cursor.baseSupport input current.cursor))
        (Financial.Installation.Cursor.baseOwner input current.cursor)
        start.account.generated current.cursor.account current.native item
  | _, .born prior registered, current, ready, item => by
      rcases current with ⟨current, event⟩
      cases event with
      | pending => exact ready.2.elim
      | registered native =>
          exact Financial.Installation.wholeTransport
            (firstItemEvolution prior current ready.1 item)
            ((prior.translation input epochDepth epochCount).oldOpenLedger _ |>.forward
              (registeredOwner input registered current))
            (World.LegacyLaw.Transport.enterAndItem (input := input) (depth := epochDepth) (count := epochCount)
              (before := registered.before input _) (claim := registered.claim) _ native item)

end Shape

namespace Generated

variable (sourceDepth sourceCount : Nat)

def firstItemEvolution (item : ActualItem input epochDepth epochCount) :
    LedgerWriteEvolutionAt ((shape input sourceDepth sourceCount).world input epochDepth epochCount)
      ⟨(shape input sourceDepth sourceCount).mappedSupport input epochDepth epochCount
        (Financial.Installation.Runtime.frames input sourceDepth sourceCount).visit.current⟩
      ⟨(shape input sourceDepth sourceCount).itemSupport input epochDepth epochCount
        (Financial.Installation.Runtime.frames input sourceDepth sourceCount).visit.current item⟩ :=
  (shape input sourceDepth sourceCount).firstItemEvolution input epochDepth epochCount _
    (all_registered_rows_are_at_the_actual_current input sourceDepth sourceCount) item

theorem all_actual_frame_debts_read_the_computed_account (item : ActualItem input epochDepth epochCount) :
    (shape input sourceDepth sourceCount).AllRead input epochDepth epochCount
      ((shape input sourceDepth sourceCount).itemTarget input epochDepth epochCount
        (Financial.Installation.Runtime.frames input sourceDepth sourceCount).visit.current item)
      ((shape input sourceDepth sourceCount).itemSupport input epochDepth epochCount
        (Financial.Installation.Runtime.frames input sourceDepth sourceCount).visit.current item) :=
  (shape input sourceDepth sourceCount).ready_support_reads_one_whole_account input epochDepth epochCount _
    (all_registered_rows_are_at_the_actual_current input sourceDepth sourceCount) _ _

end Generated

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance.Installation

#print axioms SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance.Installation.Generated.firstItemEvolution
#print axioms SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance.Installation.Generated.all_actual_frame_debts_read_the_computed_account
