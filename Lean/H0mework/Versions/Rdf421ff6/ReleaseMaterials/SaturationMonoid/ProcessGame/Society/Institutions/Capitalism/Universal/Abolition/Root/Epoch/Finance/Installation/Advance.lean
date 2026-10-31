import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance.Installation.FirstWrite

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

private theorem prefixTail {first last : (Financial.process input).GeneratedState}
    (priorRun : Nonempty ((Financial.process input).Run first.current last.current))
    (account : (process input epochDepth epochCount).GeneratedState)
    (tail : Nonempty ((process input epochDepth epochCount).Run
      (Legacy.generated input epochDepth epochCount last).current account.current)) :
    Nonempty ((process input epochDepth epochCount).Run
      (Legacy.generated input epochDepth epochCount first).current account.current) := by
  obtain ⟨priorRun⟩ := priorRun
  exact tail.map fun later => (World.LegacyLaw.runImage input epochDepth epochCount priorRun).concatRuns
    (process input epochDepth epochCount) later

namespace Shape

def currentOwner : {native : Financial.Installation.NativeFrame input} → (shape : Shape input native) →
    (current : native.V.Current) → (account : (process input epochDepth epochCount).GeneratedState) →
    (tail : Nonempty ((process input epochDepth epochCount).Run
      (Legacy.generated input epochDepth epochCount (native.cursor current).account).current account.current)) →
    OpenResponsibilityAt (shape.world input epochDepth epochCount)
      (shape.support input epochDepth epochCount current account tail)
  | _, .base start _, current, account, tail => World.currentOwner input epochDepth epochCount (ProgrammeSource.N input)
      (Financial.Installation.Cursor.baseSupport input current.cursor)
      (Financial.Installation.Cursor.baseOwner input current.cursor) start.account.generated account
      (prefixTail input epochDepth epochCount current.native account tail)
  | _, .born prior _, current, account, tail => by
      rcases current with ⟨current, event⟩
      cases event <;> exact oldEntry (currentOwner prior _ account tail)

private theorem nextTail {native : Financial.Installation.NativeFrame input} (current : native.V.Current)
    (account : (process input epochDepth epochCount).GeneratedState)
    (tail : Nonempty ((process input epochDepth epochCount).Run
      (Legacy.generated input epochDepth epochCount (native.cursor current).account).current account.current))
    (item : ActualItem input epochDepth epochCount) :
    Nonempty ((process input epochDepth epochCount).Run
      (Legacy.generated input epochDepth epochCount (native.cursor current).account).current
      ((consume input epochDepth epochCount item account).next input epochDepth epochCount).current) :=
  tail.map fun prior => prior.concatRuns (process input epochDepth epochCount)
    ((consume input epochDepth epochCount item account).transition input epochDepth epochCount)

def continueItemEvolution : {native : Financial.Installation.NativeFrame input} → (shape : Shape input native) →
    (current : native.V.Current) → shape.Ready input current →
    (account : (process input epochDepth epochCount).GeneratedState) →
    (tail : Nonempty ((process input epochDepth epochCount).Run
      (Legacy.generated input epochDepth epochCount (native.cursor current).account).current account.current)) →
    (item : ActualItem input epochDepth epochCount) →
    LedgerWriteEvolutionAt (shape.world input epochDepth epochCount)
      ⟨shape.support input epochDepth epochCount current account tail⟩
      ⟨shape.support input epochDepth epochCount current
        ((consume input epochDepth epochCount item account).next input epochDepth epochCount)
        (nextTail input epochDepth epochCount current account tail item)⟩
  | _, .base start _, current, _, account, tail, item =>
      World.continueItemEvolution input epochDepth epochCount (ProgrammeSource.N input)
        (stationary (ProgrammeSource.N input) (Financial.Installation.Cursor.baseSupport input current.cursor))
        (Financial.Installation.Cursor.baseOwner input current.cursor) start.account.generated account
        (prefixTail input epochDepth epochCount current.native account tail) item
  | _, .born prior registered, current, ready, account, tail, item => by
      rcases current with ⟨current, event⟩
      cases event with
      | pending => exact ready.2.elim
      | registered native =>
          exact Financial.Installation.wholeTransport
            (continueItemEvolution prior current ready.1 account tail item)
            (currentOwner input epochDepth epochCount prior current account tail)
            (World.LegacyLaw.Transport.actualItem (input := input) (depth := epochDepth) (count := epochCount)
              (before := registered.before input _) (claim := registered.claim) account
              (prefixTail input epochDepth epochCount native account tail) item)

end Shape

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance.Installation

#print axioms SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance.Installation.Shape.continueItemEvolution
