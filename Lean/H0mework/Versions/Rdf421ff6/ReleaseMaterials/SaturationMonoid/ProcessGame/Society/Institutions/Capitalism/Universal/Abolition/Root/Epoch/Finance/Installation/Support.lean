import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance.Installation.Shape

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance.Installation

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot DebtActivationWorld
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument) (epochDepth epochCount : Nat)

private theorem prependOriginal {first last : (Financial.process input).GeneratedState}
    (prior : Nonempty ((Financial.process input).Run first.current last.current))
    (account : (process input epochDepth epochCount).GeneratedState)
    (tail : Nonempty ((process input epochDepth epochCount).Run
      (Legacy.generated input epochDepth epochCount last).current account.current)) :
    Nonempty ((process input epochDepth epochCount).Run
      (Legacy.generated input epochDepth epochCount first).current account.current) := by
  obtain ⟨run⟩ := prior
  exact tail.map fun later => (World.LegacyLaw.runImage input epochDepth epochCount run).concatRuns
    (process input epochDepth epochCount) later

namespace Shape

/-- Only source reachability decides whether a born row has crossed its
registration step. Pending rows remain literal pending rows. -/
def Ready : {native : Financial.Installation.NativeFrame input} → (shape : Shape input native) → native.V.Current → Prop
  | _, .base _ _, _ => True
  | _, .born prior _, current => Ready prior current.1 ∧
      match current.2 with
      | .pending => False
      | .registered _ => True

def support : {native : Financial.Installation.NativeFrame input} → (shape : Shape input native) →
    (current : native.V.Current) → (account : (process input epochDepth epochCount).GeneratedState) →
    Nonempty ((process input epochDepth epochCount).Run
      (Legacy.generated input epochDepth epochCount (native.cursor current).account).current account.current) →
    (shape.world input epochDepth epochCount).Support
  | _, .base start _, current, account, tail =>
      World.currentSupport input epochDepth epochCount (ProgrammeSource.N input)
        (Financial.Installation.Cursor.baseSupport input current.cursor) start.account.generated account
        (prependOriginal input epochDepth epochCount current.native account tail)
  | _, .born prior registered, current, account, tail => by
      rcases current with ⟨current, event⟩
      cases event with
      | pending => exact (support prior _ account tail, some (.legacy .pending))
      | registered native => exact (support prior _ account tail,
          some (.current account (prependOriginal input epochDepth epochCount native account tail)))

def AllRead (account : (process input epochDepth epochCount).GeneratedState) :
    {native : Financial.Installation.NativeFrame input} → (shape : Shape input native) →
    (shape.world input epochDepth epochCount).Support → Prop
  | _, .base start _, value => World.AllReadAccount input epochDepth epochCount (ProgrammeSource.N input)
      account start.account.generated value
  | _, .born prior _, value => AllRead account prior value.1 ∧
      match value.2 with
      | some (.current actual _) => actual = account
      | _ => False

theorem ready_support_reads_one_whole_account {native : Financial.Installation.NativeFrame input}
    (shape : Shape input native) (current : native.V.Current) (ready : shape.Ready input current)
    (account : (process input epochDepth epochCount).GeneratedState)
    (tail : Nonempty ((process input epochDepth epochCount).Run
      (Legacy.generated input epochDepth epochCount (native.cursor current).account).current account.current)) :
    shape.AllRead input epochDepth epochCount account (shape.support input epochDepth epochCount current account tail) := by
  induction shape with
  | base start positive => exact World.every_old_debt_reads_the_same_account input epochDepth epochCount _ _ _ _ _
  | born prior registered inherited =>
      rcases current with ⟨current, event⟩
      cases event with
      | pending => exact ready.2.elim
      | registered native => exact ⟨inherited current ready.1 tail, rfl⟩

end Shape

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance.Installation

#print axioms SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance.Installation.Shape.ready_support_reads_one_whole_account
