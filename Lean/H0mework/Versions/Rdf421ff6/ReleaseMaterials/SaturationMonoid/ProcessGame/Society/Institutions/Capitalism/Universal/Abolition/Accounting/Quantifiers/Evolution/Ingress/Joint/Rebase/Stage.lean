import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Rebase.Keys
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Root.Compiler.First

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Rebase

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot DebtActivationWorld
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Source.Program Innovation Quantifiers.Joint

noncomputable section

inductive Stage
  | pending | entered | declared

def Stage.next : Stage → Stage
  | .pending => .entered
  | .entered | .declared => .declared

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  {mechanism : Trials.Mechanism Party Good Port Technology Instrument}
  {past : List (RawEvent Party Good Port Technology Instrument)} {nature : mechanism.Nature}
  {response : Control.HistoryResponse (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)}
  (seed : Global.Seed (mechanism := mechanism) (past := past) (nature := nature) (response := response))
  (grossClaim : Entitlement.Source.Claim (Quantifiers.Joint.window seed))

def declaredSupport : (NewN seed grossClaim).Support :=
  ((Background.family seed).currentSupport,
    some (.current (Current.declareGross seed grossClaim (Current.initial seed grossClaim))))

def stageSupport : Stage → (NewN seed grossClaim).Support
  | .pending => mappedSupport seed grossClaim
  | .entered => enteredSupport seed grossClaim
  | .declared => declaredSupport seed grossClaim

def declarationEvolution : LedgerWriteEvolutionAt (NewN seed grossClaim)
    ⟨enteredSupport seed grossClaim⟩ ⟨declaredSupport seed grossClaim⟩ :=
  Financial.Installation.wholeTransport
    (LedgerWriteEvolutionAt.identity ⟨(Background.family seed).currentSupport⟩)
    ((Background.family seed).entry (Background.family seed).currentSupport)
    (Productive.Transport.declareGross (Current.initial seed grossClaim))

def stageEvolution : (stage : Stage) → LedgerWriteEvolutionAt (NewN seed grossClaim)
    ⟨stageSupport seed grossClaim stage⟩ ⟨stageSupport seed grossClaim stage.next⟩
  | .pending => evolution seed grossClaim
  | .entered => declarationEvolution seed grossClaim
  | .declared => LedgerWriteEvolutionAt.identity _

theorem every_stage_keeps_the_original_keys (stage : Stage) :
    Financial.Installation.KeepsKeys (stageEvolution seed grossClaim stage) := by
  cases stage with
  | pending => exact every_original_key_is_retained_by_the_same_joint_write seed grossClaim
  | entered =>
      exact Financial.Installation.wholeTransport_keeps_keys (law := Productive.law seed grossClaim)
        (LedgerWriteEvolutionAt.identity ⟨(Background.family seed).currentSupport⟩)
        ((Background.family seed).entry (Background.family seed).currentSupport)
        (Productive.Transport.declareGross (Current.initial seed grossClaim)) ⟨fun _ => rfl,fun _ => rfl⟩
  | declared => exact ⟨fun _ => rfl,fun _ => rfl⟩

theorem fibres : ∀ support key, Subsingleton ((NewN seed grossClaim).OpenAt support key) :=
  Abolition.Root.Epoch.Finance.Future.Structure.extended_subsingleton (Productive.law seed grossClaim)
    (Background.family seed).open_fibres

theorem stage_entries_finite (stage : Stage) : Finite (OpenResponsibilityAt (NewN seed grossClaim) (stageSupport seed grossClaim stage)) := by
  cases stage with
  | pending =>
      let initial := (translation seed grossClaim).oldOpenLedger (oldSupport seed)
      exact @Finite.of_surjective _ _ seed.current.finite initial.forward
        (fun row => ⟨initial.backward row,no_row_is_created_or_deleted_in_the_initial_representation seed grossClaim _ row⟩)
  | entered => exact Abolition.Root.Epoch.Finance.Future.Finiteness.active_finite _ ((Background.family seed).entries_finite _ ⟨.nil⟩)
  | declared => exact Abolition.Root.Epoch.Finance.Future.Finiteness.active_finite _ ((Background.family seed).entries_finite _ ⟨.nil⟩)

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Rebase
