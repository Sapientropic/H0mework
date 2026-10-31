import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Rebase.Cut
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Joint.Gross.Law

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Admission

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot DebtActivationWorld DebtActivationLedger
open Source.Program Innovation Quantifiers.Joint

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  {mechanism : Trials.Mechanism Party Good Port Technology Instrument}
  {past : List (RawEvent Party Good Port Technology Instrument)} {nature : mechanism.Nature}
  {response : Control.HistoryResponse (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)}
  (seed : Global.Seed (mechanism := mechanism) (past := past) (nature := nature) (response := response))
  (grossClaim : Entitlement.Source.Claim (Quantifiers.Joint.window seed))

abbrev oldN := Rebase.NewN seed grossClaim
abbrev law := Gross.law seed grossClaim
abbrev N := ExtendedNetwork (oldN seed grossClaim) (law seed grossClaim)

def sourceRoot := Rebase.root seed grossClaim
def sourceVisit := Rebase.cut seed grossClaim
def sourceRow := Rebase.cutRow seed grossClaim
def sourceAuthority := Rebase.cutAuthority seed grossClaim

def initialShared := Current.initial seed grossClaim
def declaredShared := Current.declareGross seed grossClaim (initialShared seed grossClaim)

def firstStep : DebtAdmissionFirstWrite.SourceFixedDebtAdmissionEventAt (law seed grossClaim)
    (initialShared seed grossClaim) where
  target := declaredShared seed grossClaim
  step := Gross.declaration seed grossClaim

def sourceSuccessor : SourceNativeLedgerGeneratedSuccessorAt
    ((sourceRoot seed grossClaim).emitted (sourceVisit seed grossClaim).current)
    ((sourceRoot seed grossClaim).toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt (sourceVisit seed grossClaim).current) :=
  Abolition.Accounting.Root.Compiler.successor (Rebase.flow seed grossClaim) Rebase.Stage.entered

def support : Bool → (N seed grossClaim).Support
  | false => ((sourceRoot seed grossClaim).toAuthoritativeRoot.toRoot.supportAt (sourceVisit seed grossClaim).current,
      some (initialShared seed grossClaim))
  | true => ((sourceSuccessor seed grossClaim).targetOccurrence.1,some (declaredShared seed grossClaim))

def firstWrite : LedgerWriteEvolutionAt (N seed grossClaim)
    ⟨support seed grossClaim false⟩ ⟨support seed grossClaim true⟩ :=
  jointStepLedgerEvolution (sourceSuccessor seed grossClaim).ledgerEvolution (sourceRow seed grossClaim)
    (Gross.declaration seed grossClaim)

theorem the_old_side_of_the_declaration_already_uses_the_same_shared_pointer :
    (sourceSuccessor seed grossClaim).targetOccurrence.1 = Rebase.declaredSupport seed grossClaim :=
  Abolition.Accounting.Root.Compiler.successor_support (Rebase.flow seed grossClaim) Rebase.Stage.entered

theorem declaration_cannot_hide_or_pay_either_original_material_quantity :
    (declaredShared seed grossClaim).raw = currentRaw seed ∧
      (declaredShared seed grossClaim).productive = (productiveState seed).remaining ∧
      (declaredShared seed grossClaim).gross = (Entitlement.Duty.State.initial grossClaim).remaining :=
  Gross.declaration_is_not_payment seed grossClaim

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Admission
