import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Admission.Root

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Admission

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion DebtActivationWorld DebtActivationLedger
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

local notation "oldRoot" => Origin.root seed grossClaim
local notation "newRoot" => root seed grossClaim
local notation "initial" => Abolition.Accounting.Root.Compiler.initialVisit (flow seed grossClaim)
local notation "first" => Abolition.Accounting.Root.Compiler.successor (flow seed grossClaim) false

def targetAt (event : ExactTemporalCausalRootEventAt (oldRoot).toAuthoritativeRoot.toLedgerRoot (sourceVisit seed grossClaim)) :
    SourceNativeDebtAdmissionActualActionTargetAt oldRoot (sourceVisit seed grossClaim) event
      (sourceRow seed grossClaim) (Origin.authority seed grossClaim) := by
  rw [event.eq_generated]
  exact {
    law := law seed grossClaim
    sourceState := initialShared seed grossClaim
    stepEvent := firstStep seed grossClaim
    sourceSuccessor := sourceSuccessor seed grossClaim
    TargetV := V seed grossClaim
    targetRoot := newRoot
    initialSupport_eq := rfl
    initialOldRow := fun row => Abolition.Accounting.Root.Compiler.generatedRow (flow seed grossClaim) initial
      (oldEntry (law := law seed grossClaim) (state? := some (initialShared seed grossClaim)) row)
    initialBornRow := Abolition.Accounting.Root.Compiler.generatedRow (flow seed grossClaim) initial
      (debtEntry (N := oldN seed grossClaim) (law := law seed grossClaim)
        ((oldRoot).toAuthoritativeRoot.toRoot.supportAt (sourceVisit seed grossClaim).current)
        (initialShared seed grossClaim))
    firstSuccessor := first
    firstSupport_eq := Abolition.Accounting.Root.Compiler.successor_support (flow seed grossClaim) false
    firstDestination_heq := Abolition.Accounting.Root.Compiler.successor_destination (flow seed grossClaim) false
    oldProjection := oldProjection seed grossClaim
    oldProjection_injective := oldProjection_injective seed grossClaim
    oldOutcome_heq := every_original_query_outcome_is_retained seed grossClaim
    canonical_targetNextVisit_eq := Abolition.Root.Registered.Macro.Ingress.next_is_the_same_generated_successor
      (newRoot) initial first
    Answer := Current seed grossClaim
    answer := declaredShared seed grossClaim
    Receipt := fun answer => ULift.{3,0} (PLift
      (answer = declaredShared seed grossClaim ∧ answer.raw = currentRaw seed ∧
        answer.productive = (productiveState seed).remaining ∧
        answer.gross = (Entitlement.Duty.State.initial grossClaim).remaining ∧
        answer.grossDeclared = true))
    receipt := ⟨⟨rfl,rfl,rfl,rfl,rfl⟩⟩ }

def program : SourceNativeDebtAdmissionActualActionProgramAt oldRoot (sourceVisit seed grossClaim)
    (sourceRow seed grossClaim) (Origin.authority seed grossClaim) where
  targetAt := targetAt seed grossClaim

def generated := (program seed grossClaim).generate
  ((oldRoot).toAuthoritativeRoot.toLedgerRoot.exactTemporalCausalEventAt (sourceVisit seed grossClaim))

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Admission
