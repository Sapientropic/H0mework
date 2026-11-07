import H0mework.Versions.Rac87df08.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.Response

set_option autoImplicit false
set_option maxRecDepth 65536

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.Response.Runtime
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot

def beforeAt (queries : Nat → Query) (larger : Bool) (cut : Nat) (objection : Objection) (ordinal : Nat) :=
  ProgrammeSource.rawCurrent (input queries larger cut objection)
    (ProgrammeHistory.visitAt (input queries larger cut objection) ordinal).current

def wordAt (queries : Nat → Query) (larger : Bool) (cut : Nat) (objection : Objection) (ordinal : Nat) :=
  ProgrammeSource.rawEvent (input queries larger cut objection)
    (ProgrammeHistory.visitAt (input queries larger cut objection) ordinal).current

private theorem emission_preserves_claims (queries : Nat → Query) (larger : Bool) (cut : Nat)
    (objection : Objection) (before : AuditCurrent) :
    (auditLaw.next before (emitted queries larger cut objection before)).claims = before.claims := by
  unfold emitted
  split
  · split
    · rfl
    · exact response_preserves_all_original_claims _ _ _
  · exact every_emitted_word_preserves_original_claims _ _ _

theorem whole_claim_matrix_is_preserved (queries : Nat → Query) (larger : Bool) (cut : Nat)
    (objection : Objection) (ordinal : Nat) :
    (beforeAt queries larger cut objection ordinal).claims = initial.claims := by
  unfold beforeAt
  rw [current_is_own_root_current]
  induction ordinal with
  | zero => unfold current; rfl
  | succ ordinal ih =>
    rw [current_succ]
    split
    · exact ih
    · exact (emission_preserves_claims _ _ _ _ _).trans ih

structure Result (queries : Nat → Query) (larger : Bool) (cut : Nat) (objection : Objection) (ordinal : Nat) where
  packets : List Packet
  generated : packets = release (beforeAt queries larger cut objection ordinal) (wordAt queries larger cut objection ordinal)
  rejected : List (Failure (beforeAt queries larger cut objection ordinal) (wordAt queries larger cut objection ordinal))
  actualFailures : rejected = failures (beforeAt queries larger cut objection ordinal) (wordAt queries larger cut objection ordinal)
  commands : List (Mandate.ActualCommand baseLaw scope (beforeAt queries larger cut objection ordinal) (wordAt queries larger cut objection ordinal))
  actualCommands : commands = Mandate.commandsAt baseLaw scope (beforeAt queries larger cut objection ordinal) (wordAt queries larger cut objection ordinal)
  prior : Scoped.Runtime.Result queries larger cut
  priorGenerated : prior = Scoped.Runtime.result queries larger cut
  financeMatrix : Financial.BalanceConservation.ledgerClaims Cell.source.input prior.oldFinance.current =
    (beforeAt queries larger cut objection ordinal).claims

def result (queries : Nat → Query) (larger : Bool) (cut : Nat) (objection : Objection) (ordinal : Nat) :
    Result queries larger cut objection ordinal where
  packets := release (beforeAt queries larger cut objection ordinal) (wordAt queries larger cut objection ordinal)
  generated := rfl
  rejected := failures (beforeAt queries larger cut objection ordinal) (wordAt queries larger cut objection ordinal)
  actualFailures := rfl
  commands := Mandate.commandsAt baseLaw scope (beforeAt queries larger cut objection ordinal) (wordAt queries larger cut objection ordinal)
  actualCommands := rfl
  prior := Scoped.Runtime.result queries larger cut
  priorGenerated := rfl
  financeMatrix := by
    rw [whole_claim_matrix_is_preserved]
    exact (Scoped.Runtime.result queries larger cut).finance_matrix.trans
      (every_current_keeps_the_original_claim_matrix _ _ _)

def projectionLaw (queries : Nat → Query) (larger : Bool) (cut : Nat) (objection : Objection) : SourceNativeProjectionLaw
    (ProgrammeLiving.authoritySource (input queries larger cut objection)).restructuringSource.toLedgerSource where
  Projection := Unit
  ActiveAt := fun _ {_} _ => Unit
  InactiveAt := fun _ {_} _ => Empty
  classify := fun _ {_} _ => .inl ()
  PayloadAt := fun _ {current} _ _ =>
    (ordinal : Nat) → current = (ProgrammeHistory.visitAt (input queries larger cut objection) ordinal).current →
      Result queries larger cut objection ordinal
  project := fun _ {_} _ _ ordinal _canonical => result queries larger cut objection ordinal

def root (queries : Nat → Query) (larger : Bool) (cut : Nat) (objection : Objection) :=
  (ProgrammeLiving.livingRoot (input queries larger cut objection)).withProjectionCoface (projectionLaw queries larger cut objection)

theorem emitting_root_is_preserved (queries : Nat → Query) (larger : Bool) (cut : Nat) (objection : Objection) :
    (root queries larger cut objection).toAuthoritativeRoot.toRoot =
      (ProgrammeLiving.livingRoot (input queries larger cut objection)).toAuthoritativeRoot.toRoot := rfl

def stateAt (queries : Nat → Query) (larger : Bool) (cut : Nat) (objection : Objection) (ordinal : Nat) :
    SourceNativeLivingRootCurrentAt (ProgrammeSource.N (input queries larger cut objection)) :=
  ⟨ProgrammeSource.V (input queries larger cut objection),root queries larger cut objection,ProgrammeHistory.temporalVisit (input queries larger cut objection) ordinal⟩

def process (queries : Nat → Query) (larger : Bool) (cut : Nat) (objection : Objection) : SourceNativeLivingRootProcess (ProgrammeSource.N (input queries larger cut objection)) where
  State := Nat
  stateAt := stateAt queries larger cut objection
  stateAt_injective := by
    intro first second same
    have labels := congrArg (fun state : SourceNativeLivingRootCurrentAt (ProgrammeSource.N (input queries larger cut objection)) =>
      (⟨state.V.Current,state.visit.current⟩ : Sigma fun Carrier : Type => Carrier)) same
    exact ProgrammeHistory.visit_current_injective (input queries larger cut objection) (eq_of_heq (Sigma.mk.inj labels).2)
  initial := 0
  successorAt := fun ordinal => ⟨ordinal + 1,rfl,HEq.rfl⟩

inductive Face where
  | execution | response

def facade (queries : Nat → Query) (larger : Bool) (cut : Nat) (objection : Objection) : SourceNativeLivingRuntimeFacade (ProgrammeSource.N (input queries larger cut objection)) where
  process := process queries larger cut objection
  FaceAt := fun _ => Face
  componentAt := fun _ face => match face with
    | .execution => ProgrammeLiving.projectionLaw (input queries larger cut objection)
    | .response => projectionLaw queries larger cut objection
  installationAt := by
    intro state face
    cases face
    · exact SourceNativeProjectionLaw.InstallationAt.inheritedCoface
        (ProgrammeLiving.authoritySource (input queries larger cut objection)) (projectionLaw queries larger cut objection)
    · exact SourceNativeProjectionLaw.InstallationAt.componentCoface
        (ProgrammeLiving.authoritySource (input queries larger cut objection)) (projectionLaw queries larger cut objection)
  projectionAt := fun _ face => match face with
    | .execution => .execution
    | .response => ()

def activated (queries : Nat → Query) (larger : Bool) (cut : Nat) (objection : Objection) (ordinal : Nat) :=
  (facade queries larger cut objection).seed.advance ordinal

theorem activated_state (queries : Nat → Query) (larger : Bool) (cut : Nat) (objection : Objection) (ordinal : Nat) :
    (activated queries larger cut objection ordinal).state = ordinal := by
  induction ordinal with
  | zero => rfl
  | succ ordinal ih => exact congrArg Nat.succ ih

theorem response_shares_actual_writeback_and_generated_next (queries : Nat → Query) (larger : Bool) (cut : Nat) (objection : Objection) (ordinal : Nat) :
    (activated queries larger cut objection ordinal).tick.generated.occurrence =
      (activated queries larger cut objection ordinal).current.root.toAuthoritativeRoot.toLedgerRoot.emitted
        (activated queries larger cut objection ordinal).current.visit.current ∧
    HEq (activated queries larger cut objection ordinal).tick.generated.wholeLedgerWriteBack
      ((activated queries larger cut objection ordinal).current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt
        (activated queries larger cut objection ordinal).current.visit.current) ∧
    HEq ((facade queries larger cut objection).readoutAt (activated queries larger cut objection ordinal) .response)
      ((activated queries larger cut objection ordinal).tick.generated.projectionOutcome
        (((facade queries larger cut objection).installationAt (activated queries larger cut objection ordinal) .response).embed
          ((facade queries larger cut objection).projectionAt (activated queries larger cut objection ordinal) .response))) ∧
    (activated queries larger cut objection ordinal).tick.nextCurrent =
      (process queries larger cut objection).stateAt ((process queries larger cut objection).successor (activated queries larger cut objection ordinal).state) :=
  ((facade queries larger cut objection).readoutAt_factorizes (activated queries larger cut objection ordinal) .response).2

theorem payload_is_actual (queries : Nat → Query) (larger : Bool) (cut : Nat) (objection : Objection) (ordinal : Nat) :
    (projectionLaw queries larger cut objection).project () (ProgrammeSource.emitted (input queries larger cut objection)
      (ProgrammeHistory.visitAt (input queries larger cut objection) ordinal).current) () ordinal rfl = result queries larger cut objection ordinal := rfl

end SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.Response.Runtime
