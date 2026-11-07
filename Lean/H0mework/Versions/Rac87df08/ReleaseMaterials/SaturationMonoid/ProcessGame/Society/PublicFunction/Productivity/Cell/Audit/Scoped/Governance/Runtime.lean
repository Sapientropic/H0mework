import H0mework.Versions.Rac87df08.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.Governance

set_option autoImplicit false
set_option maxRecDepth 65536

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.Governance.Runtime
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot

def beforeAt (queries : Nat → Query) (larger : Bool) (births : Births) (replies : Replies) (ordinal : Nat) :=
  ProgrammeSource.rawCurrent (input queries larger births replies)
    (ProgrammeHistory.visitAt (input queries larger births replies) ordinal).current

def wordAt (queries : Nat → Query) (larger : Bool) (births : Births) (replies : Replies) (ordinal : Nat) :=
  ProgrammeSource.rawEvent (input queries larger births replies)
    (ProgrammeHistory.visitAt (input queries larger births replies) ordinal).current

theorem whole_claim_matrix_is_preserved (queries : Nat → Query) (larger : Bool)
    (births : Births) (replies : Replies) (ordinal : Nat) :
    (beforeAt queries larger births replies ordinal).claims = initial.claims := by
  unfold beforeAt
  rw [current_is_own_root_current]
  induction ordinal with
  | zero => unfold current; rfl
  | succ ordinal ih =>
    rw [current_succ]
    split
    · exact ih
    · exact (emission_preserves_all_original_claims _ _ _ _ _).trans ih

structure Result (queries : Nat → Query) (larger : Bool) (births : Births) (replies : Replies) (ordinal : Nat) where
  commands : List (Mandate.ActualCommand baseLaw scope (beforeAt queries larger births replies ordinal) (wordAt queries larger births replies ordinal))
  actualCommands : commands = Mandate.commandsAt baseLaw scope (beforeAt queries larger births replies ordinal) (wordAt queries larger births replies ordinal)
  rejected : List (Response.Failure (beforeAt queries larger births replies ordinal) (wordAt queries larger births replies ordinal))
  actualFailures : rejected = Response.failures (beforeAt queries larger births replies ordinal) (wordAt queries larger births replies ordinal)
  roles : (key : String) → List (Role (beforeAt queries larger births replies ordinal) (wordAt queries larger births replies ordinal) key)
  actualRoles : ∀ key, roles key = Governance.roles (beforeAt queries larger births replies ordinal) (wordAt queries larger births replies ordinal) key

  prior : Scoped.Runtime.Result queries larger ordinal
  priorGenerated : prior = Scoped.Runtime.result queries larger ordinal
  financeMatrix : Financial.BalanceConservation.ledgerClaims Cell.source.input prior.oldFinance.current =
    (beforeAt queries larger births replies ordinal).claims

def result (queries : Nat → Query) (larger : Bool) (births : Births) (replies : Replies) (ordinal : Nat) : Result queries larger births replies ordinal where
  commands := Mandate.commandsAt baseLaw scope (beforeAt queries larger births replies ordinal) (wordAt queries larger births replies ordinal)
  actualCommands := rfl
  rejected := Response.failures (beforeAt queries larger births replies ordinal) (wordAt queries larger births replies ordinal)
  actualFailures := rfl
  roles := fun key => Governance.roles (beforeAt queries larger births replies ordinal) (wordAt queries larger births replies ordinal) key
  actualRoles := fun _ => rfl
  prior := Scoped.Runtime.result queries larger ordinal
  priorGenerated := rfl
  financeMatrix := by
    rw [whole_claim_matrix_is_preserved]
    exact (Scoped.Runtime.result queries larger ordinal).finance_matrix.trans
      (every_current_keeps_the_original_claim_matrix _ _ _)

def projectionLaw (queries : Nat → Query) (larger : Bool) (births : Births) (replies : Replies) : SourceNativeProjectionLaw
    (ProgrammeLiving.authoritySource (input queries larger births replies)).restructuringSource.toLedgerSource where
  Projection := Unit
  ActiveAt := fun _ {_} _ => Unit
  InactiveAt := fun _ {_} _ => Empty
  classify := fun _ {_} _ => .inl ()
  PayloadAt := fun _ {current} _ _ =>
    (ordinal : Nat) → current = (ProgrammeHistory.visitAt (input queries larger births replies) ordinal).current →
      Result queries larger births replies ordinal
  project := fun _ {_} _ _ ordinal _canonical => result queries larger births replies ordinal

def root (queries : Nat → Query) (larger : Bool) (births : Births) (replies : Replies) :=
  (ProgrammeLiving.livingRoot (input queries larger births replies)).withProjectionCoface (projectionLaw queries larger births replies)

theorem emitting_root_is_preserved (queries : Nat → Query) (larger : Bool) (births : Births) (replies : Replies) :
    (root queries larger births replies).toAuthoritativeRoot.toRoot =
      (ProgrammeLiving.livingRoot (input queries larger births replies)).toAuthoritativeRoot.toRoot := rfl

def stateAt (queries : Nat → Query) (larger : Bool) (births : Births) (replies : Replies) (ordinal : Nat) :
    SourceNativeLivingRootCurrentAt (ProgrammeSource.N (input queries larger births replies)) :=
  ⟨ProgrammeSource.V (input queries larger births replies),root queries larger births replies,ProgrammeHistory.temporalVisit (input queries larger births replies) ordinal⟩

def process (queries : Nat → Query) (larger : Bool) (births : Births) (replies : Replies) : SourceNativeLivingRootProcess (ProgrammeSource.N (input queries larger births replies)) where
  State := Nat
  stateAt := stateAt queries larger births replies
  stateAt_injective := by
    intro first second same
    have labels := congrArg (fun state : SourceNativeLivingRootCurrentAt (ProgrammeSource.N (input queries larger births replies)) =>
      (⟨state.V.Current,state.visit.current⟩ : Sigma fun Carrier : Type => Carrier)) same
    exact ProgrammeHistory.visit_current_injective (input queries larger births replies) (eq_of_heq (Sigma.mk.inj labels).2)
  initial := 0
  successorAt := fun ordinal => ⟨ordinal + 1,rfl,HEq.rfl⟩

inductive Face where
  | execution | governance

def facade (queries : Nat → Query) (larger : Bool) (births : Births) (replies : Replies) : SourceNativeLivingRuntimeFacade (ProgrammeSource.N (input queries larger births replies)) where
  process := process queries larger births replies
  FaceAt := fun _ => Face
  componentAt := fun _ face => match face with
    | .execution => ProgrammeLiving.projectionLaw (input queries larger births replies)
    | .governance => projectionLaw queries larger births replies
  installationAt := by
    intro state face
    cases face
    · exact SourceNativeProjectionLaw.InstallationAt.inheritedCoface
        (ProgrammeLiving.authoritySource (input queries larger births replies)) (projectionLaw queries larger births replies)
    · exact SourceNativeProjectionLaw.InstallationAt.componentCoface
        (ProgrammeLiving.authoritySource (input queries larger births replies)) (projectionLaw queries larger births replies)
  projectionAt := fun _ face => match face with
    | .execution => .execution
    | .governance => ()

def activated (queries : Nat → Query) (larger : Bool) (births : Births) (replies : Replies) (ordinal : Nat) :=
  (facade queries larger births replies).seed.advance ordinal

theorem activated_state (queries : Nat → Query) (larger : Bool) (births : Births) (replies : Replies) (ordinal : Nat) :
    (activated queries larger births replies ordinal).state = ordinal := by
  induction ordinal with
  | zero => rfl
  | succ ordinal ih => exact congrArg Nat.succ ih

theorem governance_shares_actual_writeback_and_generated_next (queries : Nat → Query) (larger : Bool) (births : Births) (replies : Replies) (ordinal : Nat) :
    (activated queries larger births replies ordinal).tick.generated.occurrence =
      (activated queries larger births replies ordinal).current.root.toAuthoritativeRoot.toLedgerRoot.emitted
        (activated queries larger births replies ordinal).current.visit.current ∧
    HEq (activated queries larger births replies ordinal).tick.generated.wholeLedgerWriteBack
      ((activated queries larger births replies ordinal).current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt
        (activated queries larger births replies ordinal).current.visit.current) ∧
    HEq ((facade queries larger births replies).readoutAt (activated queries larger births replies ordinal) .governance)
      ((activated queries larger births replies ordinal).tick.generated.projectionOutcome
        (((facade queries larger births replies).installationAt (activated queries larger births replies ordinal) .governance).embed
          ((facade queries larger births replies).projectionAt (activated queries larger births replies ordinal) .governance))) ∧
    (activated queries larger births replies ordinal).tick.nextCurrent =
      (process queries larger births replies).stateAt ((process queries larger births replies).successor (activated queries larger births replies ordinal).state) :=
  ((facade queries larger births replies).readoutAt_factorizes (activated queries larger births replies ordinal) .governance).2

theorem payload_is_actual (queries : Nat → Query) (larger : Bool) (births : Births) (replies : Replies) (ordinal : Nat) :
    (projectionLaw queries larger births replies).project () (ProgrammeSource.emitted (input queries larger births replies)
      (ProgrammeHistory.visitAt (input queries larger births replies) ordinal).current) () ordinal rfl = result queries larger births replies ordinal := rfl

end SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.Governance.Runtime
