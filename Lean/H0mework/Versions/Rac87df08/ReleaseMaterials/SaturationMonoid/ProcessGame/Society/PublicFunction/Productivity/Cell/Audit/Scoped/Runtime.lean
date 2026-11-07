import H0mework.Versions.Rac87df08.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.Actual
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Finance

set_option autoImplicit false
set_option maxRecDepth 65536

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.Runtime
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot

structure Result (queries : Nat → Query) (larger : Bool) (ordinal : Nat) where
  records : List Record
  generated : records = recordsAt queries larger ordinal
  oldFinance : (Financial.process Cell.source.input).GeneratedState
  finance_inherited : oldFinance = Finance.account 2
  finance_run : (Financial.process Cell.source.input).Run oldFinance.current oldFinance.current
  finance_matrix : Financial.BalanceConservation.ledgerClaims Cell.source.input oldFinance.current =
    (current queries larger ordinal).claims
  originalServices : (slot : Slot) → source.ActualSlotPaid 1 (originalIndex slot)

def result (queries : Nat → Query) (larger : Bool) (ordinal : Nat) : Result queries larger ordinal where
  records := recordsAt queries larger ordinal
  generated := rfl
  oldFinance := Finance.account 2
  finance_inherited := rfl
  finance_run := .nil
  finance_matrix := by
    rw [every_current_keeps_the_original_claim_matrix]
    exact (Finance.all_native_positions_are_the_actual_claims 2).trans
      (congrArg RawCurrent.claims (raw_current_frame 2))
  originalServices := fun slot => trace_verifies_original slot (originalEvidence slot)
    (original_evidence_has_origin slot) (every_original_slot_passes slot).1

def projectionLaw (queries : Nat → Query) (larger : Bool) : SourceNativeProjectionLaw
    (ProgrammeLiving.authoritySource (input queries larger)).restructuringSource.toLedgerSource where
  Projection := Unit
  ActiveAt := fun _ {_} _ => Unit
  InactiveAt := fun _ {_} _ => Empty
  classify := fun _ {_} _ => .inl ()
  PayloadAt := fun _ {current} _ _ =>
    (ordinal : Nat) → current = (ProgrammeHistory.visitAt (input queries larger) ordinal).current →
      Result queries larger ordinal
  project := fun _ {_} _ _ ordinal _canonical => result queries larger ordinal

def root (queries : Nat → Query) (larger : Bool) :=
  (ProgrammeLiving.livingRoot (input queries larger)).withProjectionCoface (projectionLaw queries larger)

theorem emitting_root_is_preserved (queries : Nat → Query) (larger : Bool) :
    (root queries larger).toAuthoritativeRoot.toRoot =
      (ProgrammeLiving.livingRoot (input queries larger)).toAuthoritativeRoot.toRoot := rfl

def stateAt (queries : Nat → Query) (larger : Bool) (ordinal : Nat) :
    SourceNativeLivingRootCurrentAt (ProgrammeSource.N (input queries larger)) :=
  ⟨ProgrammeSource.V (input queries larger),root queries larger,ProgrammeHistory.temporalVisit (input queries larger) ordinal⟩

def process (queries : Nat → Query) (larger : Bool) : SourceNativeLivingRootProcess (ProgrammeSource.N (input queries larger)) where
  State := Nat
  stateAt := stateAt queries larger
  stateAt_injective := by
    intro first second same
    have labels := congrArg (fun state : SourceNativeLivingRootCurrentAt (ProgrammeSource.N (input queries larger)) =>
      (⟨state.V.Current,state.visit.current⟩ : Sigma fun Carrier : Type => Carrier)) same
    exact ProgrammeHistory.visit_current_injective (input queries larger) (eq_of_heq (Sigma.mk.inj labels).2)
  initial := 0
  successorAt := fun ordinal => ⟨ordinal + 1,rfl,HEq.rfl⟩

inductive Face where
  | execution | audit

def facade (queries : Nat → Query) (larger : Bool) : SourceNativeLivingRuntimeFacade (ProgrammeSource.N (input queries larger)) where
  process := process queries larger
  FaceAt := fun _ => Face
  componentAt := fun _ face => match face with
    | .execution => ProgrammeLiving.projectionLaw (input queries larger)
    | .audit => projectionLaw queries larger
  installationAt := by
    intro state face
    cases face
    · exact SourceNativeProjectionLaw.InstallationAt.inheritedCoface
        (ProgrammeLiving.authoritySource (input queries larger)) (projectionLaw queries larger)
    · exact SourceNativeProjectionLaw.InstallationAt.componentCoface
        (ProgrammeLiving.authoritySource (input queries larger)) (projectionLaw queries larger)
  projectionAt := fun _ face => match face with
    | .execution => .execution
    | .audit => ()

def activated (queries : Nat → Query) (larger : Bool) (ordinal : Nat) :=
  (facade queries larger).seed.advance ordinal

theorem activated_state (queries : Nat → Query) (larger : Bool) (ordinal : Nat) :
    (activated queries larger ordinal).state = ordinal := by
  induction ordinal with
  | zero => rfl
  | succ ordinal ih => exact congrArg Nat.succ ih

theorem audit_shares_actual_writeback_and_generated_next (queries : Nat → Query) (larger : Bool) (ordinal : Nat) :
    (activated queries larger ordinal).tick.generated.occurrence =
      (activated queries larger ordinal).current.root.toAuthoritativeRoot.toLedgerRoot.emitted
        (activated queries larger ordinal).current.visit.current ∧
    HEq (activated queries larger ordinal).tick.generated.wholeLedgerWriteBack
      ((activated queries larger ordinal).current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt
        (activated queries larger ordinal).current.visit.current) ∧
    HEq ((facade queries larger).readoutAt (activated queries larger ordinal) .audit)
      ((activated queries larger ordinal).tick.generated.projectionOutcome
        (((facade queries larger).installationAt (activated queries larger ordinal) .audit).embed
          ((facade queries larger).projectionAt (activated queries larger ordinal) .audit))) ∧
    (activated queries larger ordinal).tick.nextCurrent =
      (process queries larger).stateAt ((process queries larger).successor (activated queries larger ordinal).state) :=
  ((facade queries larger).readoutAt_factorizes (activated queries larger ordinal) .audit).2

theorem payload_is_actual (queries : Nat → Query) (larger : Bool) (ordinal : Nat) :
    (projectionLaw queries larger).project () (ProgrammeSource.emitted (input queries larger)
      (ProgrammeHistory.visitAt (input queries larger) ordinal).current) () ordinal rfl = result queries larger ordinal := rfl

end SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.Runtime
