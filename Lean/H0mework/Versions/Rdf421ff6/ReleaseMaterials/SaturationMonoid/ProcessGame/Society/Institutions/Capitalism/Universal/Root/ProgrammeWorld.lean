import H0mework.Versions.R2.Foundation.Inquiry.MinimalCoface
import H0mework.Checks.Runtime.OperationalSeparation

/-!
# The finite programme's faithful richer world

The initial support has exactly the migrated old row and the obstruction
row.  Instruction rows enter only through the first source write.  A slot
is an ongoing responsibility for one registered instruction; its claim and
root lineage are preserved across subsequent executions.  Fresh financial
claims require the separate original debt-admission mechanism.
-/

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.ProgrammeWorld

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open ConstructiveRoot.ObstructionGeneratedMinimalCoface

inductive Support (Data : Type)
  | inherited (support : Bool)
  | bootstrap
  | running (current : Data) (past : List Data)

inductive Row (count : Nat)
  | inherited
  | obstruction
  | instruction (index : Fin count)
  deriving DecidableEq

/-- Source code, not a caller-selected receipt.  Its generated value is also
available to the material emitter. -/
structure ObservationLaw (Data Payload : Type) where
  generate : Data → Payload

def TransferReceiptAt {Data Payload : Type}
    (observation? : Option (ObservationLaw Data Payload)) (support : Support Data) : Type :=
  match observation? with
  | none => Unit
  | some observation => match support with
    | .running current _ => {payload : Payload // payload = observation.generate current}
    | _ => Unit

def transferReceipt {Data Payload : Type} (observation? : Option (ObservationLaw Data Payload))
    (support : Support Data) : TransferReceiptAt observation? support := by
  cases observation? with
  | none => exact ()
  | some observation =>
      cases support with
      | inherited _ => exact ()
      | bootstrap => exact ()
      | running current _ => exact ⟨observation.generate current, rfl⟩

def OpenAt {Data : Type} {count : Nat} : Support Data → Row count → Type
  | .inherited _, .inherited => Unit
  | .inherited _, _ => PEmpty
  | .bootstrap, .instruction _ => PEmpty
  | .bootstrap, _ => Unit
  | .running _ _, _ => Unit

def claim {count : Nat} : Row count → Bool
  | .obstruction => true
  | _ => false

def progressBudget {Data : Type} {count : Nat} :
    (support : Support Data) → (row : Row count) → OpenAt support row → Nat
  | .inherited _, .inherited, _ => 2
  | .inherited _, .obstruction, impossible => impossible.elim
  | .inherited _, .instruction _, impossible => impossible.elim
  | .bootstrap, .inherited, _ => 2
  | .bootstrap, .obstruction, _ => 0
  | .bootstrap, .instruction _, impossible => impossible.elim
  | .running _ _, .obstruction, _ => 0
  | .running _ _, _, _ => 1

def network (Data : Type) (count : Nat) (Payload : Type := Unit)
    (observation? : Option (ObservationLaw Data Payload) := none) : WorldRelationNetwork where
  Support := Support Data
  Anchor := Unit
  Incidence := Bool
  Lineage := Unit
  Responsibility := Row count
  Claim := Bool
  anchorAt := fun _ => ()
  incidenceAt := fun support => match support with | .inherited _ => false | _ => true
  lineageAt := fun _ => ()
  OpenAt := OpenAt
  openClaimAt := fun {_support responsibility} _ => claim responsibility
  openProgressBudgetAt := fun {support responsibility} opened =>
    progressBudget support responsibility opened
  HoldsAt := fun support value => match support, value with
    | .inherited _, true => PEmpty
    | _, _ => Unit
  ObstructionAt := fun _ => Unit
  obstructionClaim := fun _ => false
  SemanticChangeAt := fun _ _ _ => Unit
  DispositionAt := fun support kind => match kind with
    | .transfer => TransferReceiptAt observation? support
    | _ => Unit

def supportRetraction (Data : Type) : ConstructiveRetract Bool (Support Data) where
  forward := Support.inherited
  backward := fun support => match support with | .inherited old => old | _ => true
  backward_forward := fun _ => rfl

def flagRetraction : ConstructiveRetract Unit Bool where
  forward := fun _ => false
  backward := fun _ => ()
  backward_forward := fun value => by cases value; rfl

def rowRetraction (count : Nat) : ConstructiveRetract Unit (Row count) where
  forward := fun _ => .inherited
  backward := fun _ => ()
  backward_forward := fun value => by cases value; rfl

def oldLedgerRetraction (Data : Type) (count : Nat) (oldSupport : Bool) (Payload : Type := Unit)
    (observation? : Option (ObservationLaw Data Payload) := none) :
    ConstructiveRetract
      (OpenResponsibilityAt OperationalSeparationRegression.N oldSupport)
      (OpenResponsibilityAt (network Data count Payload observation?) (.inherited oldSupport)) where
  forward := fun _ => ⟨.inherited, ()⟩
  backward := fun _ => ⟨(), ()⟩
  backward_forward := by
    rintro ⟨row, opened⟩
    cases row
    cases opened
    rfl

def translation (Data : Type) (count : Nat) (Payload : Type := Unit)
    (observation? : Option (ObservationLaw Data Payload) := none) :
    TypedSemanticWorldNetworkTranslationAt OperationalSeparationRegression.N
      (network Data count Payload observation?) where
  support := supportRetraction Data
  anchor := ⟨id, id, fun _ => rfl⟩
  incidence := flagRetraction
  lineage := ⟨id, id, fun _ => rfl⟩
  responsibility := rowRetraction count
  claim := flagRetraction
  anchor_commutes := fun _ => rfl
  incidence_commutes := fun _ => rfl
  lineage_commutes := fun _ => rfl
  oldOpenLedger := fun support => oldLedgerRetraction Data count support Payload observation?
  oldOpenClaim_commutes := fun _ _ => rfl
  oldOpenProgressBudget_commutes := fun _ _ => rfl
  oldHoldsSurvives := fun _ _ _ => ()
  oldDispositionSurvives := by
    intro support kind receipt
    cases kind <;> cases observation? <;> exact ()

def inheritedEntry (Data : Type) (count : Nat) :
    OpenResponsibilityAt (network Data count) .bootstrap := ⟨.inherited, ()⟩

def obstructionEntry (Data : Type) (count : Nat) :
    OpenResponsibilityAt (network Data count) .bootstrap := ⟨.obstruction, ()⟩

theorem bootstrap_no_dormant (Data : Type) (count : Nat)
    (entry : OpenResponsibilityAt (network Data count) .bootstrap) :
    entry = inheritedEntry Data count ∨ entry = obstructionEntry Data count := by
  rcases entry with ⟨row, opened⟩
  cases row with
  | inherited => cases opened; exact Or.inl rfl
  | obstruction => cases opened; exact Or.inr rfl
  | instruction index => exact opened.elim

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.ProgrammeWorld
