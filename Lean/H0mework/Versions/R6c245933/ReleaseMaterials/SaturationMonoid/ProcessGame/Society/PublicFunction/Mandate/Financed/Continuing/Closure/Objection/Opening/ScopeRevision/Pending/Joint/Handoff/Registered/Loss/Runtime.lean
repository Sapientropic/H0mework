import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.Registered.Loss.Source

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2500000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.Registered.Loss
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root ResponsibilityLifecycle Followup
open Institutions.Capitalism.Universal.Abolition.Accounting.Responsibility
noncomputable section

def remaining (book : Book) (actor : Bool) (good : Good) : ℚ := (book.map fun entry => entry.account.remaining (actor,good)).sum
def paid (book : Book) (actor : Bool) (good : Good) : ℚ := (book.map fun entry => entry.account.paid (actor,good)).sum
def quantity (book : Book) (actor : Bool) (good : Good) : ℚ := (book.map fun entry => Raw.quantity entry.original (actor,good)).sum

theorem the_complete_dynamic_book_has_one_original_quantity (book : Book) (actor : Bool) (good : Good) :
    remaining book actor good + paid book actor good = quantity book actor good := by
  unfold remaining paid quantity
  rw [← List.sum_map_add]
  apply congrArg List.sum
  apply List.map_congr_left
  intro entry _
  exact entry.account.balance (actor,good)

variable {fuel : ℚ} {old : Followup.Joint.Inventory fuel} (authority : ScopeRevision.Ready old)
  {originInputs : List (List Action)} (inventory : Pending.Joint.Inventory authority originInputs)
  (fresh : Handoff.Ready (Pending.B authority) (Future.advance authority inventory .revision).inputs) (original : List Action) (count : Nat)

def cursorAt := Source.run (Loss.initial authority inventory fresh original) count
abbrev I := Handoff.Continuation.inputAt fresh (cursorAt authority inventory fresh original count).state.inputs
def ordinal := (cursorAt authority inventory fresh original count).state.inputs.length+1

structure Receipt where
  private mk ::
  initial : Finance.Receipt authority inventory fresh original
  cursor : Cursor authority inventory fresh original
  continuation : (Financial.Family.process Pending.Joint.Finance.sources).Run
    (Registered.account authority inventory fresh original).current (cursorAt authority inventory fresh original count).state.finance.current
  attempt : Source.Assessment (cursorAt authority inventory fresh original count)
  nextRequest : List Action
  unpaid : Bool → Good → ℚ
  allocated : Bool → Good → ℚ
  originalQuantity : Bool → Good → ℚ

def produce : Receipt authority inventory fresh original count :=
  ⟨Finance.Runtime.fromRoot authority inventory fresh original,cursorAt authority inventory fresh original count,
    Source.runFinancial (Loss.initial authority inventory fresh original) count,
    Source.assess (cursorAt authority inventory fresh original count),(cursorAt authority inventory fresh original count).word,
    remaining (cursorAt authority inventory fresh original count).book,paid (cursorAt authority inventory fresh original count).book,
    quantity (cursorAt authority inventory fresh original count).book⟩
end
end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.Registered.Loss

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 6000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.Registered.Loss.Runtime

open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot Followup
variable {fuel : ℚ} {old : Followup.Joint.Inventory fuel} (authority : ScopeRevision.Ready old)
  {originInputs : List (List Action)} (inventory : Pending.Joint.Inventory authority originInputs)
  (fresh : Handoff.Ready (Pending.B authority) (Future.advance authority inventory .revision).inputs)
  (original : List Action) (count : Nat)
noncomputable section

def projectionLaw : SourceNativeProjectionLaw
    (ProgrammeLiving.authoritySource (Loss.I authority inventory fresh original count)).restructuringSource.toLedgerSource where
  Projection := Unit
  ActiveAt := fun _ {_} _ => Unit
  InactiveAt := fun _ {_} _ => Empty
  classify := fun _ {_} _ => .inl ()
  PayloadAt := fun _ {current} _ _ => current = (ProgrammeHistory.visitAt (Loss.I authority inventory fresh original count) (Loss.ordinal authority inventory fresh original count)).current → Loss.Receipt authority inventory fresh original count
  project := fun _ {_} _ _ _own => Loss.produce authority inventory fresh original count

def root := (ProgrammeLiving.livingRoot (Loss.I authority inventory fresh original count)).withProjectionCoface (projectionLaw authority inventory fresh original count)

theorem root_is_its_own_emitting_source : (root authority inventory fresh original count).toAuthoritativeRoot.toRoot =
    (ProgrammeLiving.livingRoot (Loss.I authority inventory fresh original count)).toAuthoritativeRoot.toRoot := rfl

def stateAt (ordinal : Nat) : SourceNativeLivingRootCurrentAt (ProgrammeSource.N (Loss.I authority inventory fresh original count)) :=
  ⟨ProgrammeSource.V (Loss.I authority inventory fresh original count), root authority inventory fresh original count, ProgrammeHistory.temporalVisit (Loss.I authority inventory fresh original count) ordinal⟩

def process : SourceNativeLivingRootProcess (ProgrammeSource.N (Loss.I authority inventory fresh original count)) where
  State := Nat
  stateAt := stateAt authority inventory fresh original count
  stateAt_injective := by
    intro first second same
    have labels := congrArg
      (fun state : SourceNativeLivingRootCurrentAt (ProgrammeSource.N (Loss.I authority inventory fresh original count)) =>
        (⟨state.V.Current, state.visit.current⟩ : Sigma fun Carrier : Type => Carrier)) same
    have currents : (ProgrammeHistory.visitAt (Loss.I authority inventory fresh original count) first).current =
        (ProgrammeHistory.visitAt (Loss.I authority inventory fresh original count) second).current := eq_of_heq (Sigma.mk.inj labels).2
    exact ProgrammeHistory.visit_current_injective (Loss.I authority inventory fresh original count) currents
  initial := 0
  successorAt := fun ordinal => ⟨ordinal + 1, rfl, HEq.rfl⟩

inductive Face where
  | previous (face : ProgrammeLiving.Projection)
  | lossAccount

def facade : SourceNativeLivingRuntimeFacade (ProgrammeSource.N (Loss.I authority inventory fresh original count)) where
  process := process authority inventory fresh original count
  FaceAt := fun _ => Face
  componentAt := fun _ face => match face with
    | .previous _ => ProgrammeLiving.projectionLaw (Loss.I authority inventory fresh original count)
    | .lossAccount => projectionLaw authority inventory fresh original count
  installationAt := by
    intro state face
    cases face with
    | previous previous =>
        exact SourceNativeProjectionLaw.InstallationAt.inheritedCoface
          (ProgrammeLiving.livingRoot (Loss.I authority inventory fresh original count)).toAuthoritativeRoot.source (projectionLaw authority inventory fresh original count)
    | lossAccount =>
        exact SourceNativeProjectionLaw.InstallationAt.componentCoface
          (ProgrammeLiving.livingRoot (Loss.I authority inventory fresh original count)).toAuthoritativeRoot.source (projectionLaw authority inventory fresh original count)
  projectionAt := fun _ face => match face with
    | .previous previous => previous
    | .lossAccount => ()

def activated (ordinal : Nat) : LivingRuntimeState (process authority inventory fresh original count) :=
  (facade authority inventory fresh original count).seed.advance ordinal


end
end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.Registered.Loss.Runtime

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.Registered.Loss.Runtime
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root ResponsibilityLifecycle Followup
noncomputable section
variable {fuel : ℚ} {old : Followup.Joint.Inventory fuel} (authority : ScopeRevision.Ready old)
  {originInputs : List (List Action)} (inventory : Pending.Joint.Inventory authority originInputs)
  (fresh : Handoff.Ready (Pending.B authority) (Future.advance authority inventory .revision).inputs) (original : List Action) (count : Nat)
def fromRoot : Loss.Receipt authority inventory fresh original count :=
  (projectionLaw authority inventory fresh original count).project ()
    (ProgrammeSource.emitted (Loss.I authority inventory fresh original count)
      (ProgrammeHistory.visitAt (Loss.I authority inventory fresh original count) (Loss.ordinal authority inventory fresh original count)).current) () rfl
end
end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.Registered.Loss.Runtime
