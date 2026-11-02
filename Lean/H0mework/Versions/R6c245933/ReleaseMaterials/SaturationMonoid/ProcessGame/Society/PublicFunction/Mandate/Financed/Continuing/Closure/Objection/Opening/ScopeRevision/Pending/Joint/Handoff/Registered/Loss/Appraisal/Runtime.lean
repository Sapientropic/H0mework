import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.Registered.Loss.Appraisal

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.Registered.Loss.Appraisal
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root ResponsibilityLifecycle Followup
noncomputable section
variable {fuel : ℚ} {old : Followup.Joint.Inventory fuel} (authority : ScopeRevision.Ready old)
  {originInputs : List (List Action)} (inventory : Pending.Joint.Inventory authority originInputs)
  (fresh : Handoff.Ready (Pending.B authority) (Future.advance authority inventory .revision).inputs)
  (count : Nat) {unit : Good} (price : Original.Prices unit) (actor : Bool) (word : List Action)

structure Receipt where
  private mk ::
  baseline : Loss.Receipt authority inventory fresh word count
  financing : Finance.Data
  actualVisits : List Registered.Finance.Visit
  amounts : Bool → Bool → Good → ℚ
  positions : List (Responsibility.Row authority inventory fresh word (Loss.cursorAt authority inventory fresh word count).state)
  responsibilities : (row : Responsibility.Row authority inventory fresh word (Loss.cursorAt authority inventory fresh word count).state) → ResponsibilityState row.origin.V
  nativeHistories : (row : Responsibility.Row authority inventory fresh word (Loss.cursorAt authority inventory fresh word count).state) → row.native.Run row.origin.initial row.state
  opportunities : Original.Agency
  decision : Decision authority inventory fresh count price actor word
  response : Option (Sigma fun candidate : List Action => Loss.Receipt authority inventory fresh candidate count × Finance.Data)

def response := (classify authority inventory fresh count price actor word).selected.map fun candidate =>
  (⟨candidate,(Loss.Runtime.fromRoot authority inventory fresh candidate count,
    Finance.produce authority inventory fresh candidate count)⟩ :
      Sigma fun candidate : List Action => Loss.Receipt authority inventory fresh candidate count × Finance.Data)

def produce : Receipt authority inventory fresh count price actor word :=
  ⟨Loss.Runtime.fromRoot authority inventory fresh word count,Finance.produce authority inventory fresh word count,
    Finance.entries authority inventory fresh word count,Finance.account authority inventory fresh word count,
    List.finRange (Responsibility.census authority inventory fresh word (Loss.cursorAt authority inventory fresh word count).state).length,
    fun row => row.state,fun row => row.complete,agency authority inventory fresh count word,
    classify authority inventory fresh count price actor word,response authority inventory fresh count price actor word⟩
end
end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.Registered.Loss.Appraisal

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 6000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.Registered.Loss.Appraisal.Runtime

open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot Followup
variable {fuel : ℚ} {old : Followup.Joint.Inventory fuel} (authority : ScopeRevision.Ready old)
  {originInputs : List (List Action)} (inventory : Pending.Joint.Inventory authority originInputs)
  (fresh : Handoff.Ready (Pending.B authority) (Future.advance authority inventory .revision).inputs)
  (count : Nat) {unit : Good} (price : Appraisal.Original.Prices unit) (actor : Bool) (word : List Action)
noncomputable section

def projectionLaw : SourceNativeProjectionLaw
    (ProgrammeLiving.authoritySource (Loss.I authority inventory fresh word count)).restructuringSource.toLedgerSource where
  Projection := Unit
  ActiveAt := fun _ {_} _ => Unit
  InactiveAt := fun _ {_} _ => Empty
  classify := fun _ {_} _ => .inl ()
  PayloadAt := fun _ {current} _ _ => current = (ProgrammeHistory.visitAt (Loss.I authority inventory fresh word count) (Loss.ordinal authority inventory fresh word count)).current → Appraisal.Receipt authority inventory fresh count price actor word
  project := fun _ {_} _ _ _own => Appraisal.produce authority inventory fresh count price actor word

def root := (ProgrammeLiving.livingRoot (Loss.I authority inventory fresh word count)).withProjectionCoface (projectionLaw authority inventory fresh count price actor word)

theorem root_is_its_own_emitting_source : (root authority inventory fresh count price actor word).toAuthoritativeRoot.toRoot =
    (ProgrammeLiving.livingRoot (Loss.I authority inventory fresh word count)).toAuthoritativeRoot.toRoot := rfl

def stateAt (ordinal : Nat) : SourceNativeLivingRootCurrentAt (ProgrammeSource.N (Loss.I authority inventory fresh word count)) :=
  ⟨ProgrammeSource.V (Loss.I authority inventory fresh word count), root authority inventory fresh count price actor word, ProgrammeHistory.temporalVisit (Loss.I authority inventory fresh word count) ordinal⟩

def process : SourceNativeLivingRootProcess (ProgrammeSource.N (Loss.I authority inventory fresh word count)) where
  State := Nat
  stateAt := stateAt authority inventory fresh count price actor word
  stateAt_injective := by
    intro first second same
    have labels := congrArg
      (fun state : SourceNativeLivingRootCurrentAt (ProgrammeSource.N (Loss.I authority inventory fresh word count)) =>
        (⟨state.V.Current, state.visit.current⟩ : Sigma fun Carrier : Type => Carrier)) same
    have currents : (ProgrammeHistory.visitAt (Loss.I authority inventory fresh word count) first).current =
        (ProgrammeHistory.visitAt (Loss.I authority inventory fresh word count) second).current := eq_of_heq (Sigma.mk.inj labels).2
    exact ProgrammeHistory.visit_current_injective (Loss.I authority inventory fresh word count) currents
  initial := 0
  successorAt := fun ordinal => ⟨ordinal + 1, rfl, HEq.rfl⟩

inductive Face where
  | previous (face : ProgrammeLiving.Projection)
  | fullAccount

def facade : SourceNativeLivingRuntimeFacade (ProgrammeSource.N (Loss.I authority inventory fresh word count)) where
  process := process authority inventory fresh count price actor word
  FaceAt := fun _ => Face
  componentAt := fun _ face => match face with
    | .previous _ => ProgrammeLiving.projectionLaw (Loss.I authority inventory fresh word count)
    | .fullAccount => projectionLaw authority inventory fresh count price actor word
  installationAt := by
    intro state face
    cases face with
    | previous previous =>
        exact SourceNativeProjectionLaw.InstallationAt.inheritedCoface
          (ProgrammeLiving.livingRoot (Loss.I authority inventory fresh word count)).toAuthoritativeRoot.source (projectionLaw authority inventory fresh count price actor word)
    | fullAccount =>
        exact SourceNativeProjectionLaw.InstallationAt.componentCoface
          (ProgrammeLiving.livingRoot (Loss.I authority inventory fresh word count)).toAuthoritativeRoot.source (projectionLaw authority inventory fresh count price actor word)
  projectionAt := fun _ face => match face with
    | .previous previous => previous
    | .fullAccount => ()

def activated (ordinal : Nat) : LivingRuntimeState (process authority inventory fresh count price actor word) :=
  (facade authority inventory fresh count price actor word).seed.advance ordinal


end
end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.Registered.Loss.Appraisal.Runtime

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.Registered.Loss.Appraisal.Runtime
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root ResponsibilityLifecycle Followup
noncomputable section
variable {fuel : ℚ} {old : Followup.Joint.Inventory fuel} (authority : ScopeRevision.Ready old)
  {originInputs : List (List Action)} (inventory : Pending.Joint.Inventory authority originInputs)
  (fresh : Handoff.Ready (Pending.B authority) (Future.advance authority inventory .revision).inputs)
  (count : Nat) {unit : Good} (price : Appraisal.Original.Prices unit) (actor : Bool) (word : List Action)
def fromRoot : Appraisal.Receipt authority inventory fresh count price actor word :=
  (projectionLaw authority inventory fresh count price actor word).project ()
    (ProgrammeSource.emitted (Loss.I authority inventory fresh word count)
      (ProgrammeHistory.visitAt (Loss.I authority inventory fresh word count) (Loss.ordinal authority inventory fresh word count)).current) () rfl

theorem the_full_account_is_this_original_sources_generated_raw_next :
    (fromRoot authority inventory fresh count price actor word).baseline.cursor.before =
      ProgrammeSource.rawCurrent (Loss.I authority inventory fresh word count)
        (ProgrammeSource.next (Loss.I authority inventory fresh word count)
          (ProgrammeHistory.visitAt (Loss.I authority inventory fresh word count)
            (Loss.ordinal authority inventory fresh word count)).current) := by
  change (Loss.cursorAt authority inventory fresh word count).before =
    Handoff.Continuation.currentAt fresh (Loss.cursorAt authority inventory fresh word count).state.inputs
  exact (Loss.cursorAt authority inventory fresh word count).before_is_the_same_actual_current
end
end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.Registered.Loss.Appraisal.Runtime
