import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Runtime
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Response.Source
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Response.Cuts

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 6000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.ResponseRuntime

open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot

variable {fuel : ℚ} {inputs : List (List Action)} (cut : Cut fuel inputs)

noncomputable section

abbrev I := ObjectionRuntime.I cut (Response.emit cut)
abbrev previousRoot := ObjectionRuntime.root cut (Response.emit cut)
abbrev previousFacade := ObjectionRuntime.facade cut (Response.emit cut)

structure Transfer (original : Response.Pending cut) where
  private mk ::
  original_history : History fuel inputs original.claim
  original_exact : original_history = Response.oldHistory cut original
  before : History fuel (Response.nextInputs cut) (Response.transportedClaim cut original)
  before_exact : before = Response.newBefore cut original
  after : History fuel (Response.nextInputs cut) (Response.transportedClaim cut original)
  after_exact : after = Response.newAfter cut original
  crossing : (Objection.process fuel (Response.nextInputs cut) (Response.transportedClaim cut original)).Run
    before.state.current after.state.current

def transfer (original : Response.Pending cut) : Transfer cut original :=
  ⟨Response.oldHistory cut original, rfl, Response.newBefore cut original, rfl,
    Response.newAfter cut original, rfl, Response.fromCut _ (cut.depth + 2) 1⟩

def actualFunding : Option (Sigma fun lender : Bool => Financing.Disbursement law cut.past.frame.raw
    (Response.word cut.past.frame.raw) (Response.terms cut.past.frame.raw lender)) :=
  match Response.decideAt cut with | .current .. => Response.funding cut.past.frame.raw | _ => none

def actualFailures : List (Response.Failure cut.past.frame.raw) :=
  match Response.decideAt cut with | .current .. => Response.failures cut.past.frame.raw | _ => []

def actualOrders : List (Response.Order cut.past.frame.raw) :=
  match Response.decideAt cut with | .current .. => Response.orders cut.past.frame.raw | _ => []

structure Disposition where
  private mk ::
  decision : Response.Decision cut
  decision_exact : decision = Response.decideAt cut
  inherited : ObjectionRuntime.Disposition cut (Response.emit cut)
  inherited_exact : inherited = ObjectionRuntime.generate cut (Response.emit cut)
  transfers : (original : Response.Pending cut) → Transfer cut original
  transfers_exact : ∀ original, transfers original = transfer cut original
  financing : Option (Sigma fun lender : Bool => Financing.Disbursement law cut.past.frame.raw
    (Response.word cut.past.frame.raw) (Response.terms cut.past.frame.raw lender))
  financing_exact : financing = actualFunding cut
  failures : List (Response.Failure cut.past.frame.raw)
  failures_exact : failures = actualFailures cut
  orders : List (Response.Order cut.past.frame.raw)
  orders_exact : orders = actualOrders cut

def generate : Disposition cut :=
  ⟨Response.decideAt cut, rfl, ObjectionRuntime.generate cut (Response.emit cut), rfl,
    transfer cut, fun _ => rfl, actualFunding cut, rfl,
    actualFailures cut, rfl, actualOrders cut, rfl⟩

def projectionLaw : SourceNativeProjectionLaw
    (ProgrammeLiving.authoritySource (I cut)).restructuringSource.toLedgerSource where
  Projection := Unit
  ActiveAt := fun _ {_} _ => Unit
  InactiveAt := fun _ {_} _ => Empty
  classify := fun _ {_} _ => .inl ()
  PayloadAt := fun _ {current} _ _ =>
    current = (ProgrammeHistory.visitAt (I cut) (cut.depth + 2)).current → Disposition cut
  project := fun _ {_} _ _ _own => generate cut

def root := (previousRoot cut).withProjectionCoface (projectionLaw cut)

def stateAt (ordinal : Nat) : SourceNativeLivingRootCurrentAt (ProgrammeSource.N (I cut)) :=
  ⟨ProgrammeSource.V (I cut), root cut, ProgrammeHistory.temporalVisit (I cut) ordinal⟩

def process : SourceNativeLivingRootProcess (ProgrammeSource.N (I cut)) where
  State := Nat
  stateAt := stateAt cut
  stateAt_injective := by
    intro first second same
    have labels := congrArg
      (fun state : SourceNativeLivingRootCurrentAt (ProgrammeSource.N (I cut)) =>
        (⟨state.V.Current, state.visit.current⟩ : Sigma fun Carrier : Type => Carrier)) same
    have currents : (ProgrammeHistory.visitAt (I cut) first).current =
        (ProgrammeHistory.visitAt (I cut) second).current := eq_of_heq (Sigma.mk.inj labels).2
    exact ProgrammeHistory.visit_current_injective (I cut) currents
  initial := 0
  successorAt := fun ordinal => ⟨ordinal + 1, rfl, HEq.rfl⟩

inductive Face where
  | previous (face : ObjectionRuntime.Face)
  | feedback

def facade : SourceNativeLivingRuntimeFacade (ProgrammeSource.N (I cut)) where
  process := process cut
  FaceAt := fun _ => Face
  componentAt := fun _ face => match face with
    | .previous previous => (previousFacade cut).componentAt (previousFacade cut).seed previous
    | .feedback => projectionLaw cut
  installationAt := by
    intro state face
    cases face with
    | previous previous =>
        exact ((previousFacade cut).installationAt (previousFacade cut).seed previous).trans
          (SourceNativeProjectionLaw.InstallationAt.inheritedCoface
            (previousRoot cut).toAuthoritativeRoot.source (projectionLaw cut))
    | feedback =>
        exact SourceNativeProjectionLaw.InstallationAt.componentCoface
          (previousRoot cut).toAuthoritativeRoot.source (projectionLaw cut)
  projectionAt := fun _ face => match face with
    | .previous previous => (previousFacade cut).projectionAt (previousFacade cut).seed previous
    | .feedback => ()

def activated (ordinal : Nat) : LivingRuntimeState (process cut) :=
  (facade cut).seed.advance ordinal

end
end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.ResponseRuntime
