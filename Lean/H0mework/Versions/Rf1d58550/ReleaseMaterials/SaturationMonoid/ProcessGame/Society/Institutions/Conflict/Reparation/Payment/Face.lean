import H0mework.Versions.Rf1d58550.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Payment.Write

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Payment

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Abolition.Root.Registered.Macro
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open DebtActivationWorld DebtActivationLedger

noncomputable section

variable {Party Good Port Technology Instrument Community : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  [DecidableEq Community]
  {source : Conflict.Root.Cut Party Good Port Technology Instrument}
  {attack : RawEvent Party Good Port Technology Instrument}
  {community : Party → Community} {key : Key Party Good}
  (claim : ClaimAt source attack community key)
  (repair : Request Party Good Port Technology Instrument)

abbrev filed := (Birth.generated claim).target
abbrev filedVisit := (filed claim).targetVisit
abbrev filedOwner := (filed claim).targetRoot.toAuthoritativeRoot.toLedgerRoot.canonicalTargetEntryAtNext
  (filed claim).firstSuccessor.next_eq (filed claim).translatedSourceEntry

def basis : Inquiry.Basis (Birth.N claim) where
  entry := fun atSupport =>
    match atSupport with
    | ⟨prior, none⟩ => oldEntry (state? := none) ((Birth.originalFrame claim).family.entry prior)
    | ⟨prior, some debt⟩ => debtEntry prior debt
  disposition := by
    intro atSupport kind
    cases kind with
    | supportSettlement => exact (Birth.originalFrame claim).family.disposition atSupport.1 .supportSettlement
    | transfer => exact .inl ((Birth.originalFrame claim).family.disposition atSupport.1 .transfer)
    | lawSurfaceExtension => exact .inl ((Birth.originalFrame claim).family.disposition atSupport.1 .lawSurfaceExtension)

def ownerAt (current : Birth.Cursor claim) :
    OpenResponsibilityAt (Birth.N claim) (Birth.support claim current) := by
  classical
  exact if same : current = (filedVisit claim).current then
    same.symm ▸ filedOwner claim else (basis claim).entry (Birth.support claim current)

theorem ownerAt_is_the_actual_filed_owner :
    ownerAt claim (filedVisit claim).current = filedOwner claim := by
  unfold ownerAt
  exact dif_pos (show (filedVisit claim).current = (filedVisit claim).current from rfl)

/-- The new inquiry is a projection of the already active liability visit.
No new admission or replacement whole-ledger source is introduced. -/
def continuationComponent :
    SourceNativeProjectionLaw (filed claim).targetRoot.toAuthoritativeRoot.toLedgerRoot.source where
  Projection := PUnit
  ActiveAt := fun _ {_} _ => PUnit
  InactiveAt := fun _ {_} _ => PEmpty
  classify := fun _ {_} _ => .inl PUnit.unit
  PayloadAt := fun _ {current} occurrence _ =>
    SourceNativeInquiryCompilationTokenAt (U7 := (basis claim).U7) (calculus := (basis claim).calculus)
      (oldTheory := (filed claim).targetRoot.toAuthoritativeRoot.source.lawSurface)
      (ownerAt claim current) PUnit.unit (ULift.up.{1,0} occurrence) .answered ℚ
  project := fun _ {_} _ _ => .canonical (remaining source attack [repair] community key)

abbrev filedRoot := (filed claim).targetRoot.withProjectionCoface (continuationComponent claim repair)

abbrev filedAuthority := ((filed claim).initialAuthority.next (filed claim).firstSuccessor.next_eq)
  |>.withProjectionCoface (continuationComponent claim repair)

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Payment
