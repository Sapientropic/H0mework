import H0mework.Versions.Rf1d58550.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Birth.Flow
import H0mework.Versions.R2.Arithmetic.PrimeShadow.LivingLawRootDebtAdmissionActualActionKernel

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Birth

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Root
open Capitalism.Universal.Abolition
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open DebtActivationWorld DebtActivationLedger

noncomputable section

private theorem destination_after_support_cast {Base : WorldRelationNetwork} {L : DebtActivationLaw}
    {first last : L.DebtState} {before left right : Base.Support} (same : left = right)
    (old : LedgerWriteEvolutionAt Base ⟨before⟩ ⟨left⟩)
    (keys : Financial.Installation.KeepsKeys old)
    (owner : OpenResponsibilityAt Base before) (step : L.StepAt first last) :
    HEq (jointStepLedgerEvolution
      (show {write : LedgerWriteEvolutionAt Base ⟨before⟩ ⟨right⟩ // Financial.Installation.KeepsKeys write}
        from same ▸ ⟨old, keys⟩).val owner step).destination
      (jointStepLedgerEvolution old owner step).destination := by
  cases same
  rfl

variable {Party Good Port Technology Instrument Community : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  [DecidableEq Community]
  {source : Root.Cut Party Good Port Technology Instrument}
  {attack : RawEvent Party Good Port Technology Instrument}
  {community : Party → Community} {key : Key Party Good}
  (claim : ClaimAt source attack community key)

abbrev baseFrame := (attacked claim).native.full

/-- The admission compiler is a face at the existing visit. Its answer
value is the already occurred original damage, not a replacement state. -/
def filingComponent :
    SourceNativeProjectionLaw (baseFrame claim).root.toAuthoritativeRoot.toLedgerRoot.source where
  Projection := PUnit
  ActiveAt := fun _ {_} _ => PUnit
  InactiveAt := fun _ {_} _ => PEmpty
  classify := fun _ {_} _ => .inl PUnit.unit
  PayloadAt := fun _ {current} occurrence _ =>
    SourceNativeInquiryCompilationTokenAt (U7 := (baseFrame claim).basis.U7)
      (calculus := (baseFrame claim).basis.calculus)
      (oldTheory := (baseFrame claim).root.toAuthoritativeRoot.source.lawSurface)
      ((baseFrame claim).entry current) PUnit.unit (ULift.up.{1,0} occurrence) .answered ℚ
  project := fun _ {_} _ _ => .canonical (gross source attack community key)

abbrev old := (baseFrame claim).withProjectionCoface (filingComponent claim)
abbrev originalVisit := (attacked claim).native.visit
abbrev originalOwner := (old claim).entry (originalVisit claim).current
abbrev originalAuthority := (attacked claim).native.authority.withProjectionCoface (filingComponent claim)

private def inheritedProjection :
    SourceNativeProjectionLaw (Accounting.Root.Compiler.ledgerSource (flow claim)) where
  Projection := (old claim).root.toAuthoritativeRoot.source.projectionLaw.Projection
  ActiveAt := fun projection {_} _ => (old claim).root.toAuthoritativeRoot.source.projectionLaw.ActiveAt projection
    ((old claim).root.emitted (originalVisit claim).current)
  InactiveAt := fun projection {_} _ => (old claim).root.toAuthoritativeRoot.source.projectionLaw.InactiveAt projection
    ((old claim).root.emitted (originalVisit claim).current)
  classify := fun projection {_} _ => (old claim).root.toAuthoritativeRoot.source.projectionLaw.classify projection
    ((old claim).root.emitted (originalVisit claim).current)
  PayloadAt := fun projection {_} _ active => (old claim).root.toAuthoritativeRoot.source.projectionLaw.PayloadAt projection
    ((old claim).root.emitted (originalVisit claim).current) active
  project := fun projection {_} _ active => (old claim).root.toAuthoritativeRoot.source.projectionLaw.project projection
    ((old claim).root.emitted (originalVisit claim).current) active

def activeRoot := (Accounting.Root.Compiler.livingRoot (flow claim)).withProjectionCoface
  (inheritedProjection claim)

def originalProjection (projection : (old claim).root.toAuthoritativeRoot.source.projectionLaw.Projection) :
    (activeRoot claim).toAuthoritativeRoot.source.projectionLaw.Projection := .component projection

theorem original_projections_read_the_same_event
    (projection : (old claim).root.toAuthoritativeRoot.source.projectionLaw.Projection) :
    HEq ((activeRoot claim).toAuthoritativeRoot.source.projectionLaw.outcomeAt
      (originalProjection claim projection) ((activeRoot claim).emitted .pending))
      ((old claim).root.toAuthoritativeRoot.source.projectionLaw.outcomeAt projection
        ((old claim).root.emitted (originalVisit claim).current)) := by
  dsimp only [activeRoot, SourceNativeLivingRootClosure.withProjectionCoface,
    SourceNativeLivingRootClosure.toAuthoritativeRoot, SourceNativeAuthoritySource.withProjectionCoface,
    SourceNativeProjectionLaw.outcomeAt, originalProjection, inheritedProjection]
  cases (old claim).root.source.base.projectionLaw.classify projection
    ((old claim).root.emitted (originalVisit claim).current) <;> rfl

set_option maxHeartbeats 1000000 in
def targetAt (event : ExactTemporalCausalRootEventAt
    (old claim).root.toAuthoritativeRoot.toLedgerRoot (originalVisit claim)) :
    SourceNativeDebtAdmissionActualActionTargetAt (old claim).root (originalVisit claim) event
      (originalOwner claim) (originalAuthority claim) := by
  rw [event.eq_generated]
  let initial := Accounting.Root.Compiler.initialVisit (flow claim)
  let first := Accounting.Root.Compiler.successor (flow claim) Cursor.pending
  let base := (originalFrame claim).successor (originalVisit claim).current
  exact {
    law := law claim
    sourceState := .unfiled
    stepEvent := filing claim
    sourceSuccessor := base
    TargetV := Accounting.Root.Compiler.V (flow claim)
    targetRoot := activeRoot claim
    initialSupport_eq := rfl
    initialOldRow := fun entry => Accounting.Root.Compiler.generatedRow (flow claim) initial
      (oldEntry (law := law claim) (state? := some .unfiled) entry)
    initialBornRow := Accounting.Root.Compiler.generatedRow (flow claim) initial
      (debtEntry (law := law claim) ((originalFrame claim).sourceSupport (originalVisit claim).current) .unfiled)
    firstSuccessor := first
    firstSupport_eq := (Accounting.Root.Compiler.successor_support (flow claim) .pending).trans
      (congrArg (fun support => (support, some (filing claim).target))
        (original_target_support claim (originalVisit claim).current).symm)
    firstDestination_heq := (Accounting.Root.Compiler.successor_destination (flow claim) .pending).trans
      (destination_after_support_cast (original_target_support claim (originalVisit claim).current)
        base.ledgerEvolution ((originalFrame claim).successor_keys (originalVisit claim).current)
        (originalOwner claim) (filing claim).step)
    oldProjection := originalProjection claim
    oldProjection_injective := by
      intro left right same
      injection same
    oldOutcome_heq := original_projections_read_the_same_event claim
    canonical_targetNextVisit_eq :=
      Root.Registered.Macro.Ingress.next_is_the_same_generated_successor (activeRoot claim) initial first
    Answer := ℚ
    answer := gross source attack community key
    Receipt := fun amount => ULift.{3,0} (PLift (0 < amount))
    receipt := ⟨⟨claim.positive⟩⟩ }

def program :
    SourceNativeDebtAdmissionActualActionProgramAt (old claim).root (originalVisit claim)
      (originalOwner claim) (originalAuthority claim) where
  targetAt := targetAt claim

def generated := (program claim).generate
  ((old claim).root.toAuthoritativeRoot.toLedgerRoot.exactTemporalCausalEventAt (originalVisit claim))

/-- The born row is native and the successor is the very next original
visit with that row activated. Its first disposition leaves the balance due. -/
theorem born_debt_has_the_original_amount_and_a_live_successor :
    (generated claim).answer = gross source attack community key ∧
    (generated claim).target.admission.paidEntry.progressBudget = 1 ∧
    (generated claim).target.targetAnswerAndNext.nextCurrent =
      ⟨_, (activeRoot claim).toAuthoritativeRoot, (generated claim).target.targetVisit⟩ :=
  ⟨rfl, opening_budget claim, (generated claim).target.targetAnswerAndNext_next_eq⟩

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Birth
