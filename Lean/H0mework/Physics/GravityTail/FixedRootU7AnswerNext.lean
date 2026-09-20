import H0mework.Foundation.Inquiry.ObstructionLineage
import H0mework.Foundation.Authority.EntryDisposition
import H0mework.Foundation.Authority.Representation
import H0mework.Physics.GravityTail.FixedLivingRoot

/-!
# Fixed gravity-tail residual in the same root U7 answer-and-next history
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace PhysicsCore
namespace StageNineDiracDualFormNativeFixedP506CartanECConstraintCauchyGravityTailRootU7AnswerNext

open ResponsibilityLifecycle.LivingLawEvolution
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open ProofFreeRicherAnholonomicSource
open StageNineDiracDualFormNativeFixedP506CartanECConstraintCauchyGravityTailAllPointResidualNormalForm
open StageNineDiracDualFormNativeFixedP506CartanECConstraintCauchyGravityTailLivingRoot
open StageNineDiracDualFormNativeFixedP506CartanECConstraintCauchyGravityTailRootNativeWrite
open StageNineDiracDualFormNativeFixedP506CartanECConstraintCauchyWholeSpacetimeAssembly
open StageNineDiracDualFormNativeCartanECSynchronizedGravityTailJointPathOperator
open StageNineDiracDualFormNativeCartanECSynchronizedGravityTailJointPathGLCoframe
open StageNineDiracDualFormNativeCartanECSynchronizedGravityTailLorentzPathOperator
open StageNineDiracDualFormNativeCompleteJointActionSpacetimeSectionOperator
open StageNineDiracDualFormNativePointwiseActionJetCarrier
open StageNineEnrichedProofFreeSource
open StageNineHolonomicField
open StageNineFormNativeP286GaugeYangMillsReadout

noncomputable section

private abbrev Source : SmoothUnifiedSource := positiveSmoothUnifiedSource

private abbrev Coface : RootCurrent := quadraticCofaceCurrent

private abbrev FirstGravity : RootCurrent := firstGravityCurrent

private abbrev FirstAssembly : RootCurrent := firstAssemblyCurrent

private abbrev FirstPostAssembly : RootCurrent := firstPostAssemblyGravityCurrent

/-- Exact residual obstruction, source-generated demand, and living-root
answer-and-next remain one dependent carrier.  The root may use one whole
residual write to answer several coordinates, but no caller can erase which
obstruction generated this particular demand incidence. -/
structure SourceNativeRootResidualAnswerAndNextAt
    (visit : SourceNativeTemporalVisitAt sourceNativeRoot)
    (obstruction : N.ObstructionAt visit.current)
    (causalEntryAuthority :
      SourceNativeLivingTemporalCausalEntryAuthorityAt livingRoot visit
        (rootU7.generateDemand obstruction).entry) : Type 3 where
  private mk ::
  demandAuthority :
    SourceGeneratedU7DemandAt rootU7 obstruction
      (rootU7.generateDemand obstruction)
  answerAndNext :
    SourceNativeLivingCausalEntryAnswerAndNextAt livingRoot visit
      (rootU7.generateDemand obstruction).entry causalEntryAuthority

/-- The only producer is the exact obstruction-indexed U7 demand together
with the canonical living-root answer at the same temporal visit. -/
def SourceNativeRootResidualAnswerAndNextAt.generated
    (visit : SourceNativeTemporalVisitAt sourceNativeRoot)
    (obstruction : N.ObstructionAt visit.current)
    (causalEntryAuthority :
      SourceNativeLivingTemporalCausalEntryAuthorityAt livingRoot visit
        (rootU7.generateDemand obstruction).entry) :
    SourceNativeRootResidualAnswerAndNextAt visit obstruction
      causalEntryAuthority :=
  ⟨.canonical obstruction,
    livingRoot.generatedCausalEntryAnswerAndNextAt visit
      (rootU7.generateDemand obstruction).entry causalEntryAuthority⟩

def initialGeneratedEntryRow :
    (sourceNativeRoot.generatedAtTemporalVisit
      (.finite sourceNativeRoot.toRoot.initialVisit)).GeneratedEntryRowAt
        (rootLedgerEntry Initial) :=
  ((sourceNativeRoot.generatedAtTemporalVisit
      (.finite sourceNativeRoot.toRoot.initialVisit)).canonicalGeneratedEntryRow?
    (rootLedgerEntry Initial)).get (by rfl)

def initialCausalEntryAuthority :
    SourceNativeLivingTemporalCausalEntryAuthorityAt livingRoot
      initialTemporalVisit (rootLedgerEntry Initial) :=
  SourceNativeLivingTemporalCausalEntryAuthorityAt.generatedFromInitialRow
    livingRoot (rootLedgerEntry Initial) initialGeneratedEntryRow

private theorem initial_next_eq :
    (root.evolutionAt Initial).nextCurrent? = some Coface :=
  rfl

def nextTemporalVisit : SourceNativeTemporalVisitAt sourceNativeRoot :=
  initialTemporalVisit.next initial_next_eq

def nextCausalEntryAuthority :
    SourceNativeLivingTemporalCausalEntryAuthorityAt livingRoot
      nextTemporalVisit (rootLedgerEntry Coface) := by
  exact initialCausalEntryAuthority.next initial_next_eq

private theorem coface_next_eq :
    (root.evolutionAt Coface).nextCurrent? = some FirstGravity :=
  rfl

def afterCofaceTemporalVisit : SourceNativeTemporalVisitAt sourceNativeRoot :=
  nextTemporalVisit.next coface_next_eq

def afterCofaceCausalEntryAuthority :
    SourceNativeLivingTemporalCausalEntryAuthorityAt livingRoot
      afterCofaceTemporalVisit (rootLedgerEntry FirstGravity) := by
  exact nextCausalEntryAuthority.next coface_next_eq

private theorem gravity_next_eq :
    (root.evolutionAt FirstGravity).nextCurrent? = some FirstAssembly :=
  rfl

def afterGravityTemporalVisit : SourceNativeTemporalVisitAt sourceNativeRoot :=
  afterCofaceTemporalVisit.next gravity_next_eq

def afterGravityCausalEntryAuthority :
    SourceNativeLivingTemporalCausalEntryAuthorityAt livingRoot
      afterGravityTemporalVisit (rootLedgerEntry FirstAssembly) := by
  exact afterCofaceCausalEntryAuthority.next gravity_next_eq

private theorem assembly_next_eq :
    (root.evolutionAt FirstAssembly).nextCurrent? = some FirstPostAssembly :=
  rfl

def afterAssemblyTemporalVisit : SourceNativeTemporalVisitAt sourceNativeRoot :=
  afterGravityTemporalVisit.next assembly_next_eq

def afterAssemblyCausalEntryAuthority :
    SourceNativeLivingTemporalCausalEntryAuthorityAt livingRoot
      afterAssemblyTemporalVisit (rootLedgerEntry FirstPostAssembly) := by
  exact afterGravityCausalEntryAuthority.next assembly_next_eq

/-! ## Same-root post-U7 continuation -/

/-- The canonical successor of the first post-assembly gravity row.  This is
an alias for the existing root `Next`; it introduces no new current
constructor or lifecycle. -/
def secondAssemblyCurrent : RootCurrent :=
  Next firstPostAssemblyGravityCurrent

@[simp] theorem next_firstPostAssemblyGravityCurrent_eq_secondAssemblyCurrent :
    Next firstPostAssemblyGravityCurrent = secondAssemblyCurrent :=
  rfl

/-- The post-U7 successor is the exact GL gravity occurrence followed by its
same-action P286 constitutive refresh. -/
@[simp] theorem secondAssemblyCurrent_configuration_eq_postGravityP286Refresh :
    secondAssemblyCurrent.configuration =
      formNativeP286GaugeConstitutiveReadout Source
        (sourceActionGeneratedCartanECSynchronizedGravityTailGLOccurrence
          Source
            (rootActionAt firstPostAssemblyGravityCurrent).p286Stage
          ).finalActual :=
  rfl

/-- One more canonical visit in the already registered physical root
history. -/
def afterPostAssemblyTemporalVisit :
    SourceNativeTemporalVisitAt sourceNativeRoot :=
  afterAssemblyTemporalVisit.next rfl

/-- Whole-ledger causal authority for the generated second assembly row. -/
def afterPostAssemblyCausalEntryAuthority :
    SourceNativeLivingTemporalCausalEntryAuthorityAt livingRoot
      afterPostAssemblyTemporalVisit (rootLedgerEntry secondAssemblyCurrent) :=
  afterAssemblyCausalEntryAuthority.next rfl

/-- At the successor the old gravity coordinate is phase-closed; the live
responsibility is the newly generated assembly seam. -/
@[simp] theorem rootResidualAt_secondAssemblyCurrent_gravity_zero :
    (rootResidualAt secondAssemblyCurrent).gravity = 0 :=
  rfl

@[simp] theorem rootResidualAt_secondAssemblyCurrent_assembly
    (point : BasePoint) :
    (rootResidualAt secondAssemblyCurrent).assembly point =
      candidateAssemblySeam Source secondAssemblyCurrent.configuration point :=
  rfl

/-- The generated post-assembly gravity output admits exact reconstruction
from its dependent seam and matching source contact at the second assembly
current.  No nonzero witness, U7 answer, or target field is supplied. -/
theorem root_secondAssembly_gravityStage_actionJet_eq_residualWriteBack
    (point : BasePoint) :
    generatedDiracDualFormNativePointwiseActionJet
        Source
        (sourceActionGeneratedCartanECSynchronizedGravityTailGLOccurrence
          Source (rootActionAt firstPostAssemblyGravityCurrent).p286Stage
          ).finalActual point =
      pointwiseActionJetWithGravityTailSeam
        (generatedDiracDualFormNativePointwiseActionJet Source
          (cartanECSynchronizedGravityTailProfileContact
            Source (rootActionAt firstPostAssemblyGravityCurrent).p286Stage
              point) 0)
        ((rootResidualAt firstPostAssemblyGravityCurrent).gravity point) := by
  exact sourceActionGeneratedGravityTailGL_actionJet_naturality
    Source (rootActionAt firstPostAssemblyGravityCurrent).p286Stage point

/-- The unique physical row authority generated along a finite root history. -/
private def finiteCausalEntryAuthorityAt
    {current : RootCurrent}
    (history : root.ReachableAt current) :
    SourceNativeLivingTemporalCausalEntryAuthorityAt livingRoot
      (.finite ⟨current, history⟩) (rootLedgerEntry current) :=
  match history with
  | .initial => initialCausalEntryAuthority
  | .step prior next_eq =>
      let generated := (finiteCausalEntryAuthorityAt prior).next next_eq
      have entry_eq := rootLedgerEntry_unique current
        (sourceNativeRoot.canonicalTargetEntryAtNext next_eq
          (rootLedgerEntry _))
      entry_eq ▸ generated

/-- A post-cofinal history cannot begin for this physical root: its fixed
cofinal event carrier is empty.  The recursive case is retained only so the
unified temporal visit API has one total source-generated authority readout. -/
private def postCofinalCausalEntryAuthorityAt
    {current : RootCurrent}
    (history : SourceNativePostCofinalReachableAt sourceNativeRoot current) :
    SourceNativeLivingTemporalCausalEntryAuthorityAt livingRoot
      ⟨current, .postCofinal history⟩ (rootLedgerEntry current) :=
  match history with
  | .cofinal visit => nomatch visit.event
  | .step prior next_eq =>
      let generated := (postCofinalCausalEntryAuthorityAt prior).next next_eq
      have entry_eq := rootLedgerEntry_unique current
        (sourceNativeRoot.canonicalTargetEntryAtNext next_eq
          (rootLedgerEntry _))
      entry_eq ▸ generated

/-- Every exact temporal visit of the fixed physical root carries its own
canonical whole-row authority.  No entry, source, or successor is accepted at
this mouth. -/
def rootCausalEntryAuthorityAt
    (visit : SourceNativeTemporalVisitAt sourceNativeRoot) :
    SourceNativeLivingTemporalCausalEntryAuthorityAt livingRoot visit
      (rootLedgerEntry visit.current) := by
  rcases visit with ⟨current, history⟩
  cases history with
  | finite finiteHistory =>
      exact finiteCausalEntryAuthorityAt finiteHistory
  | postCofinal postCofinalHistory =>
      exact postCofinalCausalEntryAuthorityAt postCofinalHistory

/-- One positive U7 mouth covers the complete dependent residual inventory at
every exact temporal visit.  The coordinate selects only a face of the
already generated residual; source, row authority, answer, and next remain
fixed by the visit. -/
def rootResidualDemandAt
    {support : RootCurrent}
    (coordinate : RootResidualCoordinate)
    (point : BasePoint)
    (evidence :
      (rootResidualAt support).coordinateAt coordinate point) :
    rootU7.DemandAt
      (rootResidualObstructionAt coordinate point evidence) :=
  rootU7.generateDemand
    (rootResidualObstructionAt coordinate point evidence)

def sourceGeneratedRootResidualAnswerAndNextAt
    (visit : SourceNativeTemporalVisitAt sourceNativeRoot)
    (coordinate : RootResidualCoordinate)
    (point : BasePoint)
    (evidence :
      (rootResidualAt visit.current).coordinateAt coordinate point) :
    SourceNativeRootResidualAnswerAndNextAt visit
      (rootResidualObstructionAt coordinate point evidence)
      (rootCausalEntryAuthorityAt visit) :=
  .generated visit (rootResidualObstructionAt coordinate point evidence)
    (rootCausalEntryAuthorityAt visit)

/-- Temporal registration retains the Physics residual as the dependent face
of this exact root occurrence. -/
theorem temporal_residual_projection_factorizes
    (visit : SourceNativeTemporalVisitAt authoritativeRoot.toLedgerRoot) :
    HEq
      ((authoritativeRoot.toLedgerRoot.generatedAtTemporalVisit visit
        ).projectionOutcome .residual)
      (authoritativeRoot.projectionOutcomeAt .residual visit.current) :=
  (authoritativeRoot.toLedgerRoot.generatedAtTemporalVisit visit
    ).projectionOutcome_heq_sourceOutcome .residual

/-! ## Quadratic boundary failure → exact demand → revised root current -/

def quadraticCoframeBoundaryDemand :
    rootU7.DemandAt fixedRootQuadraticCoframeBoundaryObstruction :=
  rootU7.generateDemand fixedRootQuadraticCoframeBoundaryObstruction

/-- The rooted old-carrier obstruction, its generated demand, and the first
coface answer remain one source-native return carrier. -/
def quadraticCoframeBoundaryAnswerAndNext :
    SourceNativeRootResidualAnswerAndNextAt initialTemporalVisit
      fixedRootQuadraticCoframeBoundaryObstruction
      initialCausalEntryAuthority :=
  .generated initialTemporalVisit
    fixedRootQuadraticCoframeBoundaryObstruction
    initialCausalEntryAuthority

/-- The exact old-carrier failure is carried by the source-native boundary
write into its target as revised debt.  The semantic-change receipt belongs
to the U7 disposition, not to a sibling root compiler branch. -/
theorem quadraticCoframeBoundaryDemand_generates_revisedRootCurrent :
    quadraticCoframeBoundaryDemand.entry = rootLedgerEntry Initial ∧
      root.evolutionAt Initial =
        EvolutionAt.nativeWrite (rootActionAt Initial) ∧
      (root.evolutionAt Initial).nextCurrent? = some Coface ∧
      (rootLedgerEntry Coface).1.coframeBoundary = .revised := by
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- The target responsibility is the affected inventory of the next actual
root occurrence; it is not parked in a parallel demand ledger. -/
@[simp] theorem nextOccurrence_consumes_targetEntry :
    rootOccurrenceLedgerEntry (rootEmitted Coface) =
      rootLedgerEntry Coface :=
  rfl

/-- The first revised occurrence is the source-generated coface consumer. -/
@[simp] theorem nextOccurrence_is_quadraticCofaceWrite :
    root.evolutionAt Coface =
      EvolutionAt.nativeWrite (rootActionAt Coface) :=
  rfl

/-- The coface consumer's target resumes the existing gravity writer with
the boundary account settled in the same live ledger. -/
@[simp] theorem afterCofaceOccurrence_is_gravityWrite :
    root.evolutionAt FirstGravity =
      EvolutionAt.nativeWrite (rootActionAt FirstGravity) :=
  rfl

/-- The following occurrence is the whole-spacetime assembly writer, not a
second gravity-tail occurrence selected by a presentation. -/
@[simp] theorem afterGravityOccurrence_is_wholeSpacetimeAssembly :
    root.evolutionAt FirstAssembly =
      EvolutionAt.nativeWrite (rootActionAt FirstAssembly) :=
  rfl

/-- A nonzero gravity-tail residual is answered only through the fixed living
root's canonical causal court.  The domain contributes the exact obstruction;
the answer, ledger transition, and next current are generated by `livingRoot`.
-/
def fixedRootResidualAnswerAndNext
    (point : BasePoint)
    (nonzero :
      (rootResidualAt FirstGravity).gravity point ≠ 0) :
    SourceNativeRootResidualAnswerAndNextAt afterCofaceTemporalVisit
      (fixedRootObstructionAt point nonzero)
      afterCofaceCausalEntryAuthority :=
  .generated afterCofaceTemporalVisit
    (fixedRootObstructionAt point nonzero)
    afterCofaceCausalEntryAuthority

/-- Exact demand generated by a nonzero repaired-action residual on the
current whole-ledger row. -/
def rootClassicalJointDemandAt
    {support : N.Support}
    (point : BasePoint)
    (nonzero : (rootResidualAt support).classicalJoint point ≠ 0) :
    rootU7.DemandAt (rootClassicalJointObstructionAt point nonzero) :=
  rootResidualDemandAt .classicalJoint point (PLift.up nonzero)

/-- SafeFinal specialization of the same-row repaired-action demand. -/
def fixedRootClassicalJointDemandAt
    (point : BasePoint)
    (nonzero :
      (rootResidualAt FirstGravity).classicalJoint point ≠ 0) :
    rootU7.DemandAt
      (fixedRootClassicalJointObstructionAt point nonzero) :=
  rootClassicalJointDemandAt point nonzero

/-- A nonzero SafeFinal repaired-action residual reuses the existing gravity
causal court and its compiler-generated assembly successor. -/
def fixedRootClassicalJointAnswerAndNextAt
    (point : BasePoint)
    (nonzero :
      (rootResidualAt FirstGravity).classicalJoint point ≠ 0) :
    SourceNativeRootResidualAnswerAndNextAt afterCofaceTemporalVisit
      (fixedRootClassicalJointObstructionAt point nonzero)
      afterCofaceCausalEntryAuthority :=
  .generated afterCofaceTemporalVisit
    (fixedRootClassicalJointObstructionAt point nonzero)
    afterCofaceCausalEntryAuthority

/-- Exact demand for a first-jet effect at any root current. -/
def rootCoframeFirstJetDemandAt
    {support : N.Support}
    (point : BasePoint)
    (nonzero :
      (rootResidualAt support).gravityCoframeFirstJet point ≠ 0) :
    rootU7.DemandAt (rootCoframeFirstJetObstructionAt point nonzero) :=
  rootResidualDemandAt .gravityCoframeFirstJet point (PLift.up nonzero)

/-- Exact demand generated by the first-gravity specialization. -/
def fixedRootCoframeFirstJetDemandAt
    (point : BasePoint)
    (nonzero :
      (rootResidualAt FirstGravity).gravityCoframeFirstJet point ≠ 0) :
    rootU7.DemandAt
      (fixedRootCoframeFirstJetObstructionAt point nonzero) :=
  rootCoframeFirstJetDemandAt point nonzero

/-- The new coordinate reuses the existing first-gravity causal court; it
does not create a second residual registry or successor compiler. -/
def fixedRootCoframeFirstJetAnswerAndNextAt
    (point : BasePoint)
    (nonzero :
      (rootResidualAt FirstGravity).gravityCoframeFirstJet point ≠ 0) :
    SourceNativeRootResidualAnswerAndNextAt afterCofaceTemporalVisit
      (fixedRootCoframeFirstJetObstructionAt point nonzero)
      afterCofaceCausalEntryAuthority :=
  .generated afterCofaceTemporalVisit
    (fixedRootCoframeFirstJetObstructionAt point nonzero)
    afterCofaceCausalEntryAuthority

/-! ## First assembly integrability seam → exact demand → next gravity write -/

def fixedRootAssemblyDemandAt
    (point : BasePoint)
    (nonzero :
      (rootResidualAt FirstAssembly).assembly point ≠ 0) :
    rootU7.DemandAt (fixedRootAssemblyObstructionAt point nonzero) :=
  rootResidualDemandAt .assembly point (PLift.up nonzero)

/-- The assembly obstruction uses the same shared causal court; no domain
record may submit a sibling target authority. -/
def fixedRootAssemblyAnswerAndNextAt
    (point : BasePoint)
    (nonzero :
      (rootResidualAt FirstAssembly).assembly point ≠ 0) :
    SourceNativeRootResidualAnswerAndNextAt afterGravityTemporalVisit
      (fixedRootAssemblyObstructionAt point nonzero)
      afterGravityCausalEntryAuthority :=
  .generated afterGravityTemporalVisit
    (fixedRootAssemblyObstructionAt point nonzero)
    afterGravityCausalEntryAuthority

/-- A nonzero assembly seam cannot remain a readout beside the live root.
It generates the exact demand on the existing assembly ledger entry, and the
same root compiler consumes that entry with the already installed
whole-spacetime write before exposing the next gravity current. -/
theorem fixedRootAssemblyDemand_generates_nextGravityWrite
    (point : BasePoint)
    (nonzero :
      (rootResidualAt FirstAssembly).assembly point ≠ 0) :
    (fixedRootAssemblyDemandAt point nonzero).entry =
        rootLedgerEntry FirstAssembly ∧
      root.evolutionAt FirstAssembly =
        EvolutionAt.nativeWrite (rootActionAt FirstAssembly) ∧
      (root.evolutionAt FirstAssembly).nextCurrent? =
        some FirstPostAssembly ∧
      generatedDiracDualFormNativePointwiseActionJet
          Source FirstPostAssembly.configuration point =
        pointwiseActionJetWithCompleteJointAssemblySeam
          (contactActionJet Source FirstAssembly.configuration point)
          ((rootResidualAt FirstAssembly).assembly point) := by
  exact ⟨rfl, rfl, rfl,
    root_firstPostAssembly_actionJet_eq_residualWriteBack point⟩

/-! ## Post-assembly gravity seam → same-row U7 answer -/

def fixedRootPostAssemblyGravityDemandAt
    (point : BasePoint)
    (nonzero :
      (rootResidualAt FirstPostAssembly).gravity point ≠ 0) :
    rootU7.DemandAt
      (fixedRootPostAssemblyGravityObstructionAt point nonzero) :=
  rootResidualDemandAt .gravity point (PLift.up nonzero)

/-- The post-assembly gravity obstruction is answered by the existing living
root at its exact temporal visit; no target or disposition is supplied. -/
def fixedRootPostAssemblyGravityAnswerAndNextAt
    (point : BasePoint)
    (nonzero :
      (rootResidualAt FirstPostAssembly).gravity point ≠ 0) :
    SourceNativeRootResidualAnswerAndNextAt afterAssemblyTemporalVisit
      (fixedRootPostAssemblyGravityObstructionAt point nonzero)
      afterAssemblyCausalEntryAuthority :=
  .generated afterAssemblyTemporalVisit
    (fixedRootPostAssemblyGravityObstructionAt point nonzero)
    afterAssemblyCausalEntryAuthority

/-- A nonzero post-assembly gravity seam generates its exact demand on the
existing row, while the same compiler-owned output has the exact dependent
whole-carrier reconstruction before the second assembly current is exposed.
The proof of nonzeroness selects the U7 answer but is not an input to the
physical writer. -/
theorem fixedRootPostAssemblyGravityDemand_generates_nextAssemblyWrite
    (point : BasePoint)
    (nonzero :
      (rootResidualAt FirstPostAssembly).gravity point ≠ 0) :
    (fixedRootPostAssemblyGravityDemandAt point nonzero).entry =
        rootLedgerEntry FirstPostAssembly ∧
      root.evolutionAt FirstPostAssembly =
        EvolutionAt.nativeWrite (rootActionAt FirstPostAssembly) ∧
      (root.evolutionAt FirstPostAssembly).nextCurrent? =
        some secondAssemblyCurrent ∧
      secondAssemblyCurrent.configuration =
        formNativeP286GaugeConstitutiveReadout Source
          (sourceActionGeneratedCartanECSynchronizedGravityTailGLOccurrence
            Source (rootActionAt FirstPostAssembly).p286Stage).finalActual ∧
      generatedDiracDualFormNativePointwiseActionJet
          Source
          (sourceActionGeneratedCartanECSynchronizedGravityTailGLOccurrence
            Source (rootActionAt FirstPostAssembly).p286Stage).finalActual
          point =
        pointwiseActionJetWithGravityTailSeam
          (generatedDiracDualFormNativePointwiseActionJet Source
            (cartanECSynchronizedGravityTailProfileContact
              Source (rootActionAt FirstPostAssembly).p286Stage point) 0)
          ((rootResidualAt FirstPostAssembly).gravity point) := by
  exact ⟨rfl, rfl, rfl, rfl,
    root_secondAssembly_gravityStage_actionJet_eq_residualWriteBack point⟩

/-- A nonzero origin curvature coordinate is already a nonzero projection of
the exact assembly row.  It therefore uses the same registered demand and
compiler-owned next write; no settlement of the row's other coordinates is
assumed here. -/
theorem firstAssemblyOriginGravityCurvature_generates_nextGravityWrite
    (nonzero :
      ((rootResidualAt FirstAssembly).assembly 0).gravityCurvature ≠ 0) :
    let obstruction :=
      fixedRootAssemblyOriginGravityCurvatureObstructionAt nonzero
    let demand := rootU7.generateDemand obstruction
    demand.entry = rootLedgerEntry FirstAssembly ∧
      root.evolutionAt FirstAssembly =
        EvolutionAt.nativeWrite (rootActionAt FirstAssembly) ∧
      (root.evolutionAt FirstAssembly).nextCurrent? =
        some FirstPostAssembly := by
  exact ⟨rfl, rfl, rfl⟩

end
end StageNineDiracDualFormNativeFixedP506CartanECConstraintCauchyGravityTailRootU7AnswerNext
end PhysicsCore
end SaturationMonoid
