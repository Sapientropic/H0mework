import H0mework.Versions.R9bdf9a34.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKDirectRCofinalDivision.WideXiContactGram

set_option autoImplicit false
set_option Elab.async false
set_option pp.deepTerms.threshold 25
set_option maxHeartbeats 165000

noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKDirectRCofinalDivision
namespace WideResidualReturn.XiContact.JointGram

open BurnolPhysicalState RootInquiryCompletion SourceOperationEffects SourceOperationExecution
open RootGeneratedDebtActivationJointSource.OwnerFree
open OriginalKFiniteOrderRelease.PositionGapCayley
open HilbertInventory HilbertInventory.SecondConductorStock.SingleSlot
open OutsideLogRank.ParameterSource.FixedRead.ResidualProbe
open scoped InnerProductSpace

attribute [local instance] HilbertInventory.SecondConductorStock.SingleSlot.wideInner

open private Boundary boundaryMap from H0mework.Versions.R9bdf9a34.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKDirectRCofinalDivision.WideXiBoundaryNative
open private readField from H0mework.Versions.R9bdf9a34.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKDirectRCofinalDivision.WideResidualPaReturn

private inductive Stage
  | births | prices | contact | graph | settled

private abbrev Births := (BurnolL2 × BurnolL2) × (BurnolL2 × BurnolL2)
private abbrev Graphs := Wide × Wide
private abbrev Settlement := Graphs × Boundary × BurnolPaAmbientCarrier

@[reducible] private def Value (S : Submodule ℂ Wide) (n : Nat) : Stage → Type
  | .births => Births
  | .prices => JointBank n
  | .contact => S
  | .graph => S × Wide
  | .settled => Settlement

private instance group (S : Submodule ℂ Wide) (n : Nat) (stage : Stage) :
    AddCommGroup (Value S n stage) := by
  cases stage <;> exact inferInstance

private abbrev Var (_ : Stage) := Unit

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n : Nat, observation.coordinate = -2*(n+1))
variable (half : OriginalKCombCalculation.Half observation) (depth ordinal : Nat)

local notation "c" => burnolDivisionZeroCompletedMellinCoordinate observation half.down
local notation "a" => OriginalPrimitiveRankBalance.conjugateCoordinate c
local notation "degree" => generatedRiemannXiZeroOrder ActualAnalyticOwner observation.coordinate
local notation "S" => contact a degree
local notation "A" => advanceWide c observation.mathlibZero
local notation "birth" => OriginalKCombFirstFullSourceDynamics.input observation nontrivial half depth
local notation "authority" => OriginalKDirectRCofinalCalculatedSource.calculationRoot observation nontrivial half depth ordinal
local notation "origin" => OriginalKDirectRCofinalCalculatedSource.calculationCurrent observation nontrivial half depth ordinal
local notation "fitted" => fit observation nontrivial half depth ordinal

private def scan (n : Nat) : Births →+ JointBank n :=
  let slot := AddMonoidHom.fst BurnolL2 BurnolL2
  let left := slot.comp (AddMonoidHom.fst (BurnolL2 × BurnolL2) (BurnolL2 × BurnolL2))
  let right := slot.comp (AddMonoidHom.snd (BurnolL2 × BurnolL2) (BurnolL2 × BurnolL2))
  (bankMap observation nontrivial half depth n).toAddMonoidHom.comp (left.prod right)

private def writeGraphs : ↥S →+ (↥S × Wide) :=
  (AddMonoidHom.id ↥S).prod ((A).comp (S).subtypeL).toAddMonoidHom

private def settle : (↥S × Wide) →+ Settlement :=
  let current := ContinuousLinearMap.fst ℂ ↥S Wide
  let before := (S).subtypeL.comp current
  let after := ContinuousLinearMap.snd ℂ ↥S Wide
  let boundary := (boundaryMap a).comp ((terminalPositionMap observation half).comp current)
  let includePa := (evenBurnolClosedFace burnolUnscaledCommonGapRadius).toSubmodule.subtypeL
  let readBefore := Pa.E.comp (readField.comp before)
  let compressed := Pa.E.comp ((burnolDirectRightResolventCLM c).comp (includePa.comp readBefore))
  let direct := Pa.E.comp (readField.comp after) - compressed
  ((before.prod after).prod (boundary.prod direct)).toAddMonoidHom

private def environment (n : Nat) : Env (Value S n) Var
  | .births, _ => (birth ordinal, birth (ordinal+1))
  | .prices, _ => 0
  | .contact, _ => 0
  | .graph, _ => 0
  | .settled, _ => 0

private def program (n : Nat) : Expr (Value S n) Var Stage.settled :=
  .linear (s := Stage.graph) (t := Stage.settled) (settle observation half)
    (.linear (s := Stage.contact) (t := Stage.graph) (writeGraphs observation half)
      (.linear (s := Stage.prices) (t := Stage.contact) (recover observation nontrivial half depth n).toAddMonoidHom
        (.linear (s := Stage.births) (t := Stage.prices) (scan observation nontrivial half depth n) (.var ()))))

/-- Both actual complete birth banks precede the common Gram inverse and the literal original R letter. -/
def reader (n : Nat)
    (_ : (authority).toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt origin) :
    Raw (Value := Value S n) (Var := Var) (sort := Stage.settled) :=
  ⟨environment observation nontrivial half depth ordinal n, program observation nontrivial half depth n⟩

local notation "read" => reader observation nontrivial half depth ordinal

def output (n : Nat) : Settlement := Eval.value authority origin (read n)

theorem paid_source (n : Nat) :
    let x := fitted n
    let y := A (x : Wide)
    output observation nontrivial half depth ordinal n =
      (((x : Wide), y),
        boundaryMap a (terminalPosition observation half x),
        Pa.E (readField y) - Pa.E ((burnolDirectRightResolventCLM c)
          (Pa.E (readField (x : Wide)) : BurnolL2))) := by
  let x := fitted n
  let y := A (x : Wide)
  let value := Pa.E (readField y) - Pa.E ((burnolDirectRightResolventCLM c)
    (Pa.E (readField (x : Wide)) : BurnolL2))
  have evaluated : output observation nontrivial half depth ordinal n =
      (((x : Wide), y), boundaryMap a (terminalPositionMap observation half x), value) :=
    Eval.value_source authority origin (read n)
  exact evaluated.trans (congrArg (fun v : PositionField => (((x : Wide), y), boundaryMap a v, value))
    (terminal_map_source observation half x))

theorem paid_steps (n : Nat) : (Eval.trace authority origin (read n)).length = 5 :=
  (Eval.paid_history authority origin (read n)).trans (by rfl)

end WideResidualReturn.XiContact.JointGram
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKDirectRCofinalDivision
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
