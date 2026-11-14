import H0mework.Versions.R9bdf9a34.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKDirectRCofinalDivision.WideXiBoundary
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKPairedBEulerJunctionSource.BandFullStockAction
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.QuarterCurrentSource

set_option autoImplicit false
set_option Elab.async false
set_option pp.deepTerms.threshold 25
set_option maxHeartbeats 170000

noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKDirectRCofinalDivision
namespace WideResidualReturn.XiContact

open BurnolPhysicalState RootInquiryCompletion SourceOperationEffects SourceOperationExecution
open RootGeneratedDebtActivationJointSource.OwnerFree
open OriginalKFiniteOrderRelease.PositionGapCayley
open HilbertInventory HilbertInventory.SecondConductorStock HilbertInventory.SecondConductorStock.SingleSlot
open OutsideLogRank.ParameterSource.FixedRead.ResidualProbe
open scoped InnerProductSpace

open private firstMap secondMap first_map_source second_map_source from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKPairedBEulerJunctionSource.BandFullStockAction

local notation "C" => OriginalPrimitiveRankBalance.conjugateCoordinate
local notation "P" => burnolEvenAmbientProjection
local notation "E" => Pa.E
local notation "Z" => BurnolQuarterMeanZeroCarrier
local notation "H" => BurnolPaAmbientCarrier

private abbrev Banks := (Wide × Wide × Wide) × (Wide × H × H)
private abbrev Branches := (Wide × Wide) × (Wide × H × H)
private abbrev Boundary := Z × BurnolL2 × (Z × Z) × (ℂ × ℂ) × (H × H)
private abbrev Material := Branches × Boundary

private def releaseMap (anchor : BurnolCompletedMellinCoordinate) : PositionField →L[ℂ] Z :=
  OriginalRieszSource.Constructor.zeroMean.comp (burnolQuarterRestriction.comp
    ((OriginalKCrossParameterRAdjointSource.CayleyEnergySource.sourceCayley anchor).adjoint.comp
      HilbertInventory.positionSpace.toSubmodule.subtypeL))

private def rawMap (anchor : BurnolCompletedMellinCoordinate) : PositionField →L[ℂ] BurnolL2 :=
  (OriginalKCrossParameterRAdjointSource.CayleyEnergySource.sourceCayley anchor).comp
    (burnolQuarterZeroExtension.comp (burnolQuarterMeanZeroClosedFace.toSubmodule.subtypeL.comp (releaseMap anchor)))

private def means : H →L[ℂ] (ℂ × ℂ) :=
  let mean := OriginalKFiniteOrderRelease.QuarterCurrentSource.quarterMean
  let read := mean.comp burnolQuarterRestriction
  let includePhysical := (evenBurnolClosedFace burnolUnscaledCommonGapRadius).toSubmodule.subtypeL
  (read.comp includePhysical).prod
    (read.comp (fourierL2.toContinuousLinearEquiv.toContinuousLinearMap.comp includePhysical))

private def boundaryMap (anchor : BurnolCompletedMellinCoordinate) : PositionField →L[ℂ] Boundary :=
  let raw := rawMap anchor
  let corrections := (firstMap.prod secondMap).comp raw
  let mean := means.comp ((P).comp raw)
  let physical := ((P).prod E).comp raw
  (releaseMap anchor).prod (raw.prod (corrections.prod (mean.prod physical)))

private theorem boundary_source (anchor : BurnolCompletedMellinCoordinate) (x : PositionField) :
    let raw := BoundaryQuarterRelease.raw anchor x
    (boundaryMap anchor x : Boundary) =
      (BoundaryQuarterRelease.release anchor x, raw,
        (burnolAmbientMeanZeroFirstCorrection raw, burnolAmbientMeanZeroSecondCorrection raw),
        (burnolQuarterMeanCoefficient (burnolQuarterRestriction (P raw : BurnolL2)),
          burnolQuarterMeanCoefficient (burnolQuarterRestriction (fourierL2 (P raw : BurnolL2)))),
        (P raw, E raw)) := by
  let raw := BoundaryQuarterRelease.raw anchor x
  change (BoundaryQuarterRelease.release anchor x, raw, (firstMap raw, secondMap raw),
    means (P raw), (P raw, E raw)) = _
  have mean (v : H) : means v =
      (burnolQuarterMeanCoefficient (burnolQuarterRestriction (v : BurnolL2)),
        burnolQuarterMeanCoefficient (burnolQuarterRestriction (fourierL2 (v : BurnolL2)))) :=
    Prod.ext (OriginalKFiniteOrderRelease.QuarterCurrentSource.quarterMean_read _)
      (OriginalKFiniteOrderRelease.QuarterCurrentSource.quarterMean_read _)
  rw [first_map_source, second_map_source, mean]

private inductive Stage
  | bank | contact | position | release

@[reducible] private def Value (anchor : BurnolCompletedMellinCoordinate) (n : Nat) : Stage → Type
  | .bank => Banks
  | .contact => Branches × ↥(contact anchor n)
  | .position => Branches × PositionField
  | .release => Material

private instance group (anchor : BurnolCompletedMellinCoordinate) (n : Nat) (stage : Stage) :
    AddCommGroup (Value anchor n stage) := by
  cases stage <;> exact inferInstance

private abbrev Var (_ : Stage) := Unit

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n : Nat, observation.coordinate = -2*(n+1))
variable (half : OriginalKCombCalculation.Half observation) (depth ordinal : Nat)

local notation "c" => burnolDivisionZeroCompletedMellinCoordinate observation half.down
local notation "a" => C c
local notation "degree" => generatedRiemannXiZeroOrder ActualAnalyticOwner observation.coordinate
local notation "authority" => OriginalKDirectRCofinalCalculatedSource.calculationRoot observation nontrivial half depth ordinal
local notation "origin" => OriginalKDirectRCofinalCalculatedSource.calculationCurrent observation nontrivial half depth ordinal
local notation "graphs" => paid observation nontrivial half depth ordinal
local notation "pa" => PaOverlap.output observation nontrivial half depth ordinal

private def split : Banks →+ Value a degree .contact :=
  let current := ((AddMonoidHom.fst Wide Wide).comp (AddMonoidHom.snd Wide (Wide × Wide))).comp
    (AddMonoidHom.fst (Wide × Wide × Wide) (Wide × H × H))
  let flow := AddMonoidHom.snd (Wide × Wide × Wide) (Wide × H × H)
  let keep := ((qualify a degree).toAddMonoidHom).comp current
  let rest := ((rejected a degree).toAddMonoidHom).comp current
  ((current.prod rest).prod flow).prod keep

private def act : Value a degree .contact →+ Value a degree .position :=
  let carry := AddMonoidHom.fst Branches ↥(contact a degree)
  let field := (terminalPositionMap observation half).toAddMonoidHom.comp
    (AddMonoidHom.snd Branches ↥(contact a degree))
  carry.prod field

private def write : Value a degree .position →+ Material :=
  let carry := AddMonoidHom.fst Branches PositionField
  let fields := ((boundaryMap a).toAddMonoidHom).comp (AddMonoidHom.snd Branches PositionField)
  carry.prod fields

private def input (n m : Nat) : Env (Value a degree) Var
  | .bank, _ => (graphs n m, pa n m)
  | .contact, _ => 0
  | .position, _ => 0
  | .release, _ => 0

private def program : Expr (Value a degree) Var Stage.release :=
  .linear (s := Stage.position) (t := Stage.release) (write observation half)
    (.linear (s := Stage.contact) (t := Stage.position) (act observation half)
      (.linear (s := Stage.bank) (t := Stage.contact) (split observation half) (.var ())))

/-- The same original current reads the exact settled graph and Pa overlap before writing the B columns. -/
def reader (n m : Nat)
    (_ : (authority).toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt origin) :
    Raw (Value := Value a degree) (Var := Var) (sort := Stage.release) :=
  ⟨input observation nontrivial half depth ordinal n m, program observation half⟩

local notation "read" => reader observation nontrivial half depth ordinal

def output (n m : Nat) : Material := Eval.value authority origin (read n m)

attribute [local irreducible] paid PaOverlap.output in
theorem paid_boundary_source (n m : Nat) :
    output observation nontrivial half depth ordinal n m =
      ((((graphs n m).2.1, rejected a degree (graphs n m).2.1), pa n m),
        boundaryMap a (terminalPosition observation half
          (paidQualified observation nontrivial half depth ordinal n m))) := by
  let p := paidQualified observation nontrivial half depth ordinal n m
  let retained : Branches := (((graphs n m).2.1, rejected a degree (graphs n m).2.1), pa n m)
  let raw := program observation half
  let bank := input observation nontrivial half depth ordinal n m
  have result : output observation nontrivial half depth ordinal n m = raw.eval bank :=
    Eval.value_source authority origin (read n m)
  have source : raw.eval bank = (retained, boundaryMap a (terminalPositionMap observation half p)) := rfl
  exact result.trans (source.trans
    (congrArg (fun x : PositionField => (retained, boundaryMap a x)) (terminal_map_source observation half p)))

theorem paid_boundary_steps (n m : Nat) : (Eval.trace authority origin (read n m)).length = 4 :=
  (Eval.paid_history authority origin (read n m)).trans (by rfl)

end WideResidualReturn.XiContact
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKDirectRCofinalDivision
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
