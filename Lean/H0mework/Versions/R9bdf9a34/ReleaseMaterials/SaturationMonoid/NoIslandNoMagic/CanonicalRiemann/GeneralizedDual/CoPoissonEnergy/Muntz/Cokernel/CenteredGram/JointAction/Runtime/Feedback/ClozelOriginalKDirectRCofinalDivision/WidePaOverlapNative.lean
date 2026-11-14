import H0mework.Versions.R9bdf9a34.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKDirectRCofinalDivision.WidePaOverlap

set_option autoImplicit false
set_option Elab.async false
set_option pp.deepTerms.threshold 25
set_option maxHeartbeats 160000

noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKDirectRCofinalDivision
namespace WideResidualReturn

open BurnolPhysicalState RootInquiryCompletion SourceOperationEffects SourceOperationExecution
open RootGeneratedDebtActivationJointSource.OwnerFree
open OriginalKFiniteOrderRelease.PositionGapCayley
open HilbertInventory.SecondConductorStock.SingleSlot
open OriginalKFiniteOrderRelease.PositionGapCayley.OutsideLogRank.ParameterSource.FixedRead.ResidualProbe
open OriginalKCrossParameterRAdjointSource.CayleyEnergySource

open private readField from H0mework.Versions.R9bdf9a34.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKDirectRCofinalDivision.WideResidualPaReturn
attribute [local instance] HilbertInventory.SecondConductorStock.SingleSlot.wideInner
attribute [local instance] DivisionEffectPrice.wideNormed

namespace PaOverlap

private inductive Stage
  | graphs | blend | write

private abbrev Bank := Wide × Wide × Wide
private abbrev Blend := Wide × BurnolPaAmbientCarrier
private abbrev Output := Wide × BurnolPaAmbientCarrier × BurnolPaAmbientCarrier

@[reducible] private def Value : Stage → Type
  | .graphs => Bank
  | .blend => Blend
  | .write => Output

private instance group (stage : Stage) : AddCommGroup (Value stage) := by
  cases stage <;> exact inferInstanceAs (AddCommGroup _)

private abbrev Var (_ : Stage) := Bool

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n : Nat, observation.coordinate = -2*(n+1))
variable (half : OriginalKCombCalculation.Half observation) (depth ordinal : Nat)

local notation "c" => burnolDivisionZeroCompletedMellinCoordinate observation half.down
local notation "δ" => (sourceDamping c : ℂ)
local notation "response" => adjointReturnMap observation nontrivial half
local notation "source" => paid observation nontrivial half depth
local notation "returns" => paReturn observation nontrivial half depth
local notation "gap" => graphOverlap observation nontrivial half depth ordinal
local notation "authority" => OriginalKDirectRCofinalCalculatedSource.calculationRoot observation nontrivial half depth ordinal
local notation "origin" => OriginalKDirectRCofinalCalculatedSource.calculationCurrent observation nontrivial half depth ordinal

private def readBefore : Bank →+ Blend :=
  let current := (AddMonoidHom.fst Wide Wide).comp (AddMonoidHom.snd Wide (Wide × Wide))
  let written := (AddMonoidHom.snd Wide Wide).comp (AddMonoidHom.snd Wide (Wide × Wide))
  (-written).prod ((response).toAddMonoidHom.comp current)

private def readAfter : Bank →+ Blend :=
  let current := (AddMonoidHom.fst Wide Wide).comp (AddMonoidHom.snd Wide (Wide × Wide))
  current.prod ((((δ • response) : Wide →L[ℂ] BurnolPaAmbientCarrier).toAddMonoidHom).comp current)

private def write : Blend →+ Output :=
  let stock := AddMonoidHom.fst Wide BurnolPaAmbientCarrier
  let total := AddMonoidHom.snd Wide BurnolPaAmbientCarrier
  let correction := ((δ • response : Wide →L[ℂ] BurnolPaAmbientCarrier).toAddMonoidHom).comp stock
  stock.prod (total.prod (total - correction))

private def environment (n m : Nat) : Env Value Var
  | .graphs, false => source ordinal n m
  | .graphs, true => source (ordinal+1) n m
  | .blend, _ => 0
  | .write, _ => 0

private def program : Expr Value Var Stage.write :=
  .linear (s := Stage.blend) (t := Stage.write) (write observation nontrivial half)
    (.add (.linear (s := Stage.graphs) (t := Stage.blend) (readBefore observation nontrivial half) (.var false))
      (.linear (s := Stage.graphs) (t := Stage.blend) (readAfter observation nontrivial half) (.var true)))

/-- The original current consumes both exact paid graph banks with separate variable addresses. -/
def reader (n m : Nat)
    (_actual : (authority).toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt origin) :
    Raw (Value := Value) (Var := Var) (sort := Stage.write) :=
  ⟨environment observation nontrivial half depth ordinal n m, program observation nontrivial half⟩

local notation "read" => reader observation nontrivial half depth ordinal

def output (n m : Nat) : Output := Eval.value authority origin (read n m)

attribute [local irreducible] paid in
theorem paid_overlap_source (n m : Nat) :
    output observation nontrivial half depth ordinal n m =
      (gap n m, returns ordinal n m + δ • returns (ordinal+1) n m,
        (returns ordinal n m + δ • returns (ordinal+1) n m) - δ • response (gap n m)) := by
  let before := source ordinal n m
  let after := source (ordinal+1) n m
  let measured : Wide := after.2.1-before.2.2
  let merged := response before.2.1 + δ • response after.2.1
  let bank := -before.2.2+after.2.1
  have same : bank = measured := neg_add_eq_sub _ _
  have performed : output observation nontrivial half depth ordinal n m =
      (program observation nontrivial half).eval (environment observation nontrivial half depth ordinal n m) :=
    Eval.value_source authority origin (read n m)
  have operation : (program observation nontrivial half).eval
      (environment observation nontrivial half depth ordinal n m) =
      (bank,merged,merged-δ • response bank) := rfl
  have computed := performed.trans (operation.trans
    (congrArg (fun x : Wide => (x,merged,merged-δ • response x)) same))
  have left := pa_return_map observation nontrivial half depth ordinal n m
  have right := pa_return_map observation nontrivial half depth (ordinal+1) n m
  have together : returns ordinal n m + δ • returns (ordinal+1) n m = merged :=
    congrArg₂ (fun a b : BurnolPaAmbientCarrier => a+δ • b) left right
  exact computed.trans (congrArg (fun x : BurnolPaAmbientCarrier =>
    (gap n m,x,x-δ • response (gap n m))) together.symm)

theorem paid_steps (n m : Nat) : (Eval.trace authority origin (read n m)).length = 6 :=
  (Eval.paid_history authority origin (read n m)).trans (by rfl)

theorem paid_direct_return (n m : Nat) :
    (output observation nontrivial half depth ordinal n m).2.2 =
      directReturnMap c (readField (source ordinal n m).2.1) := by
  have computed := congrArg (fun x : Output => x.2.2)
    (paid_overlap_source observation nontrivial half depth ordinal n m)
  have direct := two_paid_pa_returns observation nontrivial half depth ordinal n m
  let a := directReturnMap c (readField (source ordinal n m).2.1)
  let correction := δ • response (gap n m)
  exact computed.trans ((congrArg (fun x : BurnolPaAmbientCarrier => x-correction) direct).trans
    (add_sub_cancel_right a correction))

end PaOverlap
end WideResidualReturn
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKDirectRCofinalDivision
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
