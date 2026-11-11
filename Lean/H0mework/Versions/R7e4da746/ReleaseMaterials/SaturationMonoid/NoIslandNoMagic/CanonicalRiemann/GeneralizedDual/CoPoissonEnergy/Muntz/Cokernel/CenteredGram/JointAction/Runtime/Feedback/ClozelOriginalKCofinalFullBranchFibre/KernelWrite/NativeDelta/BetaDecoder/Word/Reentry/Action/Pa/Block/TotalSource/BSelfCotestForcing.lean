import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCofinalFullBranchFibre.KernelWrite.NativeDelta.BetaDecoder.Word.Reentry.Action.Pa.Block.TotalSource.BSelfResidualWrite
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKExteriorCoPoissonAction.SBCotest

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1400000
set_option maxRecDepth 6000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKCofinalFullBranchFibre.KernelWrite.NativeDelta.BetaDecoder.OriginalTotalSourceBSelfCotestForcing
open Complex BurnolPhysicalState SourceOperationEffects SourceOperationExecution
open OriginalKCoefficientBFiniteAction OriginalKExteriorCoPoissonAction
open BurnolPhysicalState.OriginalRieszFinitePairing.CoPoisson.Ward
open scoped InnerProductSpace

namespace W
export OriginalKCofinalFullBranchFibre.KernelWrite.NativeDelta.BetaDecoder.OriginalTotalSourceBSelfResidualWrite (originalRead)
namespace Residual
export OriginalKCofinalFullBranchFibre.KernelWrite.NativeDelta.BetaDecoder.OriginalTotalSourceBSelfResidualWrite.Residual (originalRead)
end Residual
namespace BS
export OriginalKCofinalFullBranchFibre.KernelWrite.NativeDelta.BetaDecoder.OriginalTotalSourceBSelfResidualWrite.BS (Value Var result)
end BS
end W
namespace M
export OriginalKCofinalFullBranchFibre.KernelWrite.NativeDelta.BetaDecoder.OriginalTotalSourceBSelfResidualWrite.Maternal (ResultAt)
end M
namespace Current
export OriginalKCofinalFullBranchFibre.KernelWrite.NativeDelta.BetaDecoder.OriginalTotalSourceBSelfResidualWrite.Current (selfCalculation)
end Current
namespace K
export OriginalKCofinalFullBranchFibre.KernelWrite.OriginalKInheritance (originalMaterial)
end K

def sourceResidual (observation : GeneratedRiemannZeroObservation)
    (nontrivial : ¬∃ n : Nat, observation.coordinate = -2*(n+1))
    (half : OriginalKCombCalculation.Half observation) : ℂ :=
  let c := OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half;
  let h := Real.log stageZeroSonineQ;
  -(inner ℂ (burnolCompletedMellinRieszVector c : BurnolL2)
      (OriginalKFixedBoundarySourceFibre.finiteBoundaryAction c h (elementarySource c)) - (1/2:ℂ) *
    (OriginalKExteriorSBCotest.sourcePrice c h - OriginalKExteriorBCotest.sourcePrice c h +
      centeringMean c h 1 * inner ℂ (burnolCompletedMellinRieszVector c : BurnolL2) ConstantDual.seed -
      centeringMean c h 0 * inner ℂ (burnolCompletedMellinRieszVector c : BurnolL2)
        (fourierL2 ConstantDual.seed)))

theorem source_equation (observation : GeneratedRiemannZeroObservation)
    (nontrivial : ¬∃ n : Nat, observation.coordinate = -2*(n+1))
    (half : OriginalKCombCalculation.Half observation) :
    burnolPaFixedShiftResidual
      (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) observation.mathlibZero =
      sourceResidual observation nontrivial half :=
  OriginalKExteriorSBCotest.original_fixedResidual_cotest observation nontrivial half

private theorem receipt_equation
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial : ¬∃ n : Nat, observation.coordinate = -2*(n+1))
    (half : OriginalKCombCalculation.Half observation) (depth : Nat)
    (maternal : type_of% (K.originalMaterial observation nontrivial half depth))
    (receipt : type_of% (((runtimeEffectRecognition observation nontrivial).effectLaw.eventVocabulary.emit maternal.1).effect.originalK.receiptAt half.down)) :
    receipt.1.fixedResidual = sourceResidual observation nontrivial half := by
  have same : receipt.1 = installedOriginalKReceiptAt observation nontrivial half.down :=
    receipt.2.trans (installedOriginalKReceiptAt_eq_source observation nontrivial half.down).symm
  rw [same, installedOriginalKReceiptAt_eq_source]
  exact source_equation observation nontrivial half

private def consumeWritten
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial : ¬∃ n : Nat, observation.coordinate = -2*(n+1))
    (half : OriginalKCombCalculation.Half observation) (depth : Nat)
    (maternal : type_of% (K.originalMaterial observation nontrivial half depth))
    (receipt : type_of% (((runtimeEffectRecognition observation nontrivial).effectLaw.eventVocabulary.emit maternal.1).effect.originalK.receiptAt half.down))
    (self : type_of% (Current.selfCalculation observation nontrivial half depth maternal))
    (source : self = W.BS.result observation nontrivial half maternal.1)
    (nonzero : self.2.2.1 ≠ 0)
    (value : self.2.2.1 = -receipt.1.fixedResidual • ConstantDual.seed)
    (written : M.ResultAt observation nontrivial half depth maternal receipt self source nonzero value) :=
  let price := receipt_equation observation nontrivial half depth maternal receipt
  let computedValue := value.trans
    (congrArg (fun z : ℂ => -z • ConstantDual.seed) price)
  let computedNext := written.1.2.2.2.trans
    (congrArg (fun z : ℂ => (Expr.const (-z • ConstantDual.seed) :
      Expr W.BS.Value W.BS.Var ())) price)
  PProd.mk price (PProd.mk computedValue computedNext)

attribute [local irreducible] M.ResultAt

local elab "forcingWritten% " writtenStx:term : term => do
  let written ← Lean.Elab.Term.elabTerm writtenStx none
  Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
  let written ← Lean.instantiateMVars written
  let indexed ← Lean.Meta.whnf (← Lean.Meta.inferType written)
  unless indexed.getAppFn.constName? == some ``M.ResultAt do
    throwError "expected the same original BSelf indexed whole-write carrier"
  let arguments := indexed.getAppArgs
  unless arguments.size == 10 do
    throwError "unexpected original BSelf whole-write source arity"
  let consumer ← Lean.Meta.mkConstWithFreshMVarLevels ``consumeWritten
  return Lean.mkAppN consumer (arguments ++ #[written])

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n : Nat, observation.coordinate = -2*(n+1))
variable (half : OriginalKCombCalculation.Half observation) (depth ordinal : Nat)

private def OriginalResult : Sort _ :=
  Σ' actual : type_of% (W.originalRead observation nontrivial half depth ordinal),
    PProd (actual = W.originalRead observation nontrivial half depth ordinal)
      (type_of% (forcingWritten% actual.2.2))

/-- The actual whole/next receives the equation of its own complete two-source cotest. -/
opaque originalRead : OriginalResult observation nontrivial half depth ordinal := by
  unfold OriginalResult
  let actual := W.originalRead observation nontrivial half depth ordinal
  exact ⟨actual, ⟨rfl, forcingWritten% actual.2.2⟩⟩

end OriginalKCofinalFullBranchFibre.KernelWrite.NativeDelta.BetaDecoder.OriginalTotalSourceBSelfCotestForcing
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
