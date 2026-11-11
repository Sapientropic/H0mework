import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCofinalFullBranchFibre.KernelWrite.NativeDelta.BetaDecoder.Word.Reentry.Action.Pa.Block.TotalSource.BSelfCotestForcing
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.NextEndpointProgramme

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1400000
set_option maxRecDepth 6000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKCofinalFullBranchFibre.KernelWrite.NativeDelta.BetaDecoder.OriginalTotalSourceBSelfRPrice
open Complex BurnolPhysicalState SourceOperationEffects SourceOperationExecution
open OriginalKCoefficientBFiniteAction OriginalKExteriorCoPoissonAction
open BurnolPhysicalState.OriginalRieszFinitePairing.CoPoisson.Ward

namespace Current
export OriginalKCofinalFullBranchFibre.KernelWrite.NativeDelta.BetaDecoder.OriginalTotalSourceBSelfCotestForcing
  (originalRead sourceResidual source_equation)
end Current
namespace BS
export OriginalKCofinalFullBranchFibre.KernelWrite.NativeDelta.BetaDecoder.OriginalTotalSourceBSelfCotestForcing.W.BS
  (Value Var result)
end BS
namespace M
export OriginalKCofinalFullBranchFibre.KernelWrite.NativeDelta.BetaDecoder.OriginalTotalSourceBSelfCotestForcing.M
  (ResultAt)
end M
namespace Self
export OriginalKCofinalFullBranchFibre.KernelWrite.NativeDelta.BetaDecoder.OriginalTotalSourceBSelfCotestForcing.Current
  (selfCalculation)
end Self
namespace K
export OriginalKCofinalFullBranchFibre.KernelWrite.NativeDelta.BetaDecoder.OriginalTotalSourceBSelfCotestForcing.K
  (originalMaterial)
end K
open private receipt_equation from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCofinalFullBranchFibre.KernelWrite.NativeDelta.BetaDecoder.Word.Reentry.Action.Pa.Block.TotalSource.BSelfCotestForcing

/-- The same source computes its original fixed-h R price before the receipt is read. -/
def sourceRPrice (observation : GeneratedRiemannZeroObservation)
    (nontrivial : ¬∃ n : Nat, observation.coordinate = -2*(n+1))
    (half : OriginalKCombCalculation.Half observation) : ℂ :=
  OriginalNextEndpointProgramme.programmePrice
    (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half)
    (Real.log stageZeroSonineQ)

theorem source_R_equation (observation : GeneratedRiemannZeroObservation)
    (nontrivial : ¬∃ n : Nat, observation.coordinate = -2*(n+1))
    (half : OriginalKCombCalculation.Half observation) :
    Current.sourceResidual observation nontrivial half = sourceRPrice observation nontrivial half :=
  (Current.source_equation observation nontrivial half).symm.trans
    (OriginalNextEndpointProgramme.original_fixedResidual_programme observation nontrivial half)

private def consumeWritten
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial : ¬∃ n : Nat, observation.coordinate = -2*(n+1))
    (half : OriginalKCombCalculation.Half observation) (depth : Nat)
    (maternal : type_of% (K.originalMaterial observation nontrivial half depth))
    (receipt : type_of% (((runtimeEffectRecognition observation nontrivial).effectLaw.eventVocabulary.emit maternal.1).effect.originalK.receiptAt half.down))
    (self : type_of% (Self.selfCalculation observation nontrivial half depth maternal))
    (source : self = BS.result observation nontrivial half maternal.1)
    (nonzero : self.2.2.1 ≠ 0)
    (value : self.2.2.1 = -receipt.1.fixedResidual • ConstantDual.seed)
    (written : M.ResultAt observation nontrivial half depth maternal receipt self source nonzero value) :=
  let price := (receipt_equation observation nontrivial half depth maternal receipt).trans
    (source_R_equation observation nontrivial half)
  let computedValue := value.trans
    (congrArg (fun z : ℂ => -z • ConstantDual.seed) price)
  let computedNext := written.1.2.2.2.trans
    (congrArg (fun z : ℂ => (Expr.const (-z • ConstantDual.seed) :
      Expr BS.Value BS.Var ())) price)
  PProd.mk price (PProd.mk computedValue computedNext)

attribute [local irreducible] M.ResultAt

local elab "rPriceWritten% " writtenStx:term : term => do
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
  Σ' current : type_of% (Current.originalRead observation nontrivial half depth ordinal),
    PProd (current = Current.originalRead observation nontrivial half depth ordinal)
      (type_of% (rPriceWritten% current.1.2.2))

/-- The computed full R price reaches the same written value and canonical next expression. -/
opaque originalRead : OriginalResult observation nontrivial half depth ordinal := by
  unfold OriginalResult
  let current := Current.originalRead observation nontrivial half depth ordinal
  exact ⟨current, ⟨rfl, rPriceWritten% current.1.2.2⟩⟩

end OriginalKCofinalFullBranchFibre.KernelWrite.NativeDelta.BetaDecoder.OriginalTotalSourceBSelfRPrice
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
