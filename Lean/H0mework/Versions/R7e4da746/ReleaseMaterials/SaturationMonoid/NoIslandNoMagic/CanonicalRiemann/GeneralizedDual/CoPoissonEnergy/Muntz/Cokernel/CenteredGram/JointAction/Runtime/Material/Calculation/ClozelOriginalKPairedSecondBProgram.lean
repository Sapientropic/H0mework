import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Material.Calculation.ClozelOriginalKSecondBContactProgram
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKPairedBEulerJunctionSource.BandFullStockAction

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1200000
set_option pp.deepTerms.threshold 24
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalPairedSecondBProgram
open BurnolPhysicalState SourceOperationEffects SourceOperationExecution OriginalRieszSource
namespace Prog
export OriginalKPaNativePortSourceCalculation (Value Var E)
end Prog
namespace Price
export OriginalConstantFourierPriceMath (embed read scalarLift scalarRead scalar_lift)
end Price
namespace Gamma
export OriginalWholeDebtRJointMobiusContactPsiPriceSource (nativeGamma)
end Gamma
open private secondMap second_map_source from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKPairedBEulerJunctionSource.BandFullStockAction
local notation "Hq"=>BurnolQuarterIntervalL2
local notation "M"=>BurnolQuarterMeanZeroCarrier
local notation "Eq"=>burnolQuarterZeroExtension
local notation "Rq"=>burnolQuarterRestriction
local notation "S"=>burnolMeanZeroTruncatedFourier
local notation "q"=>(1/4:ℝ)

def wholeB2 : BurnolL2 →L[ℂ] BurnolL2 := Price.embed.comp secondMap
def environment (paired:BurnolL2) : Env Prog.Value Prog.Var := fun _ _=>paired
private def lin (action:BurnolL2 →L[ℂ] BurnolL2) (body:Prog.E) : Prog.E :=
  .linear action.toLinearMap.toAddMonoidHom body
def b2Code : Prog.E := lin wholeB2 (.var (0:Fin 2))
def code (c:BurnolCompletedMellinCoordinate) : Prog.E :=
  lin (OriginalSecondBGammaProgram.operation c c) b2Code
theorem code_budget (c:BurnolCompletedMellinCoordinate) : remaining (code c)=3 := rfl
theorem code_eval (c:BurnolCompletedMellinCoordinate) (paired:BurnolL2) :
    (code c).eval (environment paired)=OriginalSecondBGammaProgram.operation c c (wholeB2 paired) := rfl

theorem wholeB2_source (paired:BurnolL2) :
    wholeB2 paired=Eq (burnolAmbientMeanZeroSecondCorrection paired:Hq) :=
  congrArg (fun value:M=>Eq (value:Hq)) (second_map_source paired)
theorem wholeB2_read (paired:BurnolL2) : Price.read (wholeB2 paired)=burnolAmbientMeanZeroSecondCorrection paired := by
  change Constructor.zeroMean (Rq (wholeB2 paired))=_
  rw [wholeB2_source,burnolQuarterRestriction_zeroExtension]
  apply Subtype.ext
  exact Submodule.starProjection_eq_self_iff.mpr (burnolAmbientMeanZeroSecondCorrection paired).property

theorem first_block (paired:BurnolL2) :
    burnolAmbientMeanZeroFirstCorrection paired+S (Price.read (wholeB2 paired))=
      burnolAmbientMeanZeroPosition paired := by
  rw [wholeB2_read]
  exact burnolMeanZeroBlock_first_equation (burnolAmbientMeanZeroBlockRhs paired)
theorem second_block (paired:BurnolL2) :
    S (burnolAmbientMeanZeroFirstCorrection paired)+Price.read (wholeB2 paired)=
      burnolAmbientMeanZeroFourier paired := by
  rw [wholeB2_read]
  exact burnolMeanZeroBlock_second_equation (burnolAmbientMeanZeroBlockRhs paired)

def positionInput (paired:BurnolL2) : Hq := Rq (burnolAmbientEvenPart paired)
def fourierInput (paired:BurnolL2) : Hq := Rq (fourierL2 (burnolAmbientEvenPart paired))
def positionMean (paired:BurnolL2) : ℂ := burnolQuarterMeanCoefficient (positionInput paired)
def fourierMean (paired:BurnolL2) : ℂ := burnolQuarterMeanCoefficient (fourierInput paired)
theorem first_full_block (paired:BurnolL2) :
    ((burnolAmbientMeanZeroFirstCorrection paired+S (Price.read (wholeB2 paired)):M):Hq)+
      positionMean paired • intervalConstant q=positionInput paired := by
  rw [first_block]
  change (Constructor.zeroMean (positionInput paired):Hq)+positionMean paired • intervalConstant q=_
  rw [Constructor.zeroMean_read]
  change positionInput paired-positionMean paired • intervalConstant q+positionMean paired • intervalConstant q=_
  module
theorem second_full_block (paired:BurnolL2) :
    ((S (burnolAmbientMeanZeroFirstCorrection paired)+Price.read (wholeB2 paired):M):Hq)+
      fourierMean paired • intervalConstant q=fourierInput paired := by
  rw [second_block]
  change (Constructor.zeroMean (fourierInput paired):Hq)+fourierMean paired • intervalConstant q=_
  rw [Constructor.zeroMean_read]
  change fourierInput paired-fourierMean paired • intervalConstant q+fourierMean paired • intervalConstant q=_
  module

theorem wholeB2_actual (c:BurnolCompletedMellinCoordinate) (paired:BurnolL2)
    (actual:paired=OriginalKPairedBEulerJunctionSource.sourceAction c) :
    wholeB2 paired=Eq (OriginalKPairedBEulerJunctionSource.sourceSecond c:Hq) :=
  (wholeB2_source paired).trans
    (congrArg (fun value:BurnolL2=>Eq (burnolAmbientMeanZeroSecondCorrection value:Hq)) actual)
theorem code_actual (c:BurnolCompletedMellinCoordinate) (paired:BurnolL2)
    (actual:paired=OriginalKPairedBEulerJunctionSource.sourceAction c) :
    (code c).eval (environment paired)=Price.scalarLift (Gamma.nativeGamma c c) :=
  (code_eval c paired).trans
    (OriginalSecondBGammaProgram.operation_actual c c (wholeB2 paired) (wholeB2_actual c paired actual))
theorem wholeB2_zero : wholeB2 0=0 := map_zero _

namespace Traced
variable (c:BurnolCompletedMellinCoordinate) {env:Env Prog.Value Prog.Var} {value:BurnolL2}
variable (actual:Trace env (code c) (.const value))
noncomputable def outer := Trace.splitLinear actual
noncomputable def inner := Trace.splitLinear (outer c actual).trace
noncomputable def b2Receipt : Trace.SourceReceipt actual b2Code :=
  ⟨(outer c actual).input,(outer c actual).trace,.linear (outer c actual) (.refl _)⟩
noncomputable def pairedReceipt : Trace.SourceReceipt actual (.var (0:Fin 2)) :=
  ⟨(inner c actual).input,(inner c actual).trace,
    .linear (outer c actual) (.linear (inner c actual) (.refl _))⟩
theorem paired_read : (pairedReceipt c actual).value=env () 0 := (pairedReceipt c actual).trace.sound.symm
theorem b2_read : (b2Receipt c actual).value=wholeB2 (env () 0) := (b2Receipt c actual).trace.sound.symm
end Traced
end OriginalPairedSecondBProgram
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
run_cmd Lean.modifyEnv fun env =>
  Lean.LibrarySuggestions.nameDenyListExt.addEntry env "OriginalPairedSecondBProgram"
