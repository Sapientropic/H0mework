import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Material.Calculation.ClozelOriginalKForcedInverseSourceCalculation
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Material.Calculation.ClozelOriginalKPaNativePortSourceCalculation
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.TruncatedFourier.Radius.Scaling.Variation.FiniteRank.Source.PriceChannels

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1200000
set_option pp.deepTerms.threshold 24
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalSecondBGammaProgram
open BurnolPhysicalState SourceOperationEffects SourceOperationExecution
namespace Prog
export OriginalKPaNativePortSourceCalculation (Value Var E)
end Prog
namespace Price
export OriginalConstantFourierPriceMath (scalarLift scalarRead scalar_lift)
end Price
namespace Gamma
export OriginalWholeDebtRJointMobiusContactPsiPriceSource (nativeGamma actual_native_gamma)
end Gamma
local notation "Eq"=>burnolQuarterZeroExtension
local notation "Hq"=>BurnolQuarterIntervalL2

def operation (c d:BurnolCompletedMellinCoordinate) : BurnolL2 →L[ℂ] BurnolL2 :=
  Price.scalarLift.comp
    ((-2*OriginalWholeDebtRAdjointContactSource.sigma c d) •
      OriginalKForcedInverseSourceCalculation.matrixRead d)
def environment (second:BurnolL2) : Env Prog.Value Prog.Var := fun _ _=>second
private def lin (action:BurnolL2 →L[ℂ] BurnolL2) (body:Prog.E) : Prog.E :=
  .linear action.toLinearMap.toAddMonoidHom body
def code (c d:BurnolCompletedMellinCoordinate) : Prog.E :=
  lin (operation c d) (.var (0:Fin 2))
theorem code_budget (c d:BurnolCompletedMellinCoordinate) : remaining (code c d)=2 := rfl
theorem code_eval (c d:BurnolCompletedMellinCoordinate) (second:BurnolL2) :
    (code c d).eval (environment second)=operation c d second := rfl

theorem operation_actual (c d:BurnolCompletedMellinCoordinate) (second:BurnolL2)
    (actual:second=Eq (OriginalKPairedBEulerJunctionSource.sourceSecond c:Hq)) :
    operation c d second=Price.scalarLift (Gamma.nativeGamma c d) := by
  change Price.scalarLift ((-2*OriginalWholeDebtRAdjointContactSource.sigma c d)*
    OriginalKForcedInverseSourceCalculation.matrixRead d second)=_
  rw [actual,OriginalKForcedInverseSourceCalculation.matrix_read_faithful,Gamma.actual_native_gamma]
  rfl

theorem code_actual (c d:BurnolCompletedMellinCoordinate) (second:BurnolL2)
    (actual:second=Eq (OriginalKPairedBEulerJunctionSource.sourceSecond c:Hq)) :
    (code c d).eval (environment second)=Price.scalarLift (Gamma.nativeGamma c d) :=
  (code_eval c d second).trans (operation_actual c d second actual)

theorem operation_zero (c d:BurnolCompletedMellinCoordinate) : operation c d 0=0 := map_zero _

namespace Traced
variable (c d:BurnolCompletedMellinCoordinate) {env:Env Prog.Value Prog.Var} {value:BurnolL2}
variable (actual:Trace env (code c d) (.const value))
noncomputable def outer := Trace.splitLinear actual
noncomputable def secondReceipt : Trace.SourceReceipt actual (.var (0:Fin 2)) :=
  ⟨(outer c d actual).input,(outer c d actual).trace,
    .linear (outer c d actual) (.refl _)⟩
theorem second_read : (secondReceipt c d actual).value=env () 0 :=
  (secondReceipt c d actual).trace.sound.symm
end Traced
end OriginalSecondBGammaProgram
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
run_cmd Lean.modifyEnv fun env =>
  Lean.LibrarySuggestions.nameDenyListExt.addEntry env "OriginalSecondBGammaProgram"
