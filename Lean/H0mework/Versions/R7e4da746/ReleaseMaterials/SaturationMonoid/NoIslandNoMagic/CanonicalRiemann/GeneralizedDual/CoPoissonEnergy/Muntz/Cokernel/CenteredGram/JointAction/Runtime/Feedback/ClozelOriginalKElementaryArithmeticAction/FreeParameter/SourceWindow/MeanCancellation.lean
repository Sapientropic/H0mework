import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.FreeParameter.SourceWindow.GammaBank
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.FreeParameter.SourceWindow.ConstantContact

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1200000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKElementaryArithmeticAction.FreeParameter.SourceWindow
open Complex BurnolPhysicalState
open OriginalRieszFinitePairing.CoPoisson.Ward OriginalKElementaryArithmeticAction.FreeParameter.UnitConsumer
open OriginalKElementaryArithmeticAction.FreeParameter.UnitSplice OriginalKElementaryArithmeticAction.FreeParameter.SourceWindow.ConstantContact
open scoped InnerProductSpace
local notation "q" => (1/4:ℝ)
local notation "barC" => OriginalPrimitiveRankBalance.conjugateCoordinate

/-- The full Unit mean bank and original constant contact cancel on the actual transformed-test window. -/
theorem actual_original_mean_constant_cancellation (c:BurnolCompletedMellinCoordinate)
    (m:Nat) (h:ℝ) (nonnegative:0≤h) (bound:q*Real.exp h<2*q) :
    gammaBank (barC c) m*fullMass c h-
      iteratedDeriv m constantCoefficient (star c.value)*inner ℂ (movedTest c h) ConstantDual.value=
      -(1/4:ℂ)*iteratedDeriv m constantCoefficient (star c.value)*inverseBandPrice c h := by
  rw [actual_original_constant_contact c h nonnegative bound]
  have generated:=actual_gamma_bank_cancellation (barC c) m
  change gammaBank (barC c) m+iteratedDeriv m constantCoefficient (star c.value)=0 at generated
  have paid:=congrArg (fun z:ℂ=>z*fullMass c h) generated
  linear_combination paid

end OriginalKElementaryArithmeticAction.FreeParameter.SourceWindow
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
