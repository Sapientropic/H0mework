import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.ReverseCoreJumpMean
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.CompleteContact
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKExteriorCoPoissonAction.BCotest
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalCompleteCountedSource
open Complex Filter MeasureTheory Set BurnolPhysicalState
open OriginalRieszSource OriginalRieszSourceGreen OriginalRieszFiniteColumns
open OriginalRieszFinitePairing
open OriginalRieszFinitePairing.CoPoisson OriginalRieszFinitePairing.CoPoisson.Ward
open OriginalKSourceGramAction OriginalKSourceResolventReconstruction OriginalKCoefficientBFiniteAction
open OriginalKElementaryArithmeticAction OriginalKExteriorCoPoissonAction
open OriginalKSourceFiniteUpdate.OriginalBFiniteAction OriginalReverseCoreJumpMean OriginalFullLossRAction
open scoped InnerProductSpace Topology
local notation "F" => fourierL2
local notation "barC" => OriginalPrimitiveRankBalance.conjugateCoordinate

open private reverse_mean_value K_constant_read
  from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.CompleteContact
open private gamma
  from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.UnitRProgram

/-- The complete difference consumes the existing Volterra source price and both original unit contacts. -/
def calculatedDifference (c:BurnolCompletedMellinCoordinate) (h:ℝ) : ℂ :=
  coreCharacterDefect c h*((star c.value*GapEuler.gapMean (1/4) c/(1-star c.value))*
      ((1/2:ℂ)*star (positionMean c))-kernelSelfSource c)+positionLogPrice c h+
    (1/2:ℂ)*(centeringMean c h 0*inner ℂ (sourceKernel c) (F ConstantForward.value)-
      (OriginalKExteriorBCotest.sourcePrice c h+
        centeringMean c h 0*inner ℂ (sourceKernel c) (F ConstantDual.seed)))

private theorem elementary_self (c:BurnolCompletedMellinCoordinate) :
    inner ℂ (sourceKernel c) (elementarySource c)=kernelSelfSource c := by
  rw [sourceKernel_original]
  change inner ℂ (burnolCompletedMellinRieszVector c:BurnolL2) (gapState c)=_
  rw [gapState_eq_kernel_add_correction,inner_add_right,kernel_inner_sourceCorrection_zero,add_zero]
  exact original_kernel_self_source c

private theorem full_loss_source (c:BurnolCompletedMellinCoordinate) (h:ℝ) (nn:0≤h) :
    inner ℂ (sourceKernel c) (F (FullUnit.fullSource c h 0))=
      OriginalKExteriorBCotest.sourcePrice c h+
        centeringMean c h 0*inner ℂ (sourceKernel c) (F ConstantDual.seed) := by
  have actual:=OriginalKExteriorBCotest.original_full_B_loss_cotest c h nn
  rw [←sourceKernel_original c] at actual
  exact actual

private theorem difference_formula (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0)
    (h:ℝ) (nn:0≤h) :
    coreCharacterDefect c h*(reverseMean c zero*inner ℂ (sourceKernel c) ConstantDual.seed-
      inner ℂ (sourceKernel c) (elementarySource c))+positionLogPrice c h+
    (1/2:ℂ)*(centeringMean c h 0*inner ℂ (sourceKernel c) (F ConstantForward.value)-
      inner ℂ (sourceKernel c) (F (FullUnit.fullSource c h 0)))=calculatedDifference c h := by
  rw [reverse_mean_value c zero,K_constant_read c,elementary_self c,full_loss_source c h nn]
  rfl

/-- The two original counted cotests are read at their actual common source. -/
theorem counted_difference_source (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0)
    (h:ℝ) (nn:0≤h) (bound:h≤Real.log 2) :
    inner ℂ (KCountingGram.value c) (sourceCore c h)-
      inner ℂ (sourceKernel c) (sourceCore c h)=calculatedDifference c h :=
  (original_core_counted_difference c zero h nn bound).trans (difference_formula c zero h nn)

/-- This substitutes the generated difference inside the existing complete price programme. -/
theorem fixed_price_source (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0)
    (h:ℝ) (nn:0≤h) :
    fixedJumpProgrammePrice c zero h=
      let coefficient:=(c.value-star c.value)*gamma (barC c)
      let current:=completeCoreRCurrent c zero h
      (-star (Kernel.A c)*inner ℂ (regularForcing c 0) current-
        star (Kernel.beta c)*inner ℂ (regularForcing c 1) current+
        (2*c.value-1)*inner ℂ (sourceKernel c) current-
        2*coefficient*coreJumpPrice c h-(2*c.value-1)*currentJumpPrice c h+
          2*coefficient*calculatedDifference c h)/(2*coefficient) := by
  unfold fixedJumpProgrammePrice
  dsimp only
  rw [difference_formula c zero h nn]

end OriginalCompleteCountedSource
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
