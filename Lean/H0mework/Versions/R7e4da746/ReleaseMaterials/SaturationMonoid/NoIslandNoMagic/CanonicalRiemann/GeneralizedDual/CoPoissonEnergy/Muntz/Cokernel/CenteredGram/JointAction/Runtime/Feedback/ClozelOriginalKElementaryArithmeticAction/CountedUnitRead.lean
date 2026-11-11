import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.FourierUnitPrice
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.CompleteCountedSource
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalCountedUnitRead
open Complex MeasureTheory Set BurnolPhysicalState
open OriginalRieszSource OriginalRieszFinitePairing
open OriginalRieszFinitePairing.CoPoisson OriginalRieszFinitePairing.CoPoisson.Ward
open OriginalKCoefficientBFiniteAction OriginalKElementaryArithmeticAction OriginalKExteriorCoPoissonAction
open OriginalFourierUnitPrice OriginalCompleteCountedSource
open scoped InnerProductSpace
local notation "q" => (1/4:ℝ)
local notation "F" => fourierL2

/-- The original Fourier source profile pays its quarter-unit contact with the actual mean. -/
theorem kernel_fourier_constant (c:BurnolCompletedMellinCoordinate) :
    inner ℂ (sourceKernel c) (F ConstantDual.seed)=(1/2:ℂ)*star (fourierMean c) := by
  rw [sourceKernel_original]
  have evenK:reflectL2 (burnolCompletedMellinRieszVector c:BurnolL2)=
      (burnolCompletedMellinRieszVector c:BurnolL2) :=
    mem_evenL2ClosedFace_iff.mp (burnolCompletedMellinRieszVector c).property.2
  have moved:=fourierL2.inner_map_map (F (burnolCompletedMellinRieszVector c:BurnolL2)) ConstantDual.seed
  rw [fourierL2_fourierL2,evenK] at moved
  rw [moved]
  have actual:(fun x:ℝ=>inner ℂ ((F (burnolCompletedMellinRieszVector c:BurnolL2):BurnolL2) x)
      (ConstantDual.seed x))=ᵐ[volume]
      (symmetricInterval q).indicator (fun _:ℝ=>star (fourierMean c)) := by
    filter_upwards [burnolRieszFourier_ae_raw c,ConstantDual.seed_coeFn] with x raw seed
    rw [seed,ConstantDual.seedRaw]
    by_cases inside:x∈symmetricInterval q
    · rw [if_pos (abs_le.mpr inside),indicator_of_mem inside,raw,fourier_raw,if_pos inside,add_zero]
      simp [RCLike.inner_apply]
    · rw [if_neg (fun hx=>inside (abs_le.mp hx)),indicator_of_notMem inside]
      simp
  rw [L2.inner_def,integral_congr_ae actual,integral_indicator (measurableSet_symmetricInterval q),integral_const]
  norm_num [symmetricInterval,real_smul]

/-- Both original unit contacts are read inside the existing complete counted difference. -/
theorem calculated_units (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0) (h:ℝ) :
    calculatedDifference c h=
      coreCharacterDefect c h*((star c.value*GapEuler.gapMean q c/(1-star c.value))*
        ((1/2:ℂ)*star (positionMean c))-kernelSelfSource c)+positionLogPrice c h-
        (1/2:ℂ)*(centeringMean c h 0*
          inner ℂ (sourceB c:BurnolQuarterIntervalL2) SmallScaleLog.logL2+
          OriginalKExteriorBCotest.sourcePrice c h+
          (centeringMean c h 0/2)*star (fourierMean c)) := by
  unfold calculatedDifference
  rw [kernel_fourier_unit c zero,kernel_fourier_constant c]
  ring

end OriginalCountedUnitRead
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
