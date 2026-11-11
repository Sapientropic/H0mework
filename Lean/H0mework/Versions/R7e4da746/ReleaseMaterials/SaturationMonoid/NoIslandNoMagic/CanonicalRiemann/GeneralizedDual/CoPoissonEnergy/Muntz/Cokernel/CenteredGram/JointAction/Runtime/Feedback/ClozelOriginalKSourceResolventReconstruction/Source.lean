import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Material.Calculation.ClozelOriginalKReturnJordanSourceData
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKSourceResolventReconstruction.Resolvent
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKSourceResolventReconstruction.Uniqueness
import H0mework.Versions.R7e4da746.Arithmetic.RieszSourceKernel.Generated
import H0mework.Versions.R7e4da746.Arithmetic.RieszFiniteSource.FourierEdge
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCompactAdjointRSource.Source

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 800000

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKSourceResolventReconstruction
open Complex MeasureTheory Set Filter BurnolPhysicalState
open OriginalRieszSource OriginalRieszFiniteSource
open scoped Topology InnerProductSpace FourierTransform
noncomputable section

theorem sourceResolvent_euler (coordinate : BurnolCompletedMellinCoordinate) (value : BurnolL2) :
    GapEuler.euler (sourceResolvent coordinate value : TemperedDistribution ℝ ℂ) +
      sourceRate coordinate • (sourceResolvent coordinate value : TemperedDistribution ℝ ℂ) =
        -(2 : ℂ) • (value : TemperedDistribution ℝ ℂ) := by
  have right : 1/4 < (star coordinate.value/2).re := by
    rw [Complex.div_re]
    norm_num
    linarith [coordinate.rightHalf]
  have inverse := full_R_euler (star coordinate.value/2) right value
  have coefficient : 2*(star coordinate.value/2)-1/2 = sourceRate coordinate := by
    unfold sourceRate
    ring
  simpa only [sourceResolvent,coefficient] using inverse

/-- Inverse Fourier keeps the exact full-L² scope; no unqualified F²=id is used. -/
theorem sourceResolvent_fourier_adjoint (coordinate : BurnolCompletedMellinCoordinate) (value : BurnolL2) :
    sourceResolvent coordinate value =
      fourierL2.symm (FiniteMobiusResolventFlux.Rplus (star (coordinate.value/2)) (fourierL2 value)) := by
  have right : 1/4 < (star coordinate.value/2).re := by
    rw [Complex.div_re]
    norm_num
    linarith [coordinate.rightHalf]
  apply fourierL2.injective
  rw [fourierL2.apply_symm_apply]
  simpa only [sourceResolvent,star_div₀,star_ofNat] using
    FiniteMobiusResolventFlux.fourier_R (star coordinate.value/2) right value

/-- The direction is paid by the original R adjoint action, rather than parameter coincidence. -/
theorem sourceResolvent_actual_adjoint_read (coordinate : BurnolCompletedMellinCoordinate)
    (value test : BurnolL2) :
    inner ℂ (fourierL2 (sourceResolvent coordinate value)) test =
      inner ℂ (fourierL2 value) (burnolDirectRightResolvent (coordinate.value/2) test) := by
  have right : 1/4 < (coordinate.value/2).re := by
    rw [Complex.div_re]
    norm_num
    linarith [coordinate.rightHalf]
  rw [sourceResolvent_fourier_adjoint,fourierL2.apply_symm_apply]
  exact (OriginalKCompactAdjointRSource.actual_original_R_adjoint
    (coordinate.value/2) right (fourierL2 value) test).symm

theorem sourceY0_euler (coordinate : BurnolCompletedMellinCoordinate) :
    GapEuler.euler (sourceY0 coordinate : TemperedDistribution ℝ ℂ) +
      sourceRate coordinate • (sourceY0 coordinate : TemperedDistribution ℝ ℂ) = Response.Psi := by
  have inverse := sourceResolvent_euler coordinate (fourierL2 Response.wholeU - Response.wholeV)
  have edge := edgePrimitive_euler coordinate
  have sourceSplit :
      ((fourierL2 Response.wholeU - Response.wholeV : BurnolL2) : TemperedDistribution ℝ ℂ) =
        (fourierL2 Response.wholeU : TemperedDistribution ℝ ℂ) -
          (Response.wholeV : TemperedDistribution ℝ ℂ) :=
    (Lp.toTemperedDistributionCLM ℂ volume 2).map_sub _ _
  rw [sourceSplit] at inverse
  change GapEuler.euler (Lp.toTemperedDistributionCLM ℂ volume 2 (sourceY0 coordinate)) +
    sourceRate coordinate • (Lp.toTemperedDistributionCLM ℂ volume 2 (sourceY0 coordinate)) = _
  simp only [sourceY0,map_sub,map_smul,Lp.toTemperedDistributionCLM_apply]
  unfold sourceRate at *
  rw [Response.Psi, Lp.fourier_toTemperedDistribution_eq]
  change _ = (fourierL2 Response.wholeU : TemperedDistribution ℝ ℂ) -
    (Response.wholeV : TemperedDistribution ℝ ℂ) - GapEuler.edge (1/4)
  linear_combination (norm := module) -(1/2 : ℂ) • inverse - edge

theorem sourceY1_euler (coordinate : BurnolCompletedMellinCoordinate) :
    GapEuler.euler (sourceY1 coordinate : TemperedDistribution ℝ ℂ) +
      sourceRate coordinate • (sourceY1 coordinate : TemperedDistribution ℝ ℂ) =
        FourierTransform.fourier Response.Psi := by
  have inverse := sourceResolvent_euler coordinate (Response.wholeU - fourierL2 Response.wholeV)
  have primitive := sourceResolvent_euler coordinate (fourierPrimitive coordinate)
  have edge := fourierPrimitive_euler coordinate
  have sourceSplit :
      ((Response.wholeU - fourierL2 Response.wholeV : BurnolL2) : TemperedDistribution ℝ ℂ) =
        (Response.wholeU : TemperedDistribution ℝ ℂ) -
          (fourierL2 Response.wholeV : TemperedDistribution ℝ ℂ) :=
    (Lp.toTemperedDistributionCLM ℂ volume 2).map_sub _ _
  rw [sourceSplit] at inverse
  change GapEuler.euler (Lp.toTemperedDistributionCLM ℂ volume 2 (sourceY1 coordinate)) +
    sourceRate coordinate • (Lp.toTemperedDistributionCLM ℂ volume 2 (sourceY1 coordinate)) = _
  simp only [sourceY1,map_add,map_smul,Lp.toTemperedDistributionCLM_apply]
  unfold sourceRate at *
  rw [Response.Psi_fourier, Lp.fourier_toTemperedDistribution_eq]
  change _ = (Response.wholeU : TemperedDistribution ℝ ℂ) -
    (fourierL2 Response.wholeV : TemperedDistribution ℝ ℂ) - FourierTransform.fourier (GapEuler.edge (1/4))
  linear_combination (norm := module) -(1/2 : ℂ) • inverse +
    (star coordinate.value-1/2) • primitive + edge

theorem generatedK_euler (coordinate : BurnolCompletedMellinCoordinate) :
    GapEuler.euler (generatedK coordinate : TemperedDistribution ℝ ℂ) +
      sourceRate coordinate • (generatedK coordinate : TemperedDistribution ℝ ℂ) =
        Kernel.A coordinate • Response.Psi + Kernel.beta coordinate • FourierTransform.fourier Response.Psi := by
  have first := sourceY0_euler coordinate
  have second := sourceY1_euler coordinate
  change GapEuler.euler (Lp.toTemperedDistributionCLM ℂ volume 2 (generatedK coordinate)) +
    sourceRate coordinate • (Lp.toTemperedDistributionCLM ℂ volume 2 (generatedK coordinate)) = _
  simp only [generatedK,map_add,map_smul,Lp.toTemperedDistributionCLM_apply]
  linear_combination (norm := module) Kernel.A coordinate • first + Kernel.beta coordinate • second

theorem generatedK_eq_original (coordinate : BurnolCompletedMellinCoordinate) :
    generatedK coordinate = (burnolCompletedMellinRieszVector coordinate : BurnolL2) := by
  have generated := generatedK_euler coordinate
  have original := Kernel.original_kernel_euler coordinate
  have homogeneous : GapEuler.euler
      ((generatedK coordinate - (burnolCompletedMellinRieszVector coordinate : BurnolL2) : BurnolL2) : TemperedDistribution ℝ ℂ) +
      sourceRate coordinate •
        ((generatedK coordinate - (burnolCompletedMellinRieszVector coordinate : BurnolL2) : BurnolL2) : TemperedDistribution ℝ ℂ) = 0 := by
    change GapEuler.euler (Lp.toTemperedDistributionCLM ℂ volume 2
      (generatedK coordinate - (burnolCompletedMellinRieszVector coordinate : BurnolL2))) +
      sourceRate coordinate • (Lp.toTemperedDistributionCLM ℂ volume 2
        (generatedK coordinate - (burnolCompletedMellinRieszVector coordinate : BurnolL2))) = 0
    simp only [map_sub,Lp.toTemperedDistributionCLM_apply]
    unfold sourceRate at *
    linear_combination (norm := module) generated - original
  have positive : 0 < (sourceRate coordinate).re := by
    unfold sourceRate
    simp only [Complex.sub_re,Complex.star_def,Complex.conj_re]
    norm_num
    linarith [coordinate.rightHalf]
  exact sub_eq_zero.mp (homogeneous_L2_unique (sourceRate coordinate) positive _ homogeneous)

end
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKSourceResolventReconstruction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
