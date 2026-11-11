import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKExteriorCoPoissonAction.BVolterra
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKExteriorCoPoissonAction.Action
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKSourceGramAction.Source
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKExteriorBCotest
open Complex Filter MeasureTheory Set BurnolPhysicalState
open OriginalKExteriorCoPoissonAction OriginalKExteriorBRVolterra
open OriginalKSourceGramAction OriginalKSourceResolventReconstruction
open OriginalKCoefficientBFiniteAction
open BurnolPhysicalState.OriginalRieszFinitePairing.CoPoisson.Ward
open scoped InnerProductSpace Topology

theorem bRRaw_memLp (c : BurnolCompletedMellinCoordinate) (h : ℝ) (nonnegative : 0 ≤ h) :
    MemLp (bRRaw c h) 2 volume :=
  (memLp_congr_ae (actual_b_R_source c h nonnegative)).mp
    (Lp.memLp (burnolDirectRightResolvent (c.value/2) (exteriorSource c h 0)))

theorem b_pairing_integrable (c : BurnolCompletedMellinCoordinate) (h : ℝ)
    (nonnegative : 0 ≤ h) (test : BurnolL2) :
    Integrable (fun x : ℝ => inner ℂ (test x) (bRRaw c h x)) volume := by
  apply (L2.integrable_inner (𝕜 := ℂ) test
    (burnolDirectRightResolvent (c.value/2) (exteriorSource c h 0))).congr
  filter_upwards [actual_b_R_source c h nonnegative] with x read
  rw [read]

theorem b_R_pairing (c : BurnolCompletedMellinCoordinate) (h : ℝ)
    (nonnegative : 0 ≤ h) (test : BurnolL2) :
    inner ℂ test (burnolDirectRightResolvent (c.value/2) (exteriorSource c h 0)) =
      ∫ x : ℝ, inner ℂ (test x) (bRRaw c h x) := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [actual_b_R_source c h nonnegative] with x read
  rw [read]

/-- Actual source forcing and both original jumps generate the unacted cotest. -/
def columnPrice (c : BurnolCompletedMellinCoordinate) (h : ℝ) (i : Fin 2) : ℂ :=
  -(1/2:ℂ) * (∫ x : ℝ, inner ℂ ((fourierL2 (regularForcing c i)) x) (bRRaw c h x)) +
    inner ℂ (fourierL2 (jumpColumns i)) (exteriorSource c h 0)

def sourcePrice (c : BurnolCompletedMellinCoordinate) (h : ℝ) : ℂ :=
  ∑ i : Fin 2, star (sourceCoefficients c i) * columnPrice c h i

theorem source_column_cotest (c : BurnolCompletedMellinCoordinate) (h : ℝ)
    (nonnegative : 0 ≤ h) (i : Fin 2) :
    inner ℂ (fourierL2 (sourceColumns c i)) (exteriorSource c h 0) = columnPrice c h i := by
  rw [sourceColumns_from_regular_resolvent]
  simp only [regularColumns,map_add,map_smul,inner_add_left,inner_smul_left,
    starRingEnd_apply,star_neg,star_div₀,star_ofNat,star_one]
  rw [sourceResolvent_actual_adjoint_read, b_R_pairing c h nonnegative]
  rfl

/-- This is F K against the original shell, not K against R of that shell. -/
theorem original_FK_source_cotest (c : BurnolCompletedMellinCoordinate) (h : ℝ)
    (nonnegative : 0 ≤ h) :
    inner ℂ (fourierL2 (burnolCompletedMellinRieszVector c : BurnolL2)) (exteriorSource c h 0) =
      sourcePrice c h := by
  have source : generatedK c = ∑ i : Fin 2, sourceCoefficients c i • sourceColumns c i := by
    simp only [generatedK,Fin.sum_univ_two,sourceCoefficients,sourceColumns,
      Matrix.cons_val_zero,Matrix.cons_val_one]
  rw [←generatedK_eq_original,source]
  simp only [map_sum,map_smul,sum_inner,inner_smul_left,starRingEnd_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [source_column_cotest c h nonnegative i]

theorem original_K_fourier_source_cotest (c : BurnolCompletedMellinCoordinate) (h : ℝ)
    (nonnegative : 0 ≤ h) :
    inner ℂ (burnolCompletedMellinRieszVector c : BurnolL2) (fourierL2 (exteriorSource c h 0)) =
      sourcePrice c h := by
  have twice : fourierL2 (fourierL2 (burnolCompletedMellinRieszVector c : BurnolL2)) =
      (burnolCompletedMellinRieszVector c : BurnolL2) := by
    rw [fourierL2_fourierL2]
    exact mem_evenL2ClosedFace_iff.mp (burnolCompletedMellinRieszVector c).property.2
  have pairing := fourierL2.inner_map_map
    (fourierL2 (burnolCompletedMellinRieszVector c : BurnolL2)) (exteriorSource c h 0)
  rw [twice] at pairing
  exact pairing.trans (original_FK_source_cotest c h nonnegative)

/-- The same source's complete loss retains its original m0 unit contact. -/
theorem original_full_B_loss_cotest (c : BurnolCompletedMellinCoordinate) (h : ℝ)
    (nonnegative : 0 ≤ h) :
    inner ℂ (burnolCompletedMellinRieszVector c : BurnolL2) (fourierL2 (FullUnit.fullSource c h 0)) =
      sourcePrice c h + centeringMean c h 0 *
        inner ℂ (burnolCompletedMellinRieszVector c : BurnolL2) (fourierL2 ConstantDual.seed) := by
  rw [FullUnit.full_source_inventory c h nonnegative 0,map_add,map_smul,inner_add_right,
    inner_smul_right,original_K_fourier_source_cotest c h nonnegative]

open private K_pa_read
  from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKExteriorCoPoissonAction.Action in
theorem original_arithmetic_core_cotest (c : BurnolCompletedMellinCoordinate)
    (zero : riemannZeta c.value = 0) (h : ℝ) (nonnegative : 0 ≤ h) (bounded : h ≤ Real.log 2) :
    inner ℂ (burnolCompletedMellinRieszVector c : BurnolL2) (arithmeticCoreRemainder c h) =
      inner ℂ (burnolCompletedMellinRieszVector c : BurnolL2)
        (OriginalKFixedBoundarySourceFibre.finiteBoundaryAction c h (elementarySource c)) - (1/2:ℂ) *
      (inner ℂ (burnolCompletedMellinRieszVector c : BurnolL2) (exteriorSource c h 1) -
        sourcePrice c h + centeringMean c h 1 *
          inner ℂ (burnolCompletedMellinRieszVector c : BurnolL2) ConstantDual.seed -
        centeringMean c h 0 *
          inner ℂ (burnolCompletedMellinRieszVector c : BurnolL2) (fourierL2 ConstantDual.seed)) := by
  have wave0 := K_pa_read c zero _
    (burnolOriginalPaInL2_fourier (exterior_wave_inPa c h nonnegative bounded 0))
  have wave1 := K_pa_read c zero _ (exterior_wave_inPa c h nonnegative bounded 1)
  rw [sourceKernel_original] at wave0 wave1
  simp only [arithmeticCoreRemainder,map_sub,inner_sub_right,inner_smul_right,inner_add_right]
  rw [wave0,wave1,original_K_fourier_source_cotest c h nonnegative]
  ring

/-- The original fixed residual now reads the generated B forcing price directly. -/
theorem original_fixedResidual_B_cotest (c : BurnolCompletedMellinCoordinate)
    (zero : riemannZeta c.value = 0) (h : ℝ) (nonnegative : 0 ≤ h) (bounded : h ≤ Real.log 2)
    (fixed : h = Real.log stageZeroSonineQ) :
    burnolPaFixedShiftResidual c zero =
      -(inner ℂ (burnolCompletedMellinRieszVector c : BurnolL2)
        (OriginalKFixedBoundarySourceFibre.finiteBoundaryAction c h (elementarySource c)) - (1/2:ℂ) *
      (inner ℂ (burnolCompletedMellinRieszVector c : BurnolL2) (exteriorSource c h 1) -
        sourcePrice c h + centeringMean c h 1 *
          inner ℂ (burnolCompletedMellinRieszVector c : BurnolL2) ConstantDual.seed -
        centeringMean c h 0 *
          inner ℂ (burnolCompletedMellinRieszVector c : BurnolL2) (fourierL2 ConstantDual.seed))) := by
  rw [original_fixedResidual_arithmetic_cotest c zero h nonnegative bounded fixed,
    sourceKernel_original, original_arithmetic_core_cotest c zero h nonnegative bounded]

end OriginalKExteriorBCotest
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
