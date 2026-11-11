import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKSourcePhysicalProjection.Gate
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCompactAdjointRSource.Source

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKFullAdjointSource
open Complex MeasureTheory Set
open BurnolPhysicalState BurnolPhysicalState.OriginalRieszSource
open OriginalKSourceResolventReconstruction OriginalKSourceGramAction
open OriginalRieszFinitePairing.CoPoisson.Ward
open scoped InnerProductSpace

def sourceAdjoint (coordinate : BurnolCompletedMellinCoordinate) (value : BurnolL2) : BurnolL2 :=
  FiniteMobiusResolventFlux.Rplus (star coordinate.value/2) value

def sourceAdjointRate (coordinate : BurnolCompletedMellinCoordinate) : ℂ := 2*star coordinate.value-1

/-- The full input-source field has no K, R K, residual, terminal or physical qualification constructor input. -/
def sourceAdjointField (coordinate : BurnolCompletedMellinCoordinate) : BurnolL2 :=
  (sourceAdjointRate coordinate)⁻¹ • ∑ i : Fin 2,sourceCoefficients coordinate i •
    (sourceResolvent coordinate (regularForcing coordinate i)+
      sourceAdjoint coordinate (regularForcing coordinate i)+
      sourceAdjointRate coordinate • sourceAdjoint coordinate (jumpColumns i))

theorem sourceAdjointRate_ne_zero (coordinate : BurnolCompletedMellinCoordinate) :
    sourceAdjointRate coordinate ≠ 0 := by
  intro zero
  have real := congrArg Complex.re zero
  norm_num [sourceAdjointRate,Complex.mul_re,Complex.star_def] at real
  linarith [coordinate.rightHalf]

private theorem rightQuarter (coordinate : BurnolCompletedMellinCoordinate) :
    1/4 < (coordinate.value/2).re := by
  rw [Complex.div_re];norm_num;linarith [coordinate.rightHalf]

private theorem starRightQuarter (coordinate : BurnolCompletedMellinCoordinate) :
    1/4 < (star coordinate.value/2).re := by
  rw [Complex.div_re];norm_num;linarith [coordinate.rightHalf]

private theorem actualAdjoint_read (coordinate : BurnolCompletedMellinCoordinate) (value : BurnolL2) :
    (burnolDirectRightResolventCLM coordinate).adjoint value = sourceAdjoint coordinate value := by
  apply ext_inner_right ℂ
  intro test
  rw [ContinuousLinearMap.adjoint_inner_left]
  change inner ℂ value (burnolDirectRightResolvent (coordinate.value/2) test) = _
  simpa only [sourceAdjoint,star_div₀,star_ofNat] using
    OriginalKCompactAdjointRSource.actual_original_R_adjoint (coordinate.value/2)
      (rightQuarter coordinate) value test

/-- Both Fourier directions are justified on all L2 by the paid adjoint and Fourier source laws. -/
private theorem inverseFourier_Rbar_F (coordinate : BurnolCompletedMellinCoordinate) (value : BurnolL2) :
    fourierL2.symm (sourceResolvent coordinate (fourierL2 value)) = sourceAdjoint coordinate value := by
  rw [←actualAdjoint_read]
  apply ext_inner_left ℂ
  intro test
  calc
    inner ℂ test (fourierL2.symm (sourceResolvent coordinate (fourierL2 value))) =
        inner ℂ (fourierL2 test) (sourceResolvent coordinate (fourierL2 value)) := by
      rw [←fourierL2.inner_map_map test (fourierL2.symm _),fourierL2.apply_symm_apply]
    _ = inner ℂ (FiniteMobiusResolventFlux.Rplus (coordinate.value/2) (fourierL2 test)) (fourierL2 value) := by
      simpa only [sourceResolvent,star_div₀,star_ofNat,star_star] using
        OriginalKCompactAdjointRSource.actual_original_R_adjoint (star coordinate.value/2)
          (starRightQuarter coordinate) (fourierL2 test) (fourierL2 value)
    _ = inner ℂ (fourierL2 (burnolDirectRightResolvent (coordinate.value/2) test)) (fourierL2 value) := by
      rw [FiniteMobiusResolventFlux.fourier_R _ (rightQuarter coordinate)]
    _ = inner ℂ (burnolDirectRightResolvent (coordinate.value/2) test) value := fourierL2.inner_map_map _ _
    _ = inner ℂ test ((burnolDirectRightResolventCLM coordinate).adjoint value) :=
      (ContinuousLinearMap.adjoint_inner_right (burnolDirectRightResolventCLM coordinate) test value).symm

/-- Paid mixed resolvent action computes the adjoint of every full source regular column. -/
theorem sourceAdjoint_regularColumns (coordinate : BurnolCompletedMellinCoordinate) (i : Fin 2) :
    sourceAdjointRate coordinate • sourceAdjoint coordinate (regularColumns coordinate i) =
      sourceResolvent coordinate (regularForcing coordinate i)+sourceAdjoint coordinate (regularForcing coordinate i) := by
  have mixed := burnolDirectRightResolvent_fourier_mixed
    (star coordinate.value/2) (star coordinate.value/2)
    (starRightQuarter coordinate) (starRightQuarter coordinate) (regularForcing coordinate i)
  have mapped := congrArg fourierL2.symm mixed
  simp only [map_smul,map_neg,map_add,fourierL2.symm_apply_apply] at mapped
  change (star coordinate.value/2+star coordinate.value/2-1/2) •
      fourierL2.symm (sourceResolvent coordinate (fourierL2
        (sourceResolvent coordinate (regularForcing coordinate i)))) =
    -(fourierL2.symm (sourceResolvent coordinate (fourierL2 (regularForcing coordinate i)))+
      sourceResolvent coordinate (regularForcing coordinate i)) at mapped
  rw [inverseFourier_Rbar_F,inverseFourier_Rbar_F] at mapped
  change sourceAdjointRate coordinate • FiniteMobiusResolventFlux.Rplus (star coordinate.value/2)
    (-(1/2 : ℂ) • sourceResolvent coordinate (regularForcing coordinate i)) = _
  rw [FiniteMobiusResolventFlux.Rplus_smul _ _ (starRightQuarter coordinate)]
  unfold sourceAdjoint at mapped ⊢
  unfold sourceAdjointRate
  linear_combination (norm := module) -mapped

private theorem sourceAdjoint_columns (coordinate : BurnolCompletedMellinCoordinate) (i : Fin 2) :
    sourceAdjointRate coordinate • sourceAdjoint coordinate (sourceColumns coordinate i) =
      sourceResolvent coordinate (regularForcing coordinate i)+
      sourceAdjoint coordinate (regularForcing coordinate i)+
      sourceAdjointRate coordinate • sourceAdjoint coordinate (jumpColumns i) := by
  have source := sourceColumns_from_regular_resolvent coordinate i
  have read := sourceAdjoint_regularColumns coordinate i
  rw [source]
  rw [←actualAdjoint_read,←actualAdjoint_read,←actualAdjoint_read,map_add,smul_add]
  simpa only [actualAdjoint_read] using congrArg
    (fun value : BurnolL2 => value+sourceAdjointRate coordinate • sourceAdjoint coordinate (jumpColumns i)) read

/-- The complete original adjoint vector is generated by the two actual source forcings and jumps. -/
theorem sourceAdjoint_original (coordinate : BurnolCompletedMellinCoordinate) :
    sourceAdjoint coordinate (burnolCompletedMellinRieszVector coordinate : BurnolL2) =
      sourceAdjointField coordinate := by
  have generated : generatedK coordinate = ∑ i : Fin 2,sourceCoefficients coordinate i • sourceColumns coordinate i := by
    simp only [generatedK,Fin.sum_univ_two,sourceCoefficients,sourceColumns,Matrix.cons_val_zero,Matrix.cons_val_one]
  have weighted : sourceAdjointRate coordinate •
      sourceAdjoint coordinate (burnolCompletedMellinRieszVector coordinate : BurnolL2) =
      ∑ i : Fin 2,sourceCoefficients coordinate i •
        (sourceResolvent coordinate (regularForcing coordinate i)+
          sourceAdjoint coordinate (regularForcing coordinate i)+
          sourceAdjointRate coordinate • sourceAdjoint coordinate (jumpColumns i)) := by
    rw [←generatedK_eq_original,generated,←actualAdjoint_read,map_sum,Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [map_smul,actualAdjoint_read,smul_comm,sourceAdjoint_columns]
  have unweighted := congrArg (fun value : BurnolL2 => (sourceAdjointRate coordinate)⁻¹ • value) weighted
  simpa only [smul_smul,inv_mul_cancel₀ (sourceAdjointRate_ne_zero coordinate),one_smul,sourceAdjointField] using unweighted

/-- The actual source field reads every full input, retaining all outside-P material. -/
theorem original_R_full_input (coordinate : BurnolCompletedMellinCoordinate) (value : BurnolL2) :
    inner ℂ (burnolCompletedMellinRieszVector coordinate : BurnolL2)
      (burnolDirectRightResolvent (coordinate.value/2) value) = inner ℂ (sourceAdjointField coordinate) value := by
  have actual := OriginalKCompactAdjointRSource.actual_original_R_adjoint (coordinate.value/2)
    (rightQuarter coordinate) (burnolCompletedMellinRieszVector coordinate : BurnolL2) value
  simp only [star_div₀,star_ofNat] at actual
  change inner ℂ (burnolCompletedMellinRieszVector coordinate : BurnolL2)
    (burnolDirectRightResolvent (coordinate.value/2) value) =
      inner ℂ (sourceAdjoint coordinate (burnolCompletedMellinRieszVector coordinate : BurnolL2)) value at actual
  rw [sourceAdjoint_original] at actual
  exact actual

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKFullAdjointSource
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
