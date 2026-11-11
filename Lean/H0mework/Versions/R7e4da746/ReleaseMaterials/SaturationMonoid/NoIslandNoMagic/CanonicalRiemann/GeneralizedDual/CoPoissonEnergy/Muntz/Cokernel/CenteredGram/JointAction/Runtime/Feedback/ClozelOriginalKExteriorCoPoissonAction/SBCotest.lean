import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKExteriorCoPoissonAction.SBPlusVolterra
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKExteriorCoPoissonAction.BCotest
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCompactAdjointRSource.Source
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKExteriorSBCotest
open Complex Filter MeasureTheory Set BurnolPhysicalState
open OriginalKExteriorCoPoissonAction OriginalKExteriorSBPlusVolterra
open OriginalKSourceGramAction OriginalKSourceResolventReconstruction
open OriginalKCoefficientBFiniteAction
open BurnolPhysicalState.OriginalRieszFinitePairing.CoPoisson.Ward
open scoped InnerProductSpace Topology

theorem plusRaw_memLp (c : BurnolCompletedMellinCoordinate) (h : ℝ) (nonnegative : 0 ≤ h) :
    MemLp (plusRaw c h) 2 volume :=
  (memLp_congr_ae (actual_SB_Rplus_source c h nonnegative)).mp
    (Lp.memLp (FiniteMobiusResolventFlux.Rplus (c.value/2) (exteriorSource c h 1)))

theorem sb_pairing_integrable (c : BurnolCompletedMellinCoordinate) (h : ℝ)
    (nonnegative : 0 ≤ h) (test : BurnolL2) :
    Integrable (fun x : ℝ => inner ℂ (test x) (plusRaw c h x)) volume := by
  apply (L2.integrable_inner (𝕜 := ℂ) test
    (FiniteMobiusResolventFlux.Rplus (c.value/2) (exteriorSource c h 1))).congr
  filter_upwards [actual_SB_Rplus_source c h nonnegative] with x read
  rw [read]

theorem sb_Rplus_pairing (c : BurnolCompletedMellinCoordinate) (h : ℝ)
    (nonnegative : 0 ≤ h) (test : BurnolL2) :
    inner ℂ test (FiniteMobiusResolventFlux.Rplus (c.value/2) (exteriorSource c h 1)) =
      ∫ x : ℝ, inner ℂ (test x) (plusRaw c h x) := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [actual_SB_Rplus_source c h nonnegative] with x read
  rw [read]

private theorem source_adjoint_cotest (c : BurnolCompletedMellinCoordinate) (value test : BurnolL2) :
    inner ℂ (sourceResolvent c value) test =
      inner ℂ value (FiniteMobiusResolventFlux.Rplus (c.value/2) test) := by
  have right : 1/4 < (star c.value/2).re := by
    rw [Complex.div_re]
    norm_num
    linarith [c.rightHalf]
  have actual := OriginalKCompactAdjointRSource.actual_original_R_adjoint
    (star c.value/2) right test value
  have step : inner ℂ test (sourceResolvent c value) =
      inner ℂ (FiniteMobiusResolventFlux.Rplus (c.value/2) test) value := by
    simpa only [sourceResolvent,star_div₀,star_ofNat,star_star] using actual
  calc
    _ = star (inner ℂ test (sourceResolvent c value)) := (inner_conj_symm _ _).symm
    _ = star (inner ℂ (FiniteMobiusResolventFlux.Rplus (c.value/2) test) value) := congrArg star step
    _ = _ := inner_conj_symm _ _

/-- The complete original forcing and jump columns generate the position cotest. -/
def columnPrice (c : BurnolCompletedMellinCoordinate) (h : ℝ) (i : Fin 2) : ℂ :=
  -(1/2:ℂ) * (∫ x : ℝ, inner ℂ ((regularForcing c i) x) (plusRaw c h x)) +
    inner ℂ (jumpColumns i) (exteriorSource c h 1)

def sourcePrice (c : BurnolCompletedMellinCoordinate) (h : ℝ) : ℂ :=
  ∑ i : Fin 2, star (sourceCoefficients c i) * columnPrice c h i

theorem source_column_cotest (c : BurnolCompletedMellinCoordinate) (h : ℝ)
    (nonnegative : 0 ≤ h) (i : Fin 2) :
    inner ℂ (sourceColumns c i) (exteriorSource c h 1) = columnPrice c h i := by
  rw [sourceColumns_from_regular_resolvent]
  simp only [regularColumns,inner_add_left,inner_smul_left,starRingEnd_apply,
    star_neg,star_div₀,star_ofNat,star_one]
  rw [source_adjoint_cotest,sb_Rplus_pairing c h nonnegative]
  rfl

/-- The same actual SB field computes the original unacted K cotest. -/
theorem original_K_source_cotest (c : BurnolCompletedMellinCoordinate) (h : ℝ)
    (nonnegative : 0 ≤ h) :
    inner ℂ (burnolCompletedMellinRieszVector c : BurnolL2) (exteriorSource c h 1) = sourcePrice c h := by
  have source : generatedK c = ∑ i : Fin 2, sourceCoefficients c i • sourceColumns c i := by
    simp only [generatedK,Fin.sum_univ_two,sourceCoefficients,sourceColumns,
      Matrix.cons_val_zero,Matrix.cons_val_one]
  rw [←generatedK_eq_original,source]
  simp only [sum_inner,inner_smul_left,starRingEnd_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [source_column_cotest c h nonnegative i]

/-- The complete position loss retains the actual m1 source unit. -/
theorem original_full_SB_loss_cotest (c : BurnolCompletedMellinCoordinate) (h : ℝ)
    (nonnegative : 0 ≤ h) :
    inner ℂ (burnolCompletedMellinRieszVector c : BurnolL2) (FullUnit.fullSource c h 1) =
      sourcePrice c h + centeringMean c h 1 *
        inner ℂ (burnolCompletedMellinRieszVector c : BurnolL2) ConstantDual.seed := by
  rw [FullUnit.full_source_inventory c h nonnegative 1,inner_add_right,
    inner_smul_right,original_K_source_cotest c h nonnegative]

/-- Both literal source cotests enter the complete original arithmetic remainder. -/
theorem complete_arithmetic_core_cotest (c : BurnolCompletedMellinCoordinate)
    (zero : riemannZeta c.value = 0) (h : ℝ) (nonnegative : 0 ≤ h) (bounded : h ≤ Real.log 2) :
    inner ℂ (burnolCompletedMellinRieszVector c : BurnolL2) (arithmeticCoreRemainder c h) =
      inner ℂ (burnolCompletedMellinRieszVector c : BurnolL2)
        (OriginalKFixedBoundarySourceFibre.finiteBoundaryAction c h (elementarySource c)) - (1/2:ℂ) *
      (sourcePrice c h - OriginalKExteriorBCotest.sourcePrice c h + centeringMean c h 1 *
          inner ℂ (burnolCompletedMellinRieszVector c : BurnolL2) ConstantDual.seed -
        centeringMean c h 0 *
          inner ℂ (burnolCompletedMellinRieszVector c : BurnolL2) (fourierL2 ConstantDual.seed)) := by
  rw [OriginalKExteriorBCotest.original_arithmetic_core_cotest c zero h nonnegative bounded,
    original_K_source_cotest c h nonnegative]

/-- The complete original fixed residual reads both generated forcing prices. -/
theorem complete_fixedResidual_cotest (c : BurnolCompletedMellinCoordinate)
    (zero : riemannZeta c.value = 0) (h : ℝ) (nonnegative : 0 ≤ h) (bounded : h ≤ Real.log 2)
    (fixed : h = Real.log stageZeroSonineQ) :
    burnolPaFixedShiftResidual c zero =
      -(inner ℂ (burnolCompletedMellinRieszVector c : BurnolL2)
        (OriginalKFixedBoundarySourceFibre.finiteBoundaryAction c h (elementarySource c)) - (1/2:ℂ) *
      (sourcePrice c h - OriginalKExteriorBCotest.sourcePrice c h + centeringMean c h 1 *
          inner ℂ (burnolCompletedMellinRieszVector c : BurnolL2) ConstantDual.seed -
        centeringMean c h 0 *
          inner ℂ (burnolCompletedMellinRieszVector c : BurnolL2) (fourierL2 ConstantDual.seed))) := by
  rw [OriginalKExteriorBCotest.original_fixedResidual_B_cotest c zero h nonnegative bounded fixed,
    original_K_source_cotest c h nonnegative]

/-- The original observation owns the coordinate, zero witness and fixed source shift. -/
theorem original_fixedResidual_cotest (observation : GeneratedRiemannZeroObservation)
    (nontrivial : ¬∃ n : Nat, observation.coordinate = -2*(n+1))
    (half : OriginalKCombCalculation.Half observation) :
    let c := OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half
    let h := Real.log stageZeroSonineQ
    burnolPaFixedShiftResidual c observation.mathlibZero =
      -(inner ℂ (burnolCompletedMellinRieszVector c : BurnolL2)
        (OriginalKFixedBoundarySourceFibre.finiteBoundaryAction c h (elementarySource c)) - (1/2:ℂ) *
      (sourcePrice c h - OriginalKExteriorBCotest.sourcePrice c h + centeringMean c h 1 *
          inner ℂ (burnolCompletedMellinRieszVector c : BurnolL2) ConstantDual.seed -
        centeringMean c h 0 *
          inner ℂ (burnolCompletedMellinRieszVector c : BurnolL2) (fourierL2 ConstantDual.seed))) := by
  dsimp only
  have nonnegative : 0 ≤ Real.log stageZeroSonineQ := by
    apply Real.log_nonneg
    norm_num [stageZeroSonineQ]
  have bounded : Real.log stageZeroSonineQ ≤ Real.log 2 := by
    apply Real.log_le_log stageZeroSonineQ_pos
    change Real.sqrt 3 ≤ (2:ℝ)
    exact (Real.sqrt_le_iff).2 ⟨by norm_num,by norm_num⟩
  exact complete_fixedResidual_cotest _ observation.mathlibZero _ nonnegative bounded rfl

end OriginalKExteriorSBCotest
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
