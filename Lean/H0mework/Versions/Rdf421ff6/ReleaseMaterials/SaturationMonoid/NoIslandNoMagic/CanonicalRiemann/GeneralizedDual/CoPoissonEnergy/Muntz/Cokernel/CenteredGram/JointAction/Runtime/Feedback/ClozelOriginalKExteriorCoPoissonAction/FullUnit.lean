import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKExteriorCoPoissonAction.Source
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKExteriorArithmeticMeans
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.ConstantFourier
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1600000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKExteriorCoPoissonAction.FullUnit
open Complex Filter MeasureTheory Set BurnolPhysicalState
open BurnolPhysicalState.OriginalRieszFinitePairing.CoPoisson
open BurnolPhysicalState.OriginalRieszFinitePairing.CoPoisson.Ward
open OriginalKSourceFiniteUpdate.OriginalBFiniteAction
open scoped InnerProductSpace Topology

def fullSource (c : BurnolCompletedMellinCoordinate) (h : ℝ) (i : Fin 2) : BurnolL2 :=
  fullWindowLoss h (sourceColumn c i)

def fullForward (c : BurnolCompletedMellinCoordinate) (h : ℝ) (i : Fin 2) : BurnolL2 :=
  exteriorWave c h i + centeringMean c h i • ConstantForward.value

/-- The independent reverse sequence is retained literally. -/
def exteriorReverse (c : BurnolCompletedMellinCoordinate) (h : ℝ) (i : Fin 2) : BurnolL2 :=
  limUnder atTop (fun N : ℕ => DualSource.source N (exteriorSource c h i))

def fullReverse (c : BurnolCompletedMellinCoordinate) (h : ℝ) (i : Fin 2) : BurnolL2 :=
  exteriorReverse c h i + centeringMean c h i • ConstantDual.value

theorem full_source_inventory (c : BurnolCompletedMellinCoordinate) (h : ℝ)
    (nonnegative : 0 ≤ h) (i : Fin 2) :
    fullSource c h i = exteriorSource c h i + centeringMean c h i • ConstantDual.seed := by
  rw [actual_exterior_source c h nonnegative i]
  rfl

theorem full_source_tate_inventory (c : BurnolCompletedMellinCoordinate) (h : ℝ)
    (nonnegative : 0 ≤ h) (i : Fin 2) :
    burnolTateReciprocalL2 (fullSource c h i) =
      burnolTateReciprocalL2 (exteriorSource c h i) + centeringMean c h i •
        burnolSourceScalePrimitive burnolUnitReciprocalPrimitiveL2 (1/4) := by
  rw [full_source_inventory c h nonnegative i, map_add, map_smul, ConstantFourier.reciprocal_source]

theorem full_forward_realizes (c : BurnolCompletedMellinCoordinate) (h : ℝ)
    (nonnegative : 0 ≤ h) (i : Fin 2) (test : SchwartzMap ℝ ℂ) :
    burnolRemainderSourceRead (fullSource c h i) test =
      (Lp.toTemperedDistributionCLM ℂ volume 2 (fullForward c h i)) test := by
  rw [full_source_inventory c h nonnegative i, ← burnolRemainderSourceReadCLM_apply,
    map_add, map_smul, burnolRemainderSourceReadCLM_apply, burnolRemainderSourceReadCLM_apply]
  have actual := exterior_wave_realizes c h nonnegative i test
  rw [← actual_exterior_source c h nonnegative i] at actual
  rw [actual, ConstantForward.original_realizes]
  simp only [fullForward, map_add, map_smul, add_apply, smul_apply, smul_eq_mul, Lp.toTemperedDistributionCLM_apply]

theorem full_forward_finite (c : BurnolCompletedMellinCoordinate) (h : ℝ)
    (nonnegative : 0 ≤ h) (i : Fin 2) (N : ℕ) :
    FiniteForcing.source N (fullSource c h i) = exteriorPrefix c h i N +
      centeringMean c h i • FiniteForcing.source N ConstantDual.seed := by
  change CountingDual.sourceCLM N (fullSource c h i) = _
  rw [full_source_inventory c h nonnegative i, map_add, map_smul]
  change FiniteForcing.source N (exteriorSource c h i) + _ = _
  rw [actual_exterior_source c h nonnegative i, ← exterior_prefix_source c h nonnegative i N]
  rfl

theorem full_forward_tendsto (c : BurnolCompletedMellinCoordinate) (h : ℝ)
    (nonnegative : 0 ≤ h) (i : Fin 2) :
    Tendsto (fun N : ℕ => FiniteForcing.source N (fullSource c h i)) atTop
      (𝓝 (fullForward c h i)) := by
  have actual := (exterior_prefix_tendsto c h i).add
    (ConstantForward.original_tendsto.const_smul (centeringMean c h i))
  exact actual.congr' (Eventually.of_forall (fun N => (full_forward_finite c h nonnegative i N).symm))

private theorem exterior_reverse_cauchy (c : BurnolCompletedMellinCoordinate) (h : ℝ)
    (nonnegative : 0 ≤ h) (i : Fin 2) :
    CauchySeq (fun N : ℕ => DualSource.source N (exteriorSource c h i)) := by
  have actual : CauchySeq (fun N : ℕ => FiniteForcing.source N (exteriorSource c h i)) := by
    have limit := (exterior_prefix_tendsto c h i).congr'
      (Eventually.of_forall (fun N => (exterior_prefix_source c h nonnegative i N).trans
        (congrArg (FiniteForcing.source N) (actual_exterior_source c h nonnegative i).symm)))
    exact limit.cauchySeq
  rw [Metric.cauchySeq_iff] at actual ⊢
  intro epsilon positive
  obtain ⟨N, after⟩ := actual epsilon positive
  refine ⟨N, ?_⟩
  intro m hm n hn
  simpa only [dist_eq_norm, CountingDual.difference_norm] using after m hm n hn

theorem exterior_reverse_tendsto (c : BurnolCompletedMellinCoordinate) (h : ℝ)
    (nonnegative : 0 ≤ h) (i : Fin 2) :
    Tendsto (fun N : ℕ => DualSource.source N (exteriorSource c h i)) atTop
      (𝓝 (exteriorReverse c h i)) :=
  (exterior_reverse_cauchy c h nonnegative i).tendsto_limUnder

theorem full_reverse_finite (c : BurnolCompletedMellinCoordinate) (h : ℝ)
    (nonnegative : 0 ≤ h) (i : Fin 2) (N : ℕ) :
    DualSource.source N (fullSource c h i) = DualSource.source N (exteriorSource c h i) +
      centeringMean c h i • DualSource.source N ConstantDual.seed := by
  rw [CountingDual.dual_eq_adjoint, full_source_inventory c h nonnegative i, map_add, map_smul]
  rw [← CountingDual.dual_eq_adjoint, ← CountingDual.dual_eq_adjoint]

theorem full_reverse_tendsto (c : BurnolCompletedMellinCoordinate) (h : ℝ)
    (nonnegative : 0 ≤ h) (i : Fin 2) :
    Tendsto (fun N : ℕ => DualSource.source N (fullSource c h i)) atTop
      (𝓝 (fullReverse c h i)) := by
  have actual := (exterior_reverse_tendsto c h nonnegative i).add
    (ConstantDual.original_tendsto.const_smul (centeringMean c h i))
  exact actual.congr' (Eventually.of_forall (fun N => (full_reverse_finite c h nonnegative i N).symm))

/-- The unit contribution survives in both actual Fourier directions. -/
theorem full_forward_fourier_inventory (c : BurnolCompletedMellinCoordinate) (h : ℝ) (i : Fin 2) :
    fourierL2 (fullForward c h i) = fourierL2 (exteriorWave c h i) + centeringMean c h i •
      burnolSourceScalePrimitive burnolUnitCountingPrimitiveL2 (1/4) := by
  rw [fullForward, map_add, map_smul, ConstantFourier.original_square, ConstantFourier.reciprocal_value]

/-- Both exterior gaps retain the exact same weighted program, before the full unit is added. -/
theorem exterior_two_mean_inventory (c : BurnolCompletedMellinCoordinate) (h : ℝ)
    (nonnegative : 0 ≤ h) (bounded : h ≤ Real.log 2) (i : Fin 2) :
    burnolQuarterRestriction (exteriorWave c h i) =
      (positiveWeight c h i 4 * (bandLower h-4 : ℂ) -
        ∫ u : ℝ in Ioc (bandLower h) 4, deriv (positiveWeight c h i) u * (bandLower h-u : ℂ)) •
          intervalConstant (1/4) ∧
    burnolQuarterRestriction (fourierL2 (exteriorWave c h i)) =
      (positiveWeight c h i 4 * -(Real.log (4/bandLower h) : ℂ) -
        ∫ u : ℝ in Ioc (bandLower h) 4,
          deriv (positiveWeight c h i) u * -(Real.log (u/bandLower h) : ℂ)) • intervalConstant (1/4) := by
  have lower := bandLower_in_annulus h nonnegative bounded
  have strict : (1/4 : ℝ) < bandLower h := by
    have exponential : 1/2 ≤ Real.exp (-h) := by
      calc
        1/2 = Real.exp (-Real.log 2) := by
          rw [Real.exp_neg, Real.exp_log (by norm_num)]
          norm_num
        _ ≤ Real.exp (-h) := Real.exp_le_exp.mpr (neg_le_neg bounded)
    unfold bandLower
    linarith
  exact OriginalKExteriorArithmeticMeans.weighted_two_mean_action _ _ _ _ strict
    (bandLower_le_four h nonnegative) le_rfl
    ((positiveWeight_deriv_continuousOn c h i).mono
      (fun _ inside => (bandLower_pos h).trans_le inside.1))

/-- Two faithful sequences with their whole centering inventory. -/
theorem full_two_direction_action (c : BurnolCompletedMellinCoordinate) (h : ℝ)
    (nonnegative : 0 ≤ h) (i : Fin 2) :
    (Tendsto (fun N : ℕ => FiniteForcing.source N (fullSource c h i)) atTop (𝓝 (fullForward c h i))) ∧
    (Tendsto (fun N : ℕ => DualSource.source N (fullSource c h i)) atTop (𝓝 (fullReverse c h i))) ∧
    (burnolTateReciprocalL2 (fullSource c h i) = burnolTateReciprocalL2 (exteriorSource c h i) +
      centeringMean c h i • burnolSourceScalePrimitive burnolUnitReciprocalPrimitiveL2 (1/4)) ∧
    (fourierL2 (fullForward c h i) = fourierL2 (exteriorWave c h i) + centeringMean c h i •
      burnolSourceScalePrimitive burnolUnitCountingPrimitiveL2 (1/4)) :=
  ⟨full_forward_tendsto c h nonnegative i, full_reverse_tendsto c h nonnegative i,
    full_source_tate_inventory c h nonnegative i, full_forward_fourier_inventory c h i⟩
end OriginalKExteriorCoPoissonAction.FullUnit
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
