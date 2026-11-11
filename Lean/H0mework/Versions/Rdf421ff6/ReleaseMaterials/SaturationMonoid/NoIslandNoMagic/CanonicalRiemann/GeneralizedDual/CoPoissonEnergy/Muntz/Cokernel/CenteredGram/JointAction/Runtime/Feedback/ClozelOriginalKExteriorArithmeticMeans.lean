import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCoefficientBFiniteAction.Source
import H0mework.Versions.V2.Arithmetic.RiemannUnitShell.HarmonicRealization
import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.WeightedPrefix
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1200000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKExteriorArithmeticMeans
open Complex MeasureTheory Set Filter BurnolPhysicalState
open scoped InnerProductSpace Topology
local notation "Hq" => BurnolQuarterIntervalL2
local notation "q" => (1/4 : ℝ)

private theorem native_position_restriction (lower upper : ℝ)
    (positive : 0 < lower) (ordered : lower ≤ upper) (bounded : upper ≤ 4) :
    burnolQuarterRestriction (burnolReciprocalStepNativeWave lower upper) =
      (lower-upper : ℂ) • intervalConstant q := by
  rw [burnolReciprocalStepNativeWave_eq lower upper positive ordered]
  apply Lp.ext
  filter_upwards [LpToLpRestrictCLM_coeFn ℂ (symmetricInterval q)
      (burnolReciprocalStepWaveL2 lower upper positive ordered),
    ae_restrict_of_ae (s := symmetricInterval q)
      (burnolReciprocalStepWave_memLp lower upper positive ordered).coeFn_toLp,
    Lp.coeFn_smul (lower-upper : ℂ) (intervalConstant q), intervalConstant_coeFn q,
    ae_restrict_mem (measurableSet_symmetricInterval q)] with x hrestrict hraw hsmul hconst hx
  change (burnolQuarterRestriction (burnolReciprocalStepWaveL2 lower upper positive ordered) : ℝ → ℂ) x =
    (burnolReciprocalStepWaveL2 lower upper positive ordered : ℝ → ℂ) x at hrestrict
  change (burnolReciprocalStepWaveL2 lower upper positive ordered : ℝ → ℂ) x =
    burnolReciprocalStepWaveRaw lower upper x at hraw
  rw [hrestrict, hraw, hsmul]
  change burnolReciprocalStepWaveRaw lower upper x = (lower-upper : ℂ)*intervalConstant q x
  rw [hconst, mul_one]
  apply burnolReciprocalStepWave_small lower upper x positive ordered
  have upperPos := positive.trans_le ordered
  have invBound : q ≤ upper⁻¹ := by
    rw [inv_eq_one_div, le_div_iff₀ upperPos]
    linarith
  exact (abs_le.mpr hx).trans invBound

private theorem native_fourier_restriction (lower upper : ℝ)
    (lowerStrict : q < lower) (ordered : lower ≤ upper) (bounded : upper ≤ 4) :
    burnolQuarterRestriction (fourierL2 (burnolReciprocalStepNativeWave lower upper)) =
      -(Real.log (upper/lower) : ℂ) • intervalConstant q := by
  apply Lp.ext
  filter_upwards [LpToLpRestrictCLM_coeFn ℂ (symmetricInterval q)
      (fourierL2 (burnolReciprocalStepNativeWave lower upper)),
    ae_restrict_of_ae (s := symmetricInterval q)
      (burnolReciprocalStepFourier_coeFn lower upper lowerStrict ordered bounded),
    Lp.coeFn_smul (-(Real.log (upper/lower) : ℂ)) (intervalConstant q), intervalConstant_coeFn q,
    ae_restrict_mem (measurableSet_symmetricInterval q)] with x hrestrict hraw hsmul hconst hx
  change (burnolQuarterRestriction (fourierL2 (burnolReciprocalStepNativeWave lower upper)) : ℝ → ℂ) x =
    (fourierL2 (burnolReciprocalStepNativeWave lower upper) : ℝ → ℂ) x at hrestrict
  rw [hrestrict, hraw, hsmul]
  change burnolHarmonicStepWaveRaw lower upper x = -(Real.log (upper/lower) : ℂ)*intervalConstant q x
  rw [hconst, mul_one]
  have gap : ∀ {u : ℝ}, |u| ≤ q → burnolTateStepBoxRaw lower upper u = 0 := by
    intro u hu
    apply if_neg
    intro active
    linarith [active.1]
  rw [burnolHarmonicStepWaveRaw,
    ← burnolTateStepBox_finiteCoSum lower upper x (by linarith) (by linarith),
    burnolInnerGapForward_innerGap _ gap (abs_le.mpr hx), zero_sub]

/-- The actual two gap prices of the native counted source. -/
theorem native_two_means (lower upper : ℝ)
    (lowerStrict : q < lower) (ordered : lower ≤ upper) (bounded : upper ≤ 4) :
    burnolQuarterRestriction (burnolReciprocalStepNativeWave lower upper) =
      (lower-upper : ℂ) • intervalConstant q ∧
    burnolQuarterRestriction (fourierL2 (burnolReciprocalStepNativeWave lower upper)) =
      -(Real.log (upper/lower) : ℂ) • intervalConstant q :=
  ⟨native_position_restriction lower upper (by linarith) ordered bounded,
    native_fourier_restriction lower upper lowerStrict ordered bounded⟩

private theorem weighted_family_integrable (lower upper : ℝ) (f' : ℝ → ℂ)
    (positive : 0 < lower) (regular : ContinuousOn f' (Icc lower upper)) :
    IntegrableOn (fun u => f' u • burnolReciprocalStepNativeWave lower u) (Ioc lower upper) := by
  have native : ContinuousOn (burnolReciprocalStepNativeWave lower) (Icc lower upper) :=
    ((burnolSourceScalePrimitive_continuous burnolUnitCountingPrimitiveL2).mono
      (fun _ inside => positive.trans_le inside.1)).sub continuousOn_const
  exact (regular.smul native).integrableOn_Icc.mono_set Ioc_subset_Icc_self

private theorem weighted_restriction (read : BurnolL2 →L[ℂ] Hq)
    (lower upper : ℝ) (f f' price : ℝ → ℂ) (positive : 0 < lower) (ordered : lower ≤ upper)
    (regular : ContinuousOn f' (Icc lower upper))
    (native : ∀ u ∈ Icc lower upper,
      read (burnolReciprocalStepNativeWave lower u) = price u • intervalConstant q) :
    read (burnolWeightedReciprocalStepWave lower upper f f') =
      (f upper * price upper - ∫ u : ℝ in Ioc lower upper, f' u * price u) • intervalConstant q := by
  rw [burnolWeightedReciprocalStepWave, map_sub, map_smul,
    native upper ⟨ordered, le_rfl⟩,
    ← read.integral_comp_comm (weighted_family_integrable lower upper f' positive regular)]
  have integralRead : (∫ u : ℝ in Ioc lower upper, read (f' u • burnolReciprocalStepNativeWave lower u)) =
      ∫ u : ℝ in Ioc lower upper, (f' u * price u) • intervalConstant q := by
    apply setIntegral_congr_fun measurableSet_Ioc
    intro u inside
    dsimp only
    rw [map_smul, native u ⟨inside.1.le, inside.2⟩, smul_smul]
  rw [integralRead, integral_smul_const, smul_smul, sub_smul]

/-- Both constant gaps are generated by the same complete weighted action. -/
theorem weighted_two_mean_action (lower upper : ℝ) (f f' : ℝ → ℂ)
    (lowerStrict : q < lower) (ordered : lower ≤ upper) (bounded : upper ≤ 4)
    (regular : ContinuousOn f' (Icc lower upper)) :
    burnolQuarterRestriction (burnolWeightedReciprocalStepWave lower upper f f') =
      (f upper * (lower-upper : ℂ) - ∫ u : ℝ in Ioc lower upper, f' u * (lower-u : ℂ)) • intervalConstant q ∧
    burnolQuarterRestriction (fourierL2 (burnolWeightedReciprocalStepWave lower upper f f')) =
      (f upper * -(Real.log (upper/lower) : ℂ) -
        ∫ u : ℝ in Ioc lower upper, f' u * -(Real.log (u/lower) : ℂ)) • intervalConstant q := by
  constructor
  · exact weighted_restriction burnolQuarterRestriction lower upper f f' (fun u => (lower-u : ℂ))
      (by linarith) ordered regular (fun u inside =>
        native_position_restriction lower u (by linarith) inside.1 (inside.2.trans bounded))
  · exact weighted_restriction (burnolQuarterRestriction.comp fourierL2.toLinearIsometry.toContinuousLinearMap)
      lower upper f f' (fun u => -(Real.log (u/lower) : ℂ))
      (by linarith) ordered regular (fun u inside =>
        native_fourier_restriction lower u lowerStrict inside.1 (inside.2.trans bounded))

end OriginalKExteriorArithmeticMeans
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
