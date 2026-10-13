import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.CoPoisson.Source.Mobius.Window.Action.ResolventFlux.Dilation
import H0mework.Versions.V2.Arithmetic.MobiusSource.SourceRead
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace FiniteMobiusResolventFlux
open Complex MeasureTheory Set Filter
open scoped InnerProductSpace

theorem actual_mean_eq_ambient : actualMean=burnolAmbientGapCoefficient (1/4:ℝ) := rfl

theorem source_negative_restriction (value : Ambient) (shift : ℝ) (nonpositive : shift≤0) :
    burnolRadiusRestriction (1/4:ℝ) (burnolMultiplicativeDilation shift (value : BurnolL2))=
      ((Real.exp (shift/2):ℂ)*actualMean (value : BurnolL2)) • intervalConstant (1/4:ℝ) := by
  have source := (ae_restrict_iff' (measurableSet_symmetricInterval (1/4:ℝ))).mp (burnolAmbientGap_ae value)
  have qmp : Measure.QuasiMeasurePreserving (fun x : ℝ => Real.exp shift*x) volume volume := by
    have actual : Measure.QuasiMeasurePreserving (fun x : ℝ => Real.exp shift • x) volume volume :=
      Measure.quasiMeasurePreserving_smul (μ:=(volume : Measure ℝ)) (r:=Real.exp shift) (Real.exp_ne_zero shift)
    exact actual
  apply Lp.ext
  filter_upwards [LpToLpRestrictCLM_coeFn ℂ (symmetricInterval (1/4:ℝ)) (burnolMultiplicativeDilation shift (value : BurnolL2)),
    ae_restrict_of_ae (burnolMultiplicativeDilation_coeFn shift (value : BurnolL2)),ae_restrict_of_ae (qmp.ae source),
    ae_restrict_mem (measurableSet_symmetricInterval (1/4:ℝ)),
    Lp.coeFn_smul ((Real.exp (shift/2):ℂ)*actualMean (value : BurnolL2)) (intervalConstant (1/4:ℝ)),intervalConstant_coeFn (1/4:ℝ)]
      with x restricted moved read inside scalar unit
  have scaledInside : Real.exp shift*x∈symmetricInterval (1/4:ℝ) := by
    have small : |Real.exp shift*x|≤1/4 := by
      rw [abs_mul,abs_of_pos (Real.exp_pos shift)]
      exact (mul_le_of_le_one_left (abs_nonneg x) (Real.exp_le_one_iff.mpr nonpositive)).trans (abs_le.mpr inside)
    exact abs_le.mp small
  change (burnolRadiusRestriction (1/4:ℝ) (burnolMultiplicativeDilation shift (value : BurnolL2)) : ℝ→ℂ) x=_
  change (burnolRadiusRestriction (1/4:ℝ) (burnolMultiplicativeDilation shift (value : BurnolL2)) : ℝ→ℂ) x=
    (burnolMultiplicativeDilation shift (value : BurnolL2) : ℝ→ℂ) x at restricted
  rw [restricted,moved,scalar]
  unfold burnolL2RawNormalizedDilation
  rw [read scaledInside,actual_mean_physical]
  simp only [Pi.smul_apply,smul_eq_mul,unit,mul_one]

theorem actual_mean_source_negative (value : Ambient) (shift : ℝ) (nonpositive : shift≤0) :
    actualMean (burnolMultiplicativeDilation shift (value : BurnolL2))=
      (Real.exp (shift/2):ℂ)*actualMean (value : BurnolL2) := by
  change (‖intervalConstant (1/4:ℝ)‖^2:ℂ)⁻¹ * inner ℂ (intervalConstant (1/4:ℝ))
    (burnolRadiusRestriction (1/4:ℝ) (burnolMultiplicativeDilation shift (value : BurnolL2))) = _
  rw [source_negative_restriction value shift nonpositive,inner_smul_right,inner_self_eq_norm_sq_to_K]
  have nonzero : (‖intervalConstant (1/4:ℝ)‖^2:ℂ)≠0 := by
    exact_mod_cast pow_ne_zero 2 (norm_ne_zero_iff.mpr (intervalConstant_ne_zero (by norm_num : (0:ℝ)<1/4)))
  let price : ℂ := (‖intervalConstant (1/4:ℝ)‖:ℂ)^2
  change price⁻¹ * (((Real.exp (shift/2):ℂ)*actualMean (value : BurnolL2))*price)=_
  have priceNonzero : price≠0 := nonzero
  rw [mul_comm (((Real.exp (shift/2):ℂ)*actualMean (value : BurnolL2))) price,
    ← mul_assoc,inv_mul_cancel₀ priceNonzero,one_mul]


end FiniteMobiusResolventFlux
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
