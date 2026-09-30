import H0mework.Versions.X.NavierStokes.WindowSourceGreen.LowerBound

set_option autoImplicit false
open scoped BigOperators Matrix Topology ENNReal
namespace SaturationMonoid.NavierStokes.NativeWindowMotherLowerContinuity
open Set Filter MeasureTheory
open PhysicsCore DiracExteriorMatterAction StageNineHolonomicField
open ThreeDimensionalPeriodicCoarseFilterCore
open NativeWindowAbsoluteLowerOperator
open NativeWindowAbsoluteLowerBound (lift Full)
open NativeWindowGreenTestForm (SpinFiber)
open NativeCanonicalFluidCoframe (density scale)
noncomputable section
attribute [local instance 10000] NormedAddCommGroup.toAddCommGroup NormedSpace.toModule
attribute [local instance 10000] PseudoMetricSpace.toUniformSpace UniformSpace.toTopologicalSpace
abbrev Data := PhysicalSpace × (Fin 4 → PhysicalSpace)

private theorem density_continuous : Continuous density := by unfold density; fun_prop
private theorem scale_continuous : Continuous scale := by
  unfold scale
  have rho:=density_continuous
  fun_prop (disch := positivity)

private theorem spin_continuous : Continuous (fun data : Data =>
    (1/2:ℝ)*NativeWindowMassReciprocal.derivative data.1 (data.2 0)) := by
  simp only [NativeWindowMassReciprocal.derivative_apply]
  have value : Continuous (fun data : Data => NativeWindowMassReciprocal.value data.1) :=
    NativeWindowMassReciprocal.value_continuous.comp continuous_fst
  fun_prop

private theorem free_continuous (d : Fin 4) (c : Fin 3) : Continuous (fun data : Data =>
    NativeBalancedMaterialJet.freeCoefficients data.1 data.2 d c) := by
  fin_cases d <;> fin_cases c <;>
    simp [NativeBalancedMaterialJet.freeCoefficients,NativeBalancedJetCoefficients.coefficients,
      NativeMaterialJetAction.normalizedJet,NativePauliCoframeAction.normalizedVelocity,
      NativeBalancedJetCoefficients.temporalProjection,NativeBalancedJetCoefficients.helicityCoefficient,
      NativeBalancedJetCoefficients.pairing,NativeBalancedColorControl.weight,NativeCartanConstitutive.squared,
      NativePauliControl.denominator,NativeBalancedJetCoefficients.curl,Fin.sum_univ_three]
  all_goals fun_prop (disch := (intros; positivity))

private theorem cartan_continuous (d : Fin 4) (p : Fin 6) : Continuous (fun v : PhysicalSpace => cartanCoefficient v d p) := by
  have scale:=scale_continuous
  have rho:=density_continuous
  fin_cases d <;> fin_cases p <;>
    simp [cartanCoefficient,NativeCartanCoordinates.profile,NativeCartanCoordinates.currentVector]
  all_goals fun_prop (disch := (intro v; exact (mul_pos (by norm_num : (0:ℝ)<8) (NativeCanonicalFluidCoframe.scale_pos v)).ne'))

private theorem control_original (v : PhysicalSpace) : cartanControl v=
    NativePauliControl.coefficients
      (fun i => 3/2*scale v^2*(1-NativeCartanConstitutive.squared (NativePauliCoframeAction.normalizedVelocity v))/
        NativePauliControl.denominator (NativePauliCoframeAction.normalizedVelocity v)*NativePauliCoframeAction.normalizedVelocity v i)
      0 (NativeCartanConstitutive.isotropicCorrection (scale v) (NativePauliCoframeAction.normalizedVelocity v)) := by
  simpa only [cartanControl,NativeCartanConstitutive.response_eq,neg_smul,Complex.ofReal_pow] using
    NativeCartanConstitutive.response_control (scale v) (NativePauliCoframeAction.normalizedVelocity v)

private theorem control_continuous (d : Fin 4) (c : Fin 3) : Continuous (fun v : PhysicalSpace => cartanControl v d c) := by
  simp_rw [control_original]
  have scale:=scale_continuous
  fin_cases d <;> fin_cases c <;>
    simp [NativePauliControl.coefficients,NativeCartanConstitutive.isotropicCorrection,
      NativePauliCoframeAction.normalizedVelocity,NativeCartanConstitutive.squared,NativePauliControl.denominator,Fin.sum_univ_three]
  all_goals fun_prop (disch := (intros; positivity))

private theorem constitutive_continuous (d : Fin 4) (c : Fin 3) : Continuous (fun v : PhysicalSpace =>
    NativeConstitutiveColor.coefficients v d c) := by
  have scale:=scale_continuous
  fin_cases d <;> fin_cases c <;>
    simp [NativeConstitutiveColor.coefficients,NativeConstitutiveColor.correctionScale,
      NativeConstitutiveColor.radial,NativePauliCoframeAction.normalizedVelocity,NativeCartanStressLaw.fluxFactor,
      NativeCartanConstitutive.squared,NativePauliControl.denominator,Fin.sum_univ_three]
  all_goals fun_prop (disch := (intros; positivity))

private theorem read_continuous (read : DiracExteriorMatterCarrier →ₗ[ℂ] ℂ) (basis : DiracExteriorMatterCarrier) :
    Continuous (fun data : Data => read (NativeWindowAbsoluteTimePhysicalMatter.lower data.1 data.2 basis)) := by
  simp only [lower_original,static,color_factor,bareColor_expansion,cartan_expansion,
    LinearMap.add_apply,LinearMap.smul_apply,LinearMap.sum_apply,LinearMap.id_apply,
    map_add,map_smul,map_sum,smul_eq_mul]
  have spin:=spin_continuous
  have rho : Continuous (fun data : Data => (density data.1)⁻¹) :=
    NativeWindowMassReciprocal.value_continuous.comp continuous_fst
  have free (d : Fin 4) (c : Fin 3):=free_continuous d c
  have cartan (d : Fin 4) (p : Fin 6) : Continuous (fun data : Data => cartanCoefficient data.1 d p) :=
    (cartan_continuous d p).comp continuous_fst
  have control (d : Fin 4) (c : Fin 3) : Continuous (fun data : Data => cartanControl data.1 d c) :=
    (control_continuous d c).comp continuous_fst
  have constitutive (d : Fin 4) (c : Fin 3) : Continuous (fun data : Data => NativeConstitutiveColor.coefficients data.1 d c) :=
    (constitutive_continuous d c).comp continuous_fst
  fun_prop

private theorem row_continuous (output : MatterCoordinateIndex) (entry : Fin 4 × Fin 2) :
    Continuous (fun data : Data => matterCoordinateEquiv
      (NativeWindowAbsoluteTimePhysicalMatter.lower data.1 data.2
        (NativeWindowStageTenWholeFirstJet.materialBasis entry.1 entry.2)) output) := by
  let read : DiracExteriorMatterCarrier →ₗ[ℂ] ℂ :=
    (PiLp.proj (𝕜 := ℂ) 2 (fun _ : MatterCoordinateIndex => ℂ) output).toLinearMap.comp matterCoordinateEquiv.toLinearMap
  exact read_continuous read (NativeWindowStageTenWholeFirstJet.materialBasis entry.1 entry.2)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem continuous_lift : Continuous (fun data : PhysicalSpace × (Fin 4 → PhysicalSpace) × SpinFiber E =>
    lift (NativeWindowAbsoluteTimePhysicalMatter.lower data.1 data.2.1) data.2.2) := by
  unfold lift
  apply (PiLp.continuous_toLp 2 _).comp
  apply continuous_pi
  intro output
  apply continuous_finsetSum
  intro entry _
  exact ((row_continuous output entry).comp (continuous_fst.prodMk (continuous_snd.fst))).smul
    ((PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin 4 × Fin 2 => E) entry).continuous.comp continuous_snd.snd)

end
end SaturationMonoid.NavierStokes.NativeWindowMotherLowerContinuity
