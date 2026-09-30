import H0mework.Versions.X.NavierStokes.WindowEnergyPressure.Source
import H0mework.Versions.X.NavierStokes.WindowSourceSobolev.PreparationWindow

set_option autoImplicit false
open scoped BigOperators Topology ENNReal
namespace SaturationMonoid.NavierStokes.NativeWindowPreparedPressureSource
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open NativeResolventCompactness NativeWholeResolvent NativeWholeH1Mixed NativeWholeH1Pairing NativeEndpointVelocityCarrier
open NativeWindowPressureLowKernel
open NativeWindowPressureLowSource (work work_bound work_continuous coefficient coefficient_nonnegative)
open NativeUnheatedSourceQuadraticApprox (physicalSource physicalSource_measurable)
open NativeForwardWindowJets (kernelJet)
open RationalVorticityEvaluator.ButterflyStackedSourceCurrent
noncomputable section

def physical (time : ℝ) : wholePhysical :=
  if nonnegative : 0 ≤ time then NativeUnheatedSourceGradient.physical stackedShortCurrent time nonnegative
  else NativeUnheatedSourceGradient.physical stackedShortCurrent 0 le_rfl

theorem physical_original (time : ℝ) : (physical time).1 = (NativeUnifiedCompleteSource.source stackedShortCurrent time).fst := by
  unfold physical
  split_ifs with nonnegative
  · rfl
  · rw [NativeWindowPreparationSource.complete_nonpositive stackedShortCurrent time (le_of_not_ge nonnegative)]
    rfl

theorem physical_existing (time : ℝ) (nonnegative : 0 ≤ time) :
    physical time = physicalSource stackedShortCurrent time := by
  simp only [physical,physicalSource,dif_pos nonnegative]

theorem physical_measurable : AEStronglyMeasurable physical (volume : Measure ℝ) := by
  have actual := (physicalSource_measurable stackedShortCurrent).restrict.piecewise (s := Ici (0 : ℝ))
    (g := fun _ => NativeUnheatedSourceGradient.physical stackedShortCurrent 0 le_rfl)
    measurableSet_Ici aestronglyMeasurable_const
  apply actual.congr
  filter_upwards with time
  by_cases nonnegative : 0 ≤ time <;> simp [physical,physicalSource,nonnegative]

theorem initial_regular : H1 (NativeUnheatedSourceGradient.physical stackedShortCurrent 0 le_rfl) := by
  change NativeUnheatedStressProduct.H1 (wholeVelocity (NativeUnifiedCompleteSource.source stackedShortCurrent 0).fst)
  rw [NativeWindowPreparedSobolevSource.initial_row]
  exact NativeWindowPreparedSobolevSource.initial_H1

theorem physical_regular_ae : ∀ᵐ time : ℝ, H1 (physical time) := by
  filter_upwards [NativeUnheatedSourceGradient.physical_H1_ae stackedShortCurrent] with time regular
  by_cases nonnegative : 0 ≤ time
  · simpa only [physical,dif_pos nonnegative] using regular nonnegative
  · simpa only [physical,dif_neg nonnegative] using initial_regular

def gradientEnvelope (time : ℝ) : ℝ :=
  if time ≤ 0 then NativeUnheatedStressProduct.gradientMass NativeWindowPreparationInitial.velocity
  else NativeUnheatedSourceGradient.mass stackedShortCurrent time

theorem gradientEnvelope_nonnegative (time : ℝ) : 0 ≤ gradientEnvelope time := by
  unfold gradientEnvelope
  split_ifs
  · exact tsum_nonneg (NativeUnheatedStressProduct.density_nonnegative _)
  · exact NativeUnheatedSourceGradient.mass_nonnegative _ _

theorem physical_mass (time : ℝ) : gradientMass (physical time) = gradientEnvelope time := by
  by_cases nonnegative : 0 ≤ time
  · simp only [physical,dif_pos nonnegative]
    rw [NativeUnheatedSourceGradient.physical_mass]
    by_cases before : time ≤ 0
    · have zero : time = 0 := le_antisymm before nonnegative
      subst time
      simp only [gradientEnvelope,le_refl,if_true,NativeWindowPreparedSobolevSource.mass_initial]
    · simp only [gradientEnvelope,if_neg before]
  · simp only [physical,dif_neg nonnegative,gradientEnvelope,if_pos (le_of_not_ge nonnegative)]
    rw [NativeUnheatedSourceGradient.physical_mass,NativeWindowPreparedSobolevSource.mass_initial]

theorem gradientEnvelope_integrable (horizon : ℝ) (nonnegative : 0 ≤ horizon) :
    IntegrableOn gradientEnvelope (Icc (-1 : ℝ) (horizon+2)) := by
  have left : IntegrableOn gradientEnvelope (Icc (-1 : ℝ) 0) := by
    have paid : IntegrableOn (fun _ : ℝ => NativeUnheatedStressProduct.gradientMass NativeWindowPreparationInitial.velocity)
        (Icc (-1 : ℝ) 0) (volume : Measure ℝ) := continuous_const.integrableOn_Icc
    exact paid.congr_fun (fun time inside => by simp only [gradientEnvelope,if_pos inside.2]) measurableSet_Icc
  have right : IntegrableOn gradientEnvelope (Icc (0 : ℝ) (horizon+2)) := by
    have paid := NativeUnheatedSourceGradient.mass_integrable stackedShortCurrent (horizon+2) (by linarith)
    apply IntegrableOn.congr_fun paid _ measurableSet_Icc
    intro time inside
    by_cases before : time ≤ 0
    · have zero : time = 0 := le_antisymm before inside.1
      subst time
      simp only [gradientEnvelope,le_refl,if_true,NativeWindowPreparedSobolevSource.mass_initial]
    · simp only [gradientEnvelope,if_neg before]
  apply (left.union right).mono_set
  intro time inside
  by_cases before : time ≤ 0
  · exact Or.inl ⟨inside.1,before⟩
  · exact Or.inr ⟨le_of_not_ge before,inside.2⟩

theorem source_bound_ae : ∀ᵐ time : ℝ, ∀ L F (test : NativeCompleteStressCarrier.Space),
    ‖work (physical time) (F∩L) F test‖ ≤ coefficient stackedShortCurrent L*‖test‖*gradientEnvelope time := by
  filter_upwards [physical_regular_ae] with time regular L F test
  have paid := work_bound (physical time) regular (F∩L) F test
  rw [gradientValue_norm_sq,physical_mass] at paid
  have amplitude : ‖(physical time).1‖ ≤ NativeUnifiedCompleteSource.budget stackedShortCurrent := by
    rw [physical_original]
    exact (WithLp.norm_fst_le _ _).trans (NativeUnifiedCompleteSource.source_bound stackedShortCurrent time)
  have caps : (∑ first ∈ F∩L,cap first) ≤ ∑ first ∈ L,cap first :=
    Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right (fun first _ _ => cap_nonnegative first)
  have cap0 : 0 ≤ ∑ first ∈ L,cap first := Finset.sum_nonneg fun first _ => cap_nonnegative first
  apply paid.trans
  calc
    _ ≤ (54*Real.sqrt NativeUnheatedRieszKernel.constant)*(∑ first ∈ L,cap first)*NativeUnifiedCompleteSource.budget stackedShortCurrent*
        ((2*Real.pi)^2*gradientEnvelope time)*‖test‖ := by
      gcongr
      exact mul_nonneg (sq_nonneg _) (gradientEnvelope_nonnegative time)
    _ = _ := by unfold coefficient; ring

def window (time : ℝ) (L F : Finset IntegerWavevector) (test : NativeCompleteStressCarrier.Space) : ℂ :=
  ∫ shift : ℝ, NativeForwardWindowSource.kernel shift • work (physical (time-shift)) (F∩L) F test

theorem work_integrable (horizon : ℝ) (nonnegative : 0 ≤ horizon) (L F : Finset IntegerWavevector)
    (test : NativeCompleteStressCarrier.Space) :
    IntegrableOn (fun sample => work (physical sample) (F∩L) F test) (Icc (-1 : ℝ) (horizon+2)) := by
  apply ((gradientEnvelope_integrable horizon nonnegative).const_mul
    (coefficient stackedShortCurrent L*‖test‖)).mono'
    ((work_continuous (F∩L) F test).comp_aestronglyMeasurable physical_measurable).restrict
  filter_upwards [ae_restrict_of_ae source_bound_ae] with sample bound
  exact bound L F test

theorem window_average (time horizon : ℝ) (inside : time ∈ Icc (-2 : ℝ) horizon)
    (L F : Finset IntegerWavevector) (test : NativeCompleteStressCarrier.Space) :
    window time L F test = NativeWindowPreparedSobolevWindow.average 0 time horizon
      (fun sample => work (physical sample) (F∩L) F test) := by
  rw [NativeWindowPreparedSobolevWindow.average_original 0 time horizon inside]
  rfl

def budget (horizon : ℝ) : ℝ := NativeWindowFiniteStressUniform.kernelBound 0*
  ∫ sample in Icc (-1 : ℝ) (horizon+2), gradientEnvelope sample

theorem budget_nonnegative (horizon : ℝ) : 0 ≤ budget horizon :=
  mul_nonneg (NativeWindowFiniteStressUniform.kernelBound_positive 0).le
    (integral_nonneg gradientEnvelope_nonnegative)

theorem window_bound (time horizon : ℝ) (nonnegative : 0 ≤ horizon) (inside : time ∈ Icc (-2 : ℝ) horizon)
    (L F : Finset IntegerWavevector) (test : NativeCompleteStressCarrier.Space) :
    ‖window time L F test‖ ≤ coefficient stackedShortCurrent L*‖test‖*budget horizon := by
  rw [window_average time horizon inside,NativeWindowPreparedSobolevWindow.average]
  have paid := norm_integral_le_of_norm_le
    (f := fun sample : ℝ => kernelJet 0 (time-sample) • work (physical sample) (F∩L) F test)
    ((gradientEnvelope_integrable horizon nonnegative).const_mul
      (coefficient stackedShortCurrent L*‖test‖*NativeWindowFiniteStressUniform.kernelBound 0)) (by
      filter_upwards [ae_restrict_of_ae source_bound_ae] with sample bound
      rw [norm_smul]
      exact (mul_le_mul (NativeWindowFiniteStressUniform.kernel_bounded 0 (time-sample)) (bound L F test)
        (norm_nonneg _) (NativeWindowFiniteStressUniform.kernelBound_positive 0).le).trans_eq (by ring))
  simpa only [integral_const_mul,budget,mul_assoc] using paid

theorem window_existing (time : ℝ) (valid : -1 ≤ time) (L F : Finset IntegerWavevector)
    (test : NativeCompleteStressCarrier.Space) :
    window time L F test = NativeWindowPressureLowSource.window stackedShortCurrent time L F test := by
  rw [window,NativeWindowPressureLowSource.window,NativeForwardWindowPairingReadout.density_integral]
  apply integral_congr_ae
  filter_upwards with shift
  by_cases zero : NativeForwardWindowSource.kernel shift = 0
  · simp only [zero,zero_smul]
  · have nonnegative : 0 ≤ time-shift := by linarith [(NativeViewPreparation.kernel_window shift zero).2]
    rw [physical_existing _ nonnegative]

end
end SaturationMonoid.NavierStokes.NativeWindowPreparedPressureSource
