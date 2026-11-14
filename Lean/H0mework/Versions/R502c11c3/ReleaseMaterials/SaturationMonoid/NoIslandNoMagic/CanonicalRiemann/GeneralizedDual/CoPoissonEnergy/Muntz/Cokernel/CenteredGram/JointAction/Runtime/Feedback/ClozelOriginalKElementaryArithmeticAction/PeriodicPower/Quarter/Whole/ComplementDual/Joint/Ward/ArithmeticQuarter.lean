import H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.Top.Current
import H0mework.Versions.R502c11c3.Arithmetic.RiemannGraph.History.PrimePower.Factorization.Responsibility.LivingLawCanonicalRiemannPrimeExponentPoleReceiptRelationConsumer
import H0mework.Versions.R7e4da746.Arithmetic.BurnolPhysical.QuarterMellinAdditiveRechartAlgebra

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 3600000

noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Ward
open Complex Filter MeasureTheory Set BurnolPhysicalState
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.Top.Current OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.Prices
open AllPlace.WeilQuadratic.Runtime.MuntzGraph.Conductor.History.PrimePowerCurrent
open scoped Topology InnerProductSpace ENNReal
open private integrableOn_exp_weight_iff from
  H0mework.Versions.R7e4da746.Arithmetic.BurnolPhysical.QuarterMellinAdditiveEvenRechart
open private mellin_source_ae from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.UnitMellin.ResolventSource
open private outgoing_even from H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Ward.ActedSchur
local notation "order" => generatedRiemannXiZeroOrder ActualAnalyticOwner
local notation "bare" => generatedRiemannBareZeroLocalizedSpectrum ActualAnalyticOwner

def nativeReciprocalSquareRaw (v : BurnolL2) : ClozelPositiveMellinFunction :=
  fun t => 2 * (t.1 : ℂ)^(-(1/2 : ℂ)) * v (t.1 ^ (-(1/2 : ℝ)))

private def nativePositiveHalfDensity (v : BurnolL2) (x : ℝ) : ℂ :=
  (Real.exp (x/2) : ℂ) * v (Real.exp x)

private theorem half_density_memLp (v : BurnolL2) :
    MemLp (nativePositiveHalfDensity v) 2 volume := by
  have measured : Measurable (nativePositiveHalfDensity v) := by
    exact ((Complex.measurable_ofReal.comp (Real.measurable_exp.comp
      (measurable_id.div_const 2))).mul
      ((Lp.stronglyMeasurable v).measurable.comp Real.measurable_exp))
  rw [memLp_two_iff_integrable_sq_norm measured.aestronglyMeasurable]
  have source : IntegrableOn (fun t : ℝ => ‖v t‖^2) (Ioi 0) :=
    ((memLp_two_iff_integrable_sq_norm (Lp.memLp v).1).mp
      (Lp.memLp v)).mono_measure Measure.restrict_le_self
  have generated := (integrableOn_exp_weight_iff (fun t : ℝ => ‖v t‖^2)).mp source
  apply generated.congr
  filter_upwards [] with x
  simp only [nativePositiveHalfDensity, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg (Real.exp_pos _).le, mul_pow]
  have weight : Real.exp (x / 2)^2 = Real.exp x := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  rw [weight]

private theorem reciprocal_log_read (v : BurnolL2) (x : ℝ) :
    positiveMellinLogQuarterTransform (nativeReciprocalSquareRaw v) x =
      2 * nativePositiveHalfDensity v (-x/2) := by
  change (Real.exp (x/4) : ℂ) *
    (2 * (Real.exp x : ℂ)^(-(1/2 : ℂ)) * v ((Real.exp x)^(-(1/2 : ℝ)))) = _
  rw [complexExp_cpow_neg_half]
  have power : (Real.exp x)^(-(1/2 : ℝ)) = Real.exp (-x/2) := by
    rw [Real.rpow_def_of_pos (Real.exp_pos x), Real.log_exp]
    congr 1
    ring
  rw [power]
  have weight : (Real.exp (x/4) : ℂ) * (Real.exp (-x/2) : ℂ) =
      (Real.exp ((-x/2)/2) : ℂ) := by
    rw [← ofReal_mul, ← Real.exp_add]
    congr 2
    ring
  unfold nativePositiveHalfDensity
  calc
    _ = 2 * ((Real.exp (x/4) : ℂ) * (Real.exp (-x/2) : ℂ)) * v (Real.exp (-x/2)) := by ring
    _ = _ := by rw [weight]; ring

private theorem reciprocal_quarter_L2 (v : BurnolL2) :
    nativeReciprocalSquareRaw v ∈ positiveMellinQuarterL2Submodule := by
  have source := half_density_memLp v
  have qmp : Measure.QuasiMeasurePreserving (fun x : ℝ => (-(1/2 : ℝ)) * x) volume volume := by
    simpa only [smul_eq_mul] using
      (Measure.quasiMeasurePreserving_smul (μ := (volume : Measure ℝ))
        (r := (-(1/2 : ℝ))) (by norm_num))
  have measured : AEStronglyMeasurable
      (fun x : ℝ => (2 : ℂ) * nativePositiveHalfDensity v ((-(1/2 : ℝ)) * x)) volume :=
    (source.1.comp_quasiMeasurePreserving qmp).const_mul 2
  have squared : Integrable (fun x : ℝ => ‖nativePositiveHalfDensity v x‖^2) :=
    (memLp_two_iff_integrable_sq_norm source.1).mp source
  have scaled := (squared.comp_mul_left' (show (-(1/2 : ℝ)) ≠ 0 by norm_num)).const_mul (4 : ℝ)
  have generated : MemLp (fun x : ℝ => (2 : ℂ) * nativePositiveHalfDensity v ((-(1/2 : ℝ)) * x)) 2 volume := by
    rw [memLp_two_iff_integrable_sq_norm measured]
    exact scaled.congr (ae_of_all _ fun x => by norm_num [mul_pow])
  apply generated.ae_eq
  exact ae_of_all _ fun x => by
    simpa only [show (-(1/2 : ℝ)) * x = -x/2 by ring] using (reciprocal_log_read v x).symm

private theorem reciprocal_hasMellin (v : BurnolL2) (z value : ℂ)
    (source : HasMellin (v : ℝ → ℂ) (1 - 2*z) value) :
    HasMellin (positiveMellinExtension (nativeReciprocalSquareRaw v)) z (4 * value) := by
  have composed : MellinConvergent (fun t : ℝ => v (t ^ (-(1/2 : ℝ)))) (z - 1/2) := by
    apply (MellinConvergent.comp_rpow (s := z - 1/2)
      (a := (-(1/2 : ℝ))) (by norm_num)).2
    convert source.1 using 1
    push_cast
    ring
  have weighted : MellinConvergent
      (fun t : ℝ => (t : ℂ)^(-(1/2 : ℂ)) • v (t ^ (-(1/2 : ℝ)))) z := by
    apply MellinConvergent.cpow_smul.mpr
    convert composed using 1
    ring
  have analytic : HasMellin
      (fun t : ℝ => (2 : ℂ) • ((t : ℂ)^(-(1/2 : ℂ)) • v (t ^ (-(1/2 : ℝ))))) z (4 * value) := by
    refine ⟨weighted.const_smul 2, ?_⟩
    rw [mellin_const_smul, mellin_cpow_smul, mellin_comp_rpow]
    push_cast
    rw [show (z + -(1/2 : ℂ)) / (-(1/2 : ℂ)) = 1 - 2*z by ring, source.2]
    norm_num [smul_eq_mul]
    ring
  apply mellin_source_ae _ _ z _ _ analytic
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t positive
  change (if ht : 0 < t then nativeReciprocalSquareRaw v ⟨t, ht⟩ else 0) =
    (2 : ℂ) * ((t : ℂ)^(-(1/2 : ℂ)) * v (t^(-(1/2 : ℝ))))
  rw [dif_pos (show 0 < t from positive)]
  dsimp only [nativeReciprocalSquareRaw]
  ring


/-- This source is the acted wm, with its true top Mellin value. -/
def nativeTopQuarterTest (c : BurnolCompletedMellinCoordinate) (zero : riemannZeta c.value = 0) :
    QuarterMellinL2Test (c.value / 2) :=
  ⟨nativeReciprocalSquareRaw (nativeOutgoingCotest c (order c.value)),
    reciprocal_quarter_L2 _, (reciprocal_hasMellin _ (c.value/2) _ (by
      rw [show 1 - 2*(c.value/2) = 1 - c.value by ring]
      exact actual_native_top_hasMellin c zero)).1⟩

theorem actual_native_top_quarter_read (c : BurnolCompletedMellinCoordinate)
    (zero : riemannZeta c.value = 0) :
    quarterMellinL2Functional (c.value/2) (nativeTopQuarterTest c zero) =
      4 * ((2 : ℂ)^(order c.value) * bare c.value c.value *
        burnolAmbientCompletedMellinEvaluator c (physicalCotest c : BurnolL2)) := by
  exact (reciprocal_hasMellin _ (c.value/2) _ (by
    rw [show 1 - 2*(c.value/2) = 1 - c.value by ring]
    exact actual_native_top_hasMellin c zero)).2

private theorem native_top_rechart_raw (c : BurnolCompletedMellinCoordinate)
    (zero : riemannZeta c.value = 0) {x : ℝ} (nonzero : x ≠ 0) :
    quarterMellinAdditiveEvenRechartRaw (nativeTopQuarterTest c zero) x =
      (nativeOutgoingCotest c (order c.value)) |x| := by
  have positive : 0 < |x| := abs_pos.mpr nonzero
  have argument : (|x| ^ (-2 : ℝ)) ^ (-(1/2 : ℝ)) = |x| := by
    rw [← Real.rpow_mul positive.le, show (-2 : ℝ) * -(1/2) = 1 by norm_num, Real.rpow_one]
  change (1/2 : ℂ) * (((|x| : ℝ) : ℂ)^(-(1 : ℂ)) *
    positiveMellinExtension (nativeReciprocalSquareRaw (nativeOutgoingCotest c (order c.value)))
      (|x|^(-2 : ℝ))) = _
  have sourceRead : positiveMellinExtension
      (nativeReciprocalSquareRaw (nativeOutgoingCotest c (order c.value))) (|x|^(-2 : ℝ)) =
      2 * (((Real.rpow |x| (-2) : ℝ) : ℂ)^(-(1/2 : ℂ))) *
        (nativeOutgoingCotest c (order c.value)) ((|x|^(-2 : ℝ))^(-(1/2 : ℝ))) := by
    change (if ht : 0 < |x|^(-2 : ℝ) then
      nativeReciprocalSquareRaw (nativeOutgoingCotest c (order c.value)) ⟨_, ht⟩ else 0) = _
    rw [dif_pos (Real.rpow_pos_of_pos positive _)]
    rfl
  have power : (((Real.rpow |x| (-2) : ℝ) : ℂ)^(-(1/2 : ℂ))) = ((|x| : ℝ) : ℂ) := by
    have castPower := (Complex.ofReal_cpow
      (Real.rpow_pos_of_pos positive (-2 : ℝ)).le (-(1/2 : ℝ))).symm
    have castArgument : ((Real.rpow (Real.rpow |x| (-2)) (-(1/2)) : ℝ) : ℂ) = ((|x| : ℝ) : ℂ) :=
      congrArg Complex.ofReal argument
    convert castPower.trans castArgument using 1
    norm_num
  rw [sourceRead, power, argument, Complex.cpow_neg, Complex.cpow_one]
  have castNonzero : ((|x| : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr positive.ne'
  field_simp

/-- The whole additive image is wm itself, before physical projection. -/
theorem actual_native_top_rechart (c : BurnolCompletedMellinCoordinate)
    (zero : riemannZeta c.value = 0) :
    quarterMellinAdditiveEvenRechart (nativeTopQuarterTest c zero) =
      nativeOutgoingCotest c (order c.value) := by
  have even := outgoing_even c zero (order c.value)
  have negativeRead := Lp.coeFn_compMeasurePreserving
    (nativeOutgoingCotest c (order c.value)) negMeasurePreserving
  change (reflectL2 (nativeOutgoingCotest c (order c.value)) : ℝ → ℂ) =ᵐ[volume]
    (fun x : ℝ => (nativeOutgoingCotest c (order c.value)) (-x)) at negativeRead
  rw [even] at negativeRead
  apply Lp.ext
  filter_upwards [quarterMellinAdditiveEvenRechart_coeFn (nativeTopQuarterTest c zero),
    negativeRead, volume.ae_ne (0 : ℝ)] with x sourceRead negative nonzero
  rw [sourceRead, native_top_rechart_raw c zero nonzero]
  by_cases positive : 0 ≤ x
  · rw [abs_of_nonneg positive]
  · rw [abs_of_neg (lt_of_not_ge positive)]
    exact negative.symm

/-- The actual arithmetic carrier acts on wm, retaining its full quarter source. -/
def nativeTopArithmeticTest (c : BurnolCompletedMellinCoordinate)
    (zero : riemannZeta c.value = 0) :
    PrimeExponentFactorizationCarrier →ₗ[ℤ] QuarterMellinL2Test (c.value/2) :=
  primeExponentPoleQuarterTestMap (c.value/2) (nativeTopQuarterTest c zero)

theorem actual_native_arithmetic_boundary (c : BurnolCompletedMellinCoordinate)
    (zero : riemannZeta c.value = 0) (index : ConductorPrimePowerIndex) :
    nativeTopArithmeticTest c zero (factorizationBoundaryValue index) =
      nativeTopQuarterTest c zero - quarterDilationTestAction (c.value/2)
        (Character.GlobalCoPoissonCurrent.scaleSquare
          (ThetaJRoleRepresentation.primePowerUnit index.1 index.2.1))
        (Character.GlobalCoPoissonCurrent.scaleSquare_pos _) (nativeTopQuarterTest c zero) := by
  rw [nativeTopArithmeticTest, factorizationBoundaryValue, map_sub,
    primeExponentPoleQuarterTestMap_single, primeExponentPoleQuarterTestMap_single,
    one_smul, one_smul, primeExponentScale_primePower, primeExponentScale_zero]
  have scaleOne : Character.GlobalCoPoissonCurrent.scaleSquare (1 : Units NNReal) = 1 := by
    simp [Character.GlobalCoPoissonCurrent.scaleSquare, ThetaJRoleRepresentation.scaleValue]
  simp only [scaleOne]
  have identity := LinearMap.congr_fun (quarterDilationTestAction_one (c.value/2)) (nativeTopQuarterTest c zero)
  simpa only [LinearMap.id_apply] using congrArg (fun value => value - quarterDilationTestAction (c.value/2)
    (Character.GlobalCoPoissonCurrent.scaleSquare (ThetaJRoleRepresentation.primePowerUnit index.1 index.2.1))
    (Character.GlobalCoPoissonCurrent.scaleSquare_pos _) (nativeTopQuarterTest c zero)) identity

/-- The same actual spectral-state consumer reads every complete arithmetic wm source; vertical stays present. -/
theorem actual_native_arithmetic_three_faces (c : BurnolCompletedMellinCoordinate)
    (zero : riemannZeta c.value = 0) (event : PrimeExponentFactorizationCarrier) :
    quarterMellinL2Functional (c.value/2) (nativeTopArithmeticTest c zero event) =
      inner ℂ (selectedPrimeExponentPoleRootSpectralState (burnolPaZeroObservation c zero)
        (burnolPaZeroObservation_nontrivial c zero)).fst
          (quarterMellinL2Feature (c.value/2) (nativeTopArithmeticTest c zero event)) +
      inner ℂ (selectedPrimeExponentPoleRootSpectralState (burnolPaZeroObservation c zero)
        (burnolPaZeroObservation_nontrivial c zero)).snd
          (quarterMellinL2Functional (c.value/2) (nativeTopArithmeticTest c zero event)) :=
  selectedPrimeExponentPoleRootState_quarterTest_verticalSplit
    (burnolPaZeroObservation c zero) (burnolPaZeroObservation_nontrivial c zero)
    (nativeTopArithmeticTest c zero event)

/-- Its retained value is the original prime incidence multiplied by the true acted top, without normalization. -/
theorem actual_native_arithmetic_boundary_retained (c : BurnolCompletedMellinCoordinate)
    (zero : riemannZeta c.value = 0) (index : ConductorPrimePowerIndex) :
    quarterMellinL2Functional (c.value/2)
        (nativeTopArithmeticTest c zero (factorizationBoundaryValue index)) =
      (4 * ((2 : ℂ)^(order c.value) * bare c.value c.value *
        burnolAmbientCompletedMellinEvaluator c (physicalCotest c : BurnolL2))) *
      selectedPrimeExponentPoleMellinMap (burnolPaZeroObservation c zero)
        (burnolPaZeroObservation_nontrivial c zero) (factorizationBoundaryValue index) := by
  rw [actual_native_arithmetic_boundary, map_sub]
  have action := LinearMap.congr_fun (quarterDilationFunctional_eigenlaw (c.value/2)
    (Character.GlobalCoPoissonCurrent.scaleSquare (ThetaJRoleRepresentation.primePowerUnit index.1 index.2.1))
    (Character.GlobalCoPoissonCurrent.scaleSquare_pos _)) (nativeTopQuarterTest c zero)
  change quarterMellinL2Functional (c.value/2) (quarterDilationTestAction (c.value/2)
      (Character.GlobalCoPoissonCurrent.scaleSquare (ThetaJRoleRepresentation.primePowerUnit index.1 index.2.1))
      (Character.GlobalCoPoissonCurrent.scaleSquare_pos _) (nativeTopQuarterTest c zero)) =
    ((Character.GlobalCoPoissonCurrent.scaleSquare (ThetaJRoleRepresentation.primePowerUnit index.1 index.2.1) : ℂ)^((1/4 : ℂ) - c.value/2)) •
      quarterMellinL2Functional (c.value/2) (nativeTopQuarterTest c zero) at action
  rw [action, actual_native_top_quarter_read, selectedPrimeExponentPoleMellin_boundaryValue]
  change _ = _ * (1 - (Character.GlobalCoPoissonCurrent.scaleSquare
    (ThetaJRoleRepresentation.primePowerUnit index.1 index.2.1) : ℂ)^((1/4 : ℂ) - c.value/2))
  simp only [smul_eq_mul]
  ring

end OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Ward
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
