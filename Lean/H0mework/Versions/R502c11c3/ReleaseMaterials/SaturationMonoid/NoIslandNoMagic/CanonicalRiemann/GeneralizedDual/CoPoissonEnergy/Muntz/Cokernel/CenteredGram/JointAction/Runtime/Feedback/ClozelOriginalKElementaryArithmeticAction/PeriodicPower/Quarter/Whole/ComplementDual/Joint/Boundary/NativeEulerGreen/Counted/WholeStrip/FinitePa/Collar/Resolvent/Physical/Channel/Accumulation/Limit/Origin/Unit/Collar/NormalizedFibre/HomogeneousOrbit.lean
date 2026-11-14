import H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.NativeEulerGreen.Counted.WholeStrip.FinitePa.Collar.Resolvent.Physical.Channel.Accumulation.Limit.Origin.Unit.Collar.NormalizedFibre.PhysicalProjection

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalCanonicalNativeEulerGreen.Counted.WholeStrip.FinitePa.Collar.Resolvent

open Complex Filter MeasureTheory Set BurnolPhysicalState OriginalRieszSource
open scoped Topology ENNReal
attribute [local instance 1100] NormedSpace.complexToReal

open private translation_apply from
  H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Euler.Dilation.L1

local notation "L¹" => Lp ℂ 1 (volume : Measure ℝ)
local notation "S'" => TemperedDistribution ℝ ℂ
local notation "T" => coPoissonSchwartzEnergyTranslation
local notation "D" => burnolMultiplicativeDilation
local notation "raw" => fun (z : L¹ × BurnolL2) (x : ℝ) => Prod.fst z x+Prod.snd z x

/-- The two actual strong components are read in one tempered distribution. -/
def distributionOfSplit : (L¹ × BurnolL2) →L[ℂ] S' :=
  (Lp.toTemperedDistributionCLM ℂ (volume : Measure ℝ) 1).comp (ContinuousLinearMap.fst ℂ L¹ BurnolL2) +
    (Lp.toTemperedDistributionCLM ℂ (volume : Measure ℝ) 2).comp (ContinuousLinearMap.snd ℂ L¹ BurnolL2)

theorem distributionOfSplit_apply (z : L¹ × BurnolL2) (test : SchwartzMap ℝ ℂ) :
    distributionOfSplit z test = ∫ x, test x*raw z x := by
  have inside : Integrable (fun x => test x*z.1 x) volume :=
    (memLp_one_iff_integrable.mp (Lp.memLp z.1)).mul_of_top_right test.memLp_top
  have outside : Integrable (fun x => test x*z.2 x) volume :=
    (test.memLp 2).integrable_mul (Lp.memLp z.2)
  change (z.1 : S') test+(z.2 : S') test = _
  simp only [Lp.toTemperedDistribution_apply, smul_eq_mul]
  rw [← integral_add inside outside]
  apply integral_congr_ae
  filter_upwards with x
  change test x*z.1 x+test x*z.2 x = test x*(z.1 x+z.2 x)
  rw [mul_add]

private theorem split_weak_at_zero (z : L¹ × BurnolL2) (test : SchwartzMap ℝ ℂ) :
    HasDerivAt (fun h : ℝ => distributionOfSplit z (T (-h) test))
      (GapEuler.euler (distributionOfSplit z) test) 0 := by
  have inside := Dilation.integrable_weak_at_zero z.1 test
  have outside : HasDerivAt (fun h : ℝ => (z.2 : S') (T (-h) test))
      (GapEuler.euler (z.2 : S') test) 0 := by
    simpa only [OriginalRieszFiniteResponse.original_read] using Dilation.original_weak_at_zero z.2 test
  change HasDerivAt (fun h : ℝ => ((z.1 : S')+(z.2 : S')) (T (-h) test))
    (GapEuler.euler ((z.1 : S')+(z.2 : S')) test) 0
  simpa only [map_add, add_apply] using! inside.add outside

private theorem homogeneous_split_translation (z : L¹ × BurnolL2) (coefficient : ℂ)
    (law : GapEuler.euler (distributionOfSplit z)+coefficient • distributionOfSplit z = 0)
    (test : SchwartzMap ℝ ℂ) (shift : ℝ) :
    distributionOfSplit z (T (-shift) test) =
      Complex.exp (-coefficient*(shift : ℂ))*distributionOfSplit z test := by
  let read := fun h : ℝ => distributionOfSplit z (T (-h) test)
  have actual (h : ℝ) : HasDerivAt read ((0 : ℂ)-coefficient*read h) h := by
    let shiftedTest := T (-h) test
    have derivative := (split_weak_at_zero z shiftedTest).scomp_of_eq h
      ((hasDerivAt_id h).sub_const h) (by simp)
    have orbit : (fun t : ℝ => distributionOfSplit z (T (-(t-h)) shiftedTest)) = read := by
      funext t
      have composition := LinearMap.congr_fun (coPoissonSchwartzEnergyTranslation_add (-(t-h)) (-h)) test
      change T (-(t-h)) shiftedTest = T (-(t-h)+ -h) test at composition
      rw [show -(t-h)+ -h = -t by ring] at composition
      exact congrArg (distributionOfSplit z) composition
    have atTest := congrArg (fun field : S' => field shiftedTest) law
    simp only [add_apply, smul_apply, smul_eq_mul, zero_apply] at atTest
    have velocity : GapEuler.euler (distributionOfSplit z) shiftedTest =
        (0 : ℂ)-coefficient*read h := by
      change _ = (0 : ℂ)-coefficient*distributionOfSplit z shiftedTest
      linear_combination atTest
    simp only [one_smul, Function.comp_def, id_eq] at derivative
    change HasDerivAt (fun t : ℝ => distributionOfSplit z (T (-(t-h)) shiftedTest)) _ h at derivative
    rw [orbit, velocity] at derivative
    exact derivative
  have paid := _root_.OriginalRieszFiniteResponse.Integration.finite_response read
    (fun _ => (0 : ℂ)) coefficient actual continuous_const shift
  have base : read 0 = distributionOfSplit z test := by
    simp only [read, neg_zero, coPoissonSchwartzEnergyTranslation_zero]
  simpa only [base, mul_zero, intervalIntegral.integral_zero, add_zero] using paid

private theorem split_scaled_integral (z : L¹ × BurnolL2) (h : ℝ) (test : SchwartzMap ℝ ℂ) :
    (∫ x : ℝ, test x*((Real.exp (h/2) : ℂ)*raw z (Real.exp h*x))) =
      distributionOfSplit z (T (-h) test) := by
  rw [distributionOfSplit_apply]
  let integrand := fun y : ℝ => test y*raw z (Real.exp h*y)
  have source : (fun x : ℝ => T (-h) test x*raw z x) =
      fun x => (Real.exp (-h/2) : ℂ)*integrand (Real.exp (-h)*x) := by
    funext x
    rw [translation_apply]
    have inverse : Real.exp h*(Real.exp (-h)*x) = x := by
      rw [← mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_mul]
    dsimp only [integrand]
    rw [inverse]
    ring
  rw [source, integral_const_mul, Measure.integral_comp_mul_left integrand (Real.exp (-h)),
    abs_of_pos (inv_pos.mpr (Real.exp_pos _)), Real.exp_neg h, inv_inv, Complex.real_smul,
    ← mul_assoc]
  have factor : (Real.exp (-h/2) : ℂ)*(Real.exp h : ℂ) = (Real.exp (h/2) : ℂ) := by
    rw [← Complex.ofReal_mul, ← Real.exp_add]
    congr 2
    ring
  rw [factor, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with x
  dsimp only [integrand]
  ring

private theorem scaled_split_locally_integrable (z : L¹ × BurnolL2) (h : ℝ) :
    LocallyIntegrable (fun x : ℝ => (Real.exp (h/2) : ℂ)*raw z (Real.exp h*x)) volume := by
  have inside : Integrable (fun x : ℝ => (Real.exp (h/2) : ℂ)*z.1 (Real.exp h*x)) volume :=
    (((memLp_one_iff_integrable.mp (Lp.memLp z.1)).comp_mul_left' (Real.exp_ne_zero h)).const_mul _)
  have outside := (Lp.memLp (D h z.2)).locallyIntegrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  apply (inside.locallyIntegrable.add outside).congr
  filter_upwards [burnolMultiplicativeDilation_coeFn h z.2] with x actual
  change (Real.exp (h/2) : ℂ)*z.1 (Real.exp h*x)+D h z.2 x =
    (Real.exp (h/2) : ℂ)*(z.1 (Real.exp h*x)+z.2 (Real.exp h*x))
  change D h z.2 x = (Real.exp (h/2) : ℂ)*z.2 (Real.exp h*x) at actual
  rw [actual, mul_add]

/-- On the original mixed source, the Euler equation generates the literal
pointwise dilation law almost everywhere. -/
theorem homogeneous_split_raw_dilation (z : L¹ × BurnolL2) (coefficient : ℂ)
    (law : GapEuler.euler (distributionOfSplit z)+coefficient • distributionOfSplit z = 0)
    (h : ℝ) :
    ∀ᵐ x : ℝ ∂volume, (Real.exp (h/2) : ℂ)*raw z (Real.exp h*x) =
      Complex.exp (-coefficient*(h : ℂ))*raw z x := by
  have whole : LocallyIntegrable (raw z) volume :=
    ((Lp.memLp z.1).locallyIntegrable (by norm_num : (1 : ℝ≥0∞) ≤ 1)).add
      ((Lp.memLp z.2).locallyIntegrable (by norm_num : (1 : ℝ≥0∞) ≤ 2))
  have scaled : LocallyIntegrable (fun x => Complex.exp (-coefficient*(h : ℂ))*raw z x) volume := by
    simpa only [Pi.smul_apply, smul_eq_mul] using! whole.smul (Complex.exp (-coefficient*(h : ℂ)))
  apply ae_eq_of_integral_contDiff_smul_eq (scaled_split_locally_integrable z h) scaled
  intro test smooth compact
  have complexCompact : HasCompactSupport (Complex.ofRealCLM ∘ test) := compact.comp_left rfl
  have complexSmooth := Complex.ofRealCLM.contDiff.comp smooth
  let sch := complexCompact.toSchwartzMap complexSmooth
  have result := (split_scaled_integral z h sch).trans (homogeneous_split_translation z coefficient law sch h)
  rw [distributionOfSplit_apply, ← integral_const_mul] at result
  simp only [Complex.real_smul]
  refine result.trans ?_
  apply integral_congr_ae
  filter_upwards with x
  change Complex.exp (-coefficient*(h : ℂ))*((test x : ℂ)*raw z x) =
    (test x : ℂ)*(Complex.exp (-coefficient*(h : ℂ))*raw z x)
  ring

end OriginalCanonicalNativeEulerGreen.Counted.WholeStrip.FinitePa.Collar.Resolvent
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
