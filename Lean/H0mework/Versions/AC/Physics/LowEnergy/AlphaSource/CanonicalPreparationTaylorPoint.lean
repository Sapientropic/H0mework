import H0mework.Versions.AC.Physics.LowEnergy.AlphaSource.CanonicalPreparationTaylorTimeJets
import Mathlib.Analysis.Calculus.TaylorIntegral
import Mathlib.Analysis.Calculus.ContDiff.Deriv

set_option autoImplicit false
set_option maxHeartbeats 240000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumTaylor
open PreparationVacuumWeyl PreparationVacuumWeylDecay PreparationVacuumFourierJets
open PreparationVacuumRemainder CanonicalPreparationSquareCutoff
open MeasureTheory Filter
open scoped ContDiff Topology FourierTransform RealInnerProductSpace
attribute [local irreducible] partialFourier symbolSlice

theorem shiftedFactor_smooth (p v k : PhysicalMomentum) : ContDiff ℝ ∞ (shiftedFactor p v k) := by
  have curve : ContDiff ℝ ∞ (fun t : ℝ => p+t • v) :=
    contDiff_const.add (contDiff_id.smul contDiff_const)
  exact (partialFourier_momentum_smooth k).comp curve

theorem compositionIntegrand_time_smooth (z p : PhysicalMomentum)
    (w : PhysicalMomentum × PhysicalMomentum) : ContDiff ℝ ∞ (fun t : ℝ => compositionIntegrand t z p w) := by
  have source := ((shiftedFactor_smooth p (Real.pi • w.2) w.1).mul
    (shiftedFactor_smooth p (-Real.pi • w.1) w.2)).const_smul (𝐞 ⟪z,w.1+w.2⟫ : ℂ)
  simpa only [compositionIntegrand,shiftedFactor,Circle.smul_def,smul_neg,smul_smul,
    neg_smul,sub_eq_add_neg,Pi.smul_apply,Pi.mul_apply] using! source

theorem compositionIntegrand_deriv (z p : PhysicalMomentum) (w : PhysicalMomentum × PhysicalMomentum) :
    deriv (fun t : ℝ => compositionIntegrand t z p w)=(fun t => compositionFirstIntegrand t z p w) := by
  funext t
  exact (compositionIntegrand_hasDerivAt t z p w).deriv

theorem compositionFirstIntegrand_deriv (z p : PhysicalMomentum) (w : PhysicalMomentum × PhysicalMomentum) :
    deriv (fun t : ℝ => compositionFirstIntegrand t z p w)=(fun t => compositionSecondIntegrand t z p w) := by
  funext t
  exact (compositionFirstIntegrand_hasDerivAt t z p w).deriv

theorem compositionFirstIntegrand_time_smooth (z p : PhysicalMomentum)
    (w : PhysicalMomentum × PhysicalMomentum) : ContDiff ℝ ∞ (fun t => compositionFirstIntegrand t z p w) := by
  rw [←compositionIntegrand_deriv]
  exact (contDiff_infty_iff_deriv.mp (compositionIntegrand_time_smooth z p w)).2

theorem compositionSecondIntegrand_continuous (z p : PhysicalMomentum)
    (w : PhysicalMomentum × PhysicalMomentum) : Continuous (fun t => compositionSecondIntegrand t z p w) := by
  rw [←compositionFirstIntegrand_deriv]
  exact (compositionFirstIntegrand_time_smooth z p w).continuous_deriv (by simp)

theorem compositionSecondIntegrand_interval_integrable (z p : PhysicalMomentum)
    (w : PhysicalMomentum × PhysicalMomentum) :
    IntervalIntegrable (fun t : ℝ => (1-t) • compositionSecondIntegrand t z p w) volume 0 1 :=
  ((continuous_const.sub continuous_id).smul (compositionSecondIntegrand_continuous z p w)).intervalIntegrable _ _

def pointSecondRemainder (z p : PhysicalMomentum) (w : PhysicalMomentum × PhysicalMomentum) : ℂ :=
  ∫ t in (0 : ℝ)..1,(1-t) • compositionSecondIntegrand t z p w

theorem composition_point_Taylor (z p : PhysicalMomentum) (w : PhysicalMomentum × PhysicalMomentum) :
    compositionIntegrand 1 z p w-compositionIntegrand 0 z p w-compositionFirstIntegrand 0 z p w=
      pointSecondRemainder z p w := by
  have smooth : ContDiff ℝ 2 (fun t : ℝ => compositionIntegrand t z p w) :=
    (compositionIntegrand_time_smooth z p w).of_le
      (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞)≤⊤))
  have taylor := map_add_eq_sum_add_integral_iteratedFDeriv
    (f := fun t : ℝ => compositionIntegrand t z p w) (x := 0) (y := 1) (n := 1)
    (fun t _ => smooth.contDiffAt)
  have second : iteratedDeriv 2 (fun t : ℝ => compositionIntegrand t z p w)=
      (fun t => compositionSecondIntegrand t z p w) := by
    simp only [iteratedDeriv_succ,iteratedDeriv_zero,compositionIntegrand_deriv,compositionFirstIntegrand_deriv]
  simp only [zero_add,smul_eq_mul,mul_one,←iteratedDeriv_eq_iteratedFDeriv,
    Finset.sum_range_succ,Finset.sum_range_zero,zero_add,Nat.factorial_zero,Nat.factorial_one,
    Nat.cast_one,inv_one,one_smul,pow_one,iteratedDeriv_zero,iteratedDeriv_one,
    compositionIntegrand_deriv,second] at taylor
  change compositionIntegrand 1 z p w=
    compositionIntegrand 0 z p w+compositionFirstIntegrand 0 z p w+pointSecondRemainder z p w at taylor
  linear_combination taylor

theorem compositionFirstIntegrand_zero_antisymmetric (z p : PhysicalMomentum)
    (xi eta : PhysicalMomentum) :
    compositionFirstIntegrand 0 z p (eta,xi) = -compositionFirstIntegrand 0 z p (xi,eta) := by
  simp only [compositionFirstIntegrand,shiftedFirst,shiftedFactor,zero_smul,add_zero,
    add_comm eta xi,neg_smul,map_neg,Circle.smul_def,smul_eq_mul]
  ring

theorem shiftedFirst_source_integral (p v k : PhysicalMomentum) (t : ℝ) :
    shiftedFirst p v k t=∫ x : PhysicalMomentum,𝐞 (-⟪x,k⟫) •
      fderiv ℝ (fun q : PhysicalMomentum => symbolSlice q x) (p+t • v) v :=
  original_partialFourier_first_derivative _ _ _

theorem shiftedSecond_source_integral (p v k : PhysicalMomentum) (t : ℝ) :
    shiftedSecond p v k t=∫ x : PhysicalMomentum,𝐞 (-⟪x,k⟫) •
      fderiv ℝ (fderiv ℝ (fun q : PhysicalMomentum => symbolSlice q x)) (p+t • v) v v :=
  original_partialFourier_second_derivative _ _ _ _

end LowEnergy.PreparationVacuumTaylor
