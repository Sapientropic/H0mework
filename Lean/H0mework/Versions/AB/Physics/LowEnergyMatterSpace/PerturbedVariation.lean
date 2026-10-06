import H0mework.Versions.AB.Physics.LowEnergyMatterSpace.PerturbedNorm
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Asymptotics.Lemmas

/-! A true interaction ODE family generates its coupling derivative, via a quadratic remainder. -/
set_option autoImplicit false
open Set Filter Topology Asymptotics
open scoped InnerProductSpace
namespace SaturationMonoid.PhysicsCore.LowEnergy.MatterSpace.Response
noncomputable section

def interactionTangent (perturbation : ℝ → MatterL2 →L[ℂ] MatterL2) (u : MatterL2) (time : ℝ) : MatterL2 :=
  interactionIntegral (perturbationForce perturbation u) time

theorem interactionTangent_zero (perturbation : ℝ → MatterL2 →L[ℂ] MatterL2) (u : MatterL2) :
    interactionTangent perturbation u 0=0 := by
  simp [interactionTangent,interactionIntegral]

theorem interactionGenerator_coupling (perturbation : ℝ → MatterL2 →L[ℂ] MatterL2)
    (epsilon time : ℝ) (v : MatterL2) :
    interactionGenerator perturbation epsilon time v=epsilon • interactionGenerator perturbation 1 time v := by
  change (-Complex.I*(epsilon : ℂ)) • heisenberg (perturbation time) time v=
    epsilon • ((-Complex.I*(1 : ℂ)) • heisenberg (perturbation time) time v)
  rw [mul_one,← smul_assoc]
  congr 1
  change -Complex.I*(epsilon : ℂ)=(epsilon : ℂ)*(-Complex.I)
  ring

theorem interactionTangent_derivative (perturbation : ℝ → MatterL2 →L[ℂ] MatterL2)
    (continuousPerturbation : Continuous perturbation) (u : MatterL2) (time : ℝ) :
    HasDerivAt (interactionTangent perturbation u) (interactionGenerator perturbation 1 time u) time := by
  have derivative := interactionIntegral_derivative (perturbationForce perturbation u)
    (perturbationForce_continuous perturbation continuousPerturbation u) time
  have same : interactionGenerator perturbation 1 time u=
      interactionForcing (perturbationForce perturbation u) time := by
    change (-Complex.I*(1 : ℂ)) • spatialUnitary (-time) (perturbation time (spatialUnitary time u))=
      spatialUnitary (-time) ((-Complex.I) • perturbation time (spatialUnitary time u))
    rw [mul_one,map_smul]
  change HasDerivAt (interactionIntegral (perturbationForce perturbation u)) _ _
  rw [same]
  exact derivative

private theorem segment_inside {delta time : ℝ} (positive : 0<delta)
    (inside : time ∈ Ioo (-delta) delta) : uIcc 0 time ⊆ Ioo (-delta) delta := by
  intro s hs
  change Min.min (0 : ℝ) time ≤ s ∧ s ≤ Max.max (0 : ℝ) time at hs
  exact ⟨lt_of_lt_of_le (lt_min (by linarith) inside.1) hs.1,
    lt_of_le_of_lt hs.2 (max_lt positive inside.2)⟩

private theorem segment_abs {time s : ℝ} (inside : s ∈ uIcc 0 time) : |s|≤|time| := by
  apply abs_le.mpr
  exact uIcc_subset_Icc ⟨neg_nonpos.mpr (abs_nonneg time),abs_nonneg time⟩
    ⟨neg_abs_le time,le_abs_self time⟩ inside

theorem perturbed_deviation_bound (perturbation : ℝ → MatterL2 →L[ℂ] MatterL2)
    (symmetric : ∀ time, IsSelfAdjoint (perturbation time))
    (epsilon delta : ℝ) (positive : 0<delta) (curve : ℝ → MatterL2) (u : MatterL2)
    (starts : curve 0=u)
    (evolves : ∀ s ∈ Ioo (-delta) delta,
      HasDerivAt curve (interactionGenerator perturbation epsilon s (curve s)) s)
    (time : ℝ) (inside : time ∈ Ioo (-delta) delta) (M : ℝ)
    (bounded : ∀ s ∈ uIcc 0 time, ‖perturbation s‖≤M)
    (s : ℝ) (onSegment : s ∈ uIcc 0 time) :
    ‖curve s-u‖≤(|epsilon| *M*‖u‖)*|s| := by
  have zeroInside : (0 : ℝ) ∈ Ioo (-delta) delta := ⟨by linarith,positive⟩
  have derivative (r : ℝ) (hr : r ∈ uIcc 0 time) :
      HasDerivWithinAt curve (interactionGenerator perturbation epsilon r (curve r)) (uIcc 0 time) r :=
    (evolves r (segment_inside positive inside hr)).hasDerivWithinAt
  have estimate (r : ℝ) (hr : r ∈ uIcc 0 time) :
      ‖interactionGenerator perturbation epsilon r (curve r)‖≤|epsilon| *M*‖u‖ := by
    have conserved := perturbed_curve_norm perturbation symmetric epsilon delta curve evolves r 0
      (segment_inside positive inside hr) zeroInside
    rw [starts] at conserved
    apply (interactionGenerator_bound perturbation epsilon r (curve r)).trans
    rw [conserved]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (bounded r hr) (abs_nonneg epsilon)) (norm_nonneg u)
  have result := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le derivative estimate
    (convex_uIcc (0 : ℝ) time) left_mem_uIcc onSegment
  simpa only [starts,sub_zero,Real.norm_eq_abs] using result

def couplingRemainder (perturbation : ℝ → MatterL2 →L[ℂ] MatterL2)
    (curve : ℝ → MatterL2) (u : MatterL2) (epsilon time : ℝ) : MatterL2 :=
  curve time-u-epsilon • interactionTangent perturbation u time

theorem couplingRemainder_derivative (perturbation : ℝ → MatterL2 →L[ℂ] MatterL2)
    (continuousPerturbation : Continuous perturbation) (curve : ℝ → MatterL2)
    (u : MatterL2) (epsilon time : ℝ)
    (evolves : HasDerivAt curve (interactionGenerator perturbation epsilon time (curve time)) time) :
    HasDerivAt (couplingRemainder perturbation curve u epsilon)
      (interactionGenerator perturbation epsilon time (curve time-u)) time := by
  have derivative := (evolves.sub_const u).sub
    ((interactionTangent_derivative perturbation continuousPerturbation u time).const_smul epsilon)
  convert! derivative using 1
  rw [map_sub,interactionGenerator_coupling perturbation epsilon time u]

theorem perturbed_quadratic_remainder (perturbation : ℝ → MatterL2 →L[ℂ] MatterL2)
    (continuousPerturbation : Continuous perturbation)
    (symmetric : ∀ time, IsSelfAdjoint (perturbation time))
    (epsilon delta : ℝ) (positive : 0<delta) (curve : ℝ → MatterL2) (u : MatterL2)
    (starts : curve 0=u)
    (evolves : ∀ s ∈ Ioo (-delta) delta,
      HasDerivAt curve (interactionGenerator perturbation epsilon s (curve s)) s)
    (time : ℝ) (inside : time ∈ Ioo (-delta) delta) (M : ℝ)
    (bounded : ∀ s ∈ uIcc 0 time, ‖perturbation s‖≤M) :
    ‖couplingRemainder perturbation curve u epsilon time‖≤|epsilon|^2*M^2*|time|^2*‖u‖ := by
  have nonnegative : 0≤M := (norm_nonneg (perturbation 0)).trans (bounded 0 left_mem_uIcc)
  have derivative (r : ℝ) (hr : r ∈ uIcc 0 time) :
      HasDerivWithinAt (couplingRemainder perturbation curve u epsilon)
        (interactionGenerator perturbation epsilon r (curve r-u)) (uIcc 0 time) r :=
    (couplingRemainder_derivative perturbation continuousPerturbation curve u epsilon r
      (evolves r (segment_inside positive inside hr))).hasDerivWithinAt
  have estimate (r : ℝ) (hr : r ∈ uIcc 0 time) :
      ‖interactionGenerator perturbation epsilon r (curve r-u)‖≤|epsilon|^2*M^2*|time| *‖u‖ := by
    have difference := perturbed_deviation_bound perturbation symmetric epsilon delta positive curve u starts evolves
      time inside M bounded r hr
    have coefficient : 0≤|epsilon| *M := mul_nonneg (abs_nonneg epsilon) nonnegative
    calc
      _≤(|epsilon| *M)*‖curve r-u‖ :=
        (interactionGenerator_bound perturbation epsilon r (curve r-u)).trans
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (bounded r hr) (abs_nonneg epsilon)) (norm_nonneg _))
      _≤(|epsilon| *M)*((|epsilon| *M*‖u‖)*|r|) := mul_le_mul_of_nonneg_left difference coefficient
      _≤(|epsilon| *M)*((|epsilon| *M*‖u‖)*|time|) := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (segment_abs hr) (mul_nonneg coefficient (norm_nonneg u))) coefficient
      _=_ := by ring
  have result := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le derivative estimate
    (convex_uIcc (0 : ℝ) time) left_mem_uIcc right_mem_uIcc
  have zero : couplingRemainder perturbation curve u epsilon 0=0 := by
    rw [couplingRemainder,starts,interactionTangent_zero,sub_self,smul_zero,sub_zero]
  rw [zero,sub_zero,sub_zero,Real.norm_eq_abs] at result
  exact result.trans_eq (by ring)

theorem true_family_interaction_derivative (perturbation : ℝ → MatterL2 →L[ℂ] MatterL2)
    (continuousPerturbation : Continuous perturbation)
    (symmetric : ∀ time, IsSelfAdjoint (perturbation time))
    (delta : ℝ) (positive : 0<delta) (family : ℝ → ℝ → MatterL2) (u : MatterL2)
    (starts : ∀ epsilon, |epsilon|≤1 → family epsilon 0=u)
    (evolves : ∀ epsilon, |epsilon|≤1 → ∀ s ∈ Ioo (-delta) delta,
      HasDerivAt (family epsilon) (interactionGenerator perturbation epsilon s (family epsilon s)) s)
    (time : ℝ) (inside : time ∈ Ioo (-delta) delta) :
    HasDerivAt (fun epsilon : ℝ => family epsilon time) (interactionTangent perturbation u time) 0 := by
  obtain ⟨M,bounded⟩ := (isCompact_uIcc : IsCompact (uIcc (0 : ℝ) time)).exists_bound_of_continuousOn
    continuousPerturbation.continuousOn
  have zeroCoupling : |(0 : ℝ)|≤1 := by norm_num
  have atZero : family 0 time=u := by
    have bound := perturbed_deviation_bound perturbation symmetric 0 delta positive (family 0) u
      (starts 0 zeroCoupling) (evolves 0 zeroCoupling) time inside M bounded time right_mem_uIcc
    have zero : ‖family 0 time-u‖=0 := le_antisymm (by simpa using bound) (norm_nonneg _)
    exact sub_eq_zero.mp (norm_eq_zero.mp zero)
  have near : ∀ᶠ epsilon : ℝ in 𝓝 0, |epsilon|≤1 := by
    filter_upwards [Icc_mem_nhds (by norm_num : (-1 : ℝ)<0) (by norm_num : (0 : ℝ)<1)] with epsilon h
    exact abs_le.mpr h
  have quadratic : (fun epsilon : ℝ => couplingRemainder perturbation (family epsilon) u epsilon time)
      =O[𝓝 0] (fun epsilon : ℝ => epsilon^2) := by
    apply IsBigO.of_bound (M^2*|time|^2*‖u‖)
    filter_upwards [near] with epsilon coupling
    have bound := perturbed_quadratic_remainder perturbation continuousPerturbation symmetric epsilon delta positive
      (family epsilon) u (starts epsilon coupling) (evolves epsilon coupling) time inside M bounded
    apply bound.trans_eq
    rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg epsilon),sq_abs]
    ring
  have little := quadratic.trans_isLittleO (isLittleO_pow_id (𝕜 := ℝ) (by norm_num : 1<2))
  rw [hasDerivAt_iff_isLittleO]
  simpa only [atZero,sub_zero,couplingRemainder] using little

theorem true_family_physical_derivative (perturbation : ℝ → MatterL2 →L[ℂ] MatterL2)
    (continuousPerturbation : Continuous perturbation)
    (symmetric : ∀ time, IsSelfAdjoint (perturbation time))
    (delta : ℝ) (positive : 0<delta) (family : ℝ → ℝ → MatterL2) (u : MatterL2)
    (starts : ∀ epsilon, |epsilon|≤1 → family epsilon 0=u)
    (evolves : ∀ epsilon, |epsilon|≤1 → ∀ s ∈ Ioo (-delta) delta,
      HasDerivAt (family epsilon) (interactionGenerator perturbation epsilon s (family epsilon s)) s)
    (time : ℝ) (inside : time ∈ Ioo (-delta) delta) :
    HasDerivAt (fun epsilon : ℝ => spatialUnitary time (family epsilon time))
      (firstOrder perturbation time u) 0 := by
  have derivative := true_family_interaction_derivative perturbation continuousPerturbation symmetric
    delta positive family u starts evolves time inside
  let transport := (spatialUnitary time).toContinuousLinearEquiv.toContinuousLinearMap.restrictScalars ℝ
  have physical := transport.hasFDerivAt.comp_hasDerivAt 0 derivative
  convert! physical using 1

end
end SaturationMonoid.PhysicsCore.LowEnergy.MatterSpace.Response
