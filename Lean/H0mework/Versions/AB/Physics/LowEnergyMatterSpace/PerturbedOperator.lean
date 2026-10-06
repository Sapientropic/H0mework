import H0mework.Versions.AB.Physics.LowEnergyMatterSpace.PerturbedVariation
import H0mework.Versions.AB.Physics.LowEnergyMatterSpace.PerturbedNative

/-! The same initial-data-independent remainder gives the true propagator's operator-norm derivative. -/
set_option autoImplicit false
open Set Filter Topology Asymptotics
namespace SaturationMonoid.PhysicsCore.LowEnergy.MatterSpace.Response
noncomputable section
namespace PerturbedDevelopment
variable {perturbation : ℝ → MatterL2 →L[ℂ] MatterL2}
    (development : PerturbedDevelopment perturbation)
    (continuousPerturbation : Continuous perturbation)
    (symmetric : ∀ t, IsSelfAdjoint (perturbation t))
    (time : ℝ) (inside : time ∈ Ioo (-development.radius) development.radius)

/-- A total parameter chart for differentiation at zero; its physical interval is |epsilon|≤1. -/
def couplingOperator (epsilon : ℝ) : MatterL2 →L[ℂ] MatterL2 :=
  if coupling : |epsilon|≤1 then
    development.physicalOperator symmetric epsilon coupling 0 time
      ⟨neg_lt_zero.mpr development.positive,development.positive⟩ inside
  else freeOperator time

theorem couplingOperator_apply (epsilon : ℝ) (coupling : |epsilon|≤1) (u : MatterL2) :
    development.couplingOperator symmetric time inside epsilon u=
      development.physicalCurve epsilon 0 u time := by
  rw [couplingOperator,dif_pos coupling]
  rfl

theorem couplingOperator_zero : development.couplingOperator symmetric time inside 0=freeOperator time := by
  ext u
  rw [development.couplingOperator_apply symmetric time inside 0 (by norm_num),
    development.physicalCurve_zeroCoupling symmetric 0 time
      ⟨neg_lt_zero.mpr development.positive,development.positive⟩ inside,sub_zero]
  rfl

theorem couplingOperator_remainder (epsilon : ℝ) (coupling : |epsilon|≤1) (M : ℝ)
    (bounded : ∀ s ∈ uIcc 0 time, ‖perturbation s‖≤M) :
    ‖development.couplingOperator symmetric time inside epsilon-freeOperator time-
      epsilon • firstOrderOperator perturbation continuousPerturbation time‖≤|epsilon|^2*M^2*|time|^2 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro u
  have atZero : (0 : ℝ) ∈ Ioo (-development.radius) development.radius :=
    ⟨neg_lt_zero.mpr development.positive,development.positive⟩
  have point := perturbed_quadratic_remainder perturbation continuousPerturbation symmetric epsilon
    development.radius development.positive (development.curve epsilon 0 u) u
    (development.starts epsilon 0 u coupling atZero) (development.evolves epsilon 0 u coupling atZero)
    time inside M bounded
  have transported :
      (development.couplingOperator symmetric time inside epsilon-freeOperator time-
        epsilon • firstOrderOperator perturbation continuousPerturbation time) u=
      spatialUnitary time (couplingRemainder perturbation (development.curve epsilon 0 u) u epsilon time) := by
    rw [sub_apply,sub_apply,smul_apply,
      development.couplingOperator_apply symmetric time inside epsilon coupling]
    simp only [physicalCurve,neg_zero,spatialUnitary_zero]
    change spatialUnitary time (development.curve epsilon 0 u time)-spatialUnitary time u-
      epsilon • spatialUnitary time (interactionIntegral (perturbationForce perturbation u) time)=
        spatialUnitary time (development.curve epsilon 0 u time-u-
          epsilon • interactionIntegral (perturbationForce perturbation u) time)
    simp only [map_sub,RCLike.real_smul_eq_coe_smul (K := ℂ),map_smul]
  rw [transported,spatialUnitary_norm]
  exact point

theorem couplingOperator_derivative :
    HasDerivAt (development.couplingOperator symmetric time inside)
      (firstOrderOperator perturbation continuousPerturbation time) 0 := by
  obtain ⟨M,bounded⟩ := (isCompact_uIcc : IsCompact (uIcc (0 : ℝ) time)).exists_bound_of_continuousOn
    continuousPerturbation.continuousOn
  have near : ∀ᶠ epsilon : ℝ in 𝓝 0, |epsilon|≤1 := by
    filter_upwards [Icc_mem_nhds (by norm_num : (-1 : ℝ)<0) (by norm_num : (0 : ℝ)<1)] with epsilon h
    exact abs_le.mpr h
  have quadratic : (fun epsilon : ℝ => development.couplingOperator symmetric time inside epsilon-
      freeOperator time-epsilon • firstOrderOperator perturbation continuousPerturbation time)
      =O[𝓝 0] (fun epsilon : ℝ => epsilon^2) := by
    apply IsBigO.of_bound (M^2*|time|^2)
    filter_upwards [near] with epsilon coupling
    apply (development.couplingOperator_remainder continuousPerturbation symmetric time inside epsilon coupling M bounded).trans_eq
    rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg epsilon),sq_abs]
    ring
  have little := quadratic.trans_isLittleO (isLittleO_pow_id (𝕜 := ℝ) (by norm_num : 1<2))
  rw [hasDerivAt_iff_isLittleO]
  simpa only [development.couplingOperator_zero symmetric time inside,sub_zero] using little

end PerturbedDevelopment
end
end SaturationMonoid.PhysicsCore.LowEnergy.MatterSpace.Response
