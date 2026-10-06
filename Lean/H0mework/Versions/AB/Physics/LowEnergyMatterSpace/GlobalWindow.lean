import H0mework.Versions.AB.Physics.LowEnergyMatterSpace.GlobalRadial

/-! The source norm invariant removes the local Picard duration restriction on every finite interval. -/
set_option autoImplicit false
open Set Metric
open scoped NNReal
namespace SaturationMonoid.PhysicsCore.LowEnergy.MatterSpace.Response
noncomputable section

theorem perturbed_finite_interval_exists (perturbation : ℝ → MatterL2 →L[ℂ] MatterL2)
    (continuousPerturbation : Continuous perturbation)
    (symmetric : ∀ t, IsSelfAdjoint (perturbation t))
    (epsilon radius start : ℝ) (positive : 0<radius) (located : start ∈ Ioo (-radius) radius)
    (initial : MatterL2) :
    ∃ curve : ℝ → MatterL2, curve start=initial ∧
      ∀ t ∈ Ioo (-radius) radius,
        HasDerivAt curve (interactionGenerator perturbation epsilon t (curve t)) t := by
  obtain ⟨M,bounded⟩ := (isCompact_Icc : IsCompact (Icc (-radius) radius)).exists_bound_of_continuousOn
    continuousPerturbation.continuousOn
  have nonnegative : 0≤M := (norm_nonneg (perturbation start)).trans
    (bounded start (Ioo_subset_Icc_self located))
  let K : ℝ≥0 := ⟨M,nonnegative⟩
  let L : ℝ≥0 := ‖epsilon‖₊*K*(1+‖initial‖₊)
  let duration : ℝ≥0 := ⟨2*radius,by positivity⟩
  let a : ℝ≥0 := L*duration+1
  let origin : Icc (-radius) radius := ⟨start,Ioo_subset_Icc_self located⟩
  have picard : IsPicardLindelof (sphereField perturbation epsilon initial) origin initial a 0 L (L*2) := by
    constructor
    · intro t inside
      exact (sphereField_lipschitz perturbation epsilon initial t K (bounded t inside)).lipschitzOnWith
    · intro v _
      exact (sphereField_continuous perturbation continuousPerturbation epsilon initial v).continuousOn
    · intro t inside v _
      apply (sphereField_norm perturbation epsilon initial v t).trans
      change |epsilon| * ‖perturbation t‖*(1+‖initial‖)≤(L : ℝ)
      simp only [L,NNReal.coe_mul,NNReal.coe_add,NNReal.coe_one,coe_nnnorm,Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (bounded t inside) (abs_nonneg epsilon)) (by positivity)
    · have length : max (radius-start) (start-(-radius))≤2*radius :=
        max_le (by linarith [located.1]) (by linarith [located.2])
      change (L : ℝ)*max (radius-start) (start-(-radius))≤(a : ℝ)-0
      calc
        _≤(L : ℝ)*(2*radius) := mul_le_mul_of_nonneg_left length L.2
        _≤(a : ℝ)-0 := by
          change (L : ℝ)*(2*radius)≤(L : ℝ)*(2*radius)+1-0
          linarith
  obtain ⟨curve,starts,evolves⟩ := picard.exists_eq_forall_mem_Icc_hasDerivWithinAt₀
  have interior (t : ℝ) (inside : t ∈ Ioo (-radius) radius) :
      HasDerivAt curve (sphereField perturbation epsilon initial t (curve t)) t :=
    (evolves t (Ioo_subset_Icc_self inside)).hasDerivAt (Icc_mem_nhds inside.1 inside.2)
  exact ⟨curve,starts,sphere_curve_original perturbation symmetric epsilon radius start initial curve located starts interior⟩

end
end SaturationMonoid.PhysicsCore.LowEnergy.MatterSpace.Response
