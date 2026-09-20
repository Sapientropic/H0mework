import H0mework.Physics.LowEnergyMatterSpace.SpatialResponseKubo
import Mathlib.Analysis.ODE.ExistUnique

/-! A bounded perturbation history generates a genuine finite-coupling interaction development. -/
set_option autoImplicit false
open Set Metric
open scoped NNReal
namespace SaturationMonoid.PhysicsCore.LowEnergy.MatterSpace.Response
noncomputable section

def interactionGenerator (perturbation : ℝ → MatterL2 →L[ℂ] MatterL2)
    (epsilon time : ℝ) : MatterL2 →L[ℂ] MatterL2 :=
  (-Complex.I*(epsilon : ℂ)) • heisenberg (perturbation time) time

theorem interactionGenerator_continuous (perturbation : ℝ → MatterL2 →L[ℂ] MatterL2)
    (continuousPerturbation : Continuous perturbation) (epsilon : ℝ) (v : MatterL2) :
    Continuous (fun time => interactionGenerator perturbation epsilon time v) := by
  unfold interactionGenerator
  convert! (heisenberg_action_continuous perturbation continuousPerturbation v).const_smul
    (-Complex.I*(epsilon : ℂ)) using 1

theorem interactionGenerator_bound (perturbation : ℝ → MatterL2 →L[ℂ] MatterL2)
    (epsilon time : ℝ) (v : MatterL2) :
    ‖interactionGenerator perturbation epsilon time v‖≤|epsilon| * ‖perturbation time‖*‖v‖ := by
  change ‖(-Complex.I*(epsilon : ℂ)) •
    spatialUnitary (-time) (perturbation time (spatialUnitary time v))‖≤_
  simp only [norm_smul,norm_mul,norm_neg,Complex.norm_I,Complex.norm_real,Real.norm_eq_abs,
    one_mul,spatialUnitary_norm]
  have bound := (perturbation time).le_opNorm (spatialUnitary time v)
  rw [spatialUnitary_norm] at bound
  exact (mul_le_mul_of_nonneg_left bound (abs_nonneg epsilon)).trans_eq (mul_assoc _ _ _).symm

theorem interactionGenerator_lipschitz (perturbation : ℝ → MatterL2 →L[ℂ] MatterL2)
    (epsilon time : ℝ) (K : ℝ≥0) (coupling : |epsilon|≤1) (bounded : ‖perturbation time‖≤K) :
    LipschitzWith K (interactionGenerator perturbation epsilon time) := by
  apply LipschitzWith.of_dist_le_mul
  intro u v
  rw [dist_eq_norm,← map_sub,dist_eq_norm]
  apply (interactionGenerator_bound perturbation epsilon time (u-v)).trans
  have product : |epsilon| * ‖perturbation time‖≤K :=
    (mul_le_mul_of_nonneg_right coupling (norm_nonneg _)).trans (by simpa using bounded)
  exact mul_le_mul_of_nonneg_right product (norm_nonneg _)

theorem perturbedFamily_exists (perturbation : ℝ → MatterL2 →L[ℂ] MatterL2)
    (continuousPerturbation : Continuous perturbation) :
    ∃ delta : ℝ, 0<delta ∧ ∃ family : ℝ → ℝ → MatterL2 → ℝ → MatterL2,
      ∀ epsilon start initial, |epsilon|≤1 → start ∈ Ioo (-delta) delta →
        family epsilon start initial start=initial ∧
        ∀ time ∈ Ioo (-delta) delta,
          HasDerivAt (family epsilon start initial)
            (interactionGenerator perturbation epsilon time (family epsilon start initial time)) time := by
  obtain ⟨M,bounded⟩ := (isCompact_Icc : IsCompact (Icc (-1 : ℝ) 1)).exists_bound_of_continuousOn
    continuousPerturbation.continuousOn
  have nonnegative : 0≤M := (norm_nonneg (perturbation 0)).trans (bounded 0 (by constructor <;> norm_num))
  let K : ℝ≥0 := ⟨M,nonnegative⟩
  let delta : ℝ := 1/(4*M+1)
  have positive : 0<delta := by dsimp [delta]; positivity
  have small : delta≤1 := by
    dsimp [delta]
    apply (div_le_one (by positivity)).mpr
    linarith
  have radius : 4*M*delta≤1 := by
    dsimp [delta]
    rw [mul_one_div]
    exact (div_le_one (by positivity)).mpr (by linarith)
  have subinterval (time : ℝ) (inside : time ∈ Icc (-delta) delta) : time ∈ Icc (-1 : ℝ) 1 :=
    ⟨by linarith [inside.1],by linarith [inside.2]⟩
  have curves (epsilon start : ℝ) (initial : MatterL2) :
      ∃ curve : ℝ → MatterL2, |epsilon|≤1 → start ∈ Ioo (-delta) delta → curve start=initial ∧
        ∀ time ∈ Ioo (-delta) delta,
          HasDerivAt curve (interactionGenerator perturbation epsilon time (curve time)) time := by
    by_cases coupling : |epsilon|≤1
    · by_cases located : start ∈ Ioo (-delta) delta
      · let r : ℝ≥0 := ‖initial‖₊+1
        let a : ℝ≥0 := 2*r
        let L : ℝ≥0 := K*a
        let origin : Icc (-delta) delta := ⟨start,Ioo_subset_Icc_self located⟩
        have picard : IsPicardLindelof (fun time v => interactionGenerator perturbation epsilon time v)
            origin (0 : MatterL2) a r L K := by
          constructor
          · intro time inside
            exact (interactionGenerator_lipschitz perturbation epsilon time K coupling
              (bounded time (subinterval time inside))).lipschitzOnWith
          · intro v _
            exact (interactionGenerator_continuous perturbation continuousPerturbation epsilon v).continuousOn
          · intro time inside v near
            have size : ‖v‖≤a := by simpa only [mem_closedBall_iff_norm,sub_zero] using near
            have estimate := (interactionGenerator_lipschitz perturbation epsilon time K coupling
              (bounded time (subinterval time inside))).dist_le_mul v 0
            simp only [map_zero,dist_zero_right] at estimate
            exact estimate.trans (mul_le_mul_of_nonneg_left size K.2)
          · have length : max (delta-start) (start-(-delta))≤2*delta :=
              max_le (by linarith [located.1]) (by linarith [located.2])
            change (L : ℝ)*max (delta-start) (start-(-delta))≤(a : ℝ)-r
            calc
              _≤(L : ℝ)*(2*delta) := mul_le_mul_of_nonneg_left length L.2
              _=(r : ℝ)*(4*M*delta) := by
                change (M*(2*(r : ℝ)))*(2*delta)=(r : ℝ)*(4*M*delta)
                ring
              _≤(r : ℝ)*1 := mul_le_mul_of_nonneg_left radius r.2
              _=(a : ℝ)-r := by simp only [a,NNReal.coe_mul,NNReal.coe_ofNat]; ring
        have initialInside : initial ∈ closedBall (0 : MatterL2) r := by
          simp only [mem_closedBall_iff_norm,sub_zero,r,NNReal.coe_add,coe_nnnorm,NNReal.coe_one]
          linarith
        obtain ⟨curve,starts,evolves⟩ := picard.exists_eq_forall_mem_Icc_hasDerivWithinAt initialInside
        refine ⟨curve,fun _ _ => ⟨starts,fun time inside => ?_⟩⟩
        exact (evolves time (Ioo_subset_Icc_self inside)).hasDerivAt (Icc_mem_nhds inside.1 inside.2)
      · exact ⟨fun _ => initial,fun _ impossible => False.elim (located impossible)⟩
    · exact ⟨fun _ => initial,fun impossible _ => False.elim (coupling impossible)⟩
  choose family generated using curves
  exact ⟨delta,positive,family,generated⟩

end
end SaturationMonoid.PhysicsCore.LowEnergy.MatterSpace.Response
