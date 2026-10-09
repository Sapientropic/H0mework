import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Attraction.Substitution
import H0mework.Arithmetic.PrimeShadow.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Kernel
import H0mework.Versions.AB.Arithmetic.PrimeShadow.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.Continuous.WholeBand.IQA.Coulomb.Source

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Attraction
open LAlanine40K2025 UnifiedOrbitals BasinRefinement GaussianPrimitive SourceGaussianModel SourceFiniteData ContinuousGradient GlobalSource Polynomial MeasureTheory Set
open LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace
open BasinRefinement.SourceCoulomb
open scoped BigOperators intervalIntegral Topology
noncomputable section

/-- The heat-kernel (Tonelli) swap:
`∫ v_s·v_t·kernel(x−C) = (2/√π)·∫_{t>0} ∫_x v_s·v_t·e^{−t²·|x−C|²}`. -/
theorem attraction_heat_swap (s t : Term) (hs : 0 < s.exponent) (ht : 0 < t.exponent)
    (C : Fin 3 → ℚ) :
    ∫ x : Point, (value s zeroJet x * value t zeroJet x) *
        kernel (x - fun k => (C k : ℝ)) =
    (2/Real.sqrt Real.pi) * ∫ tt in Ioi (0:ℝ), ∫ x : Point,
      (value s zeroJet x * value t zeroJet x) *
        Real.exp (-(distance (x - fun k => (C k : ℝ)))^2 * tt^2) := by
  set Cv : Point := fun k => (C k : ℝ) with hCv
  set v : Point → ℝ := fun x => value s zeroJet x * value t zeroJet x with hvdef
  set F : Point × ℝ → ℝ := fun p =>
    v p.1 * Real.exp (-(distance (p.1 - Cv))^2 * p.2^2) with hFdef
  have hv_int : Integrable v :=
    (term_integrable t ht zeroJet).bdd_mul
      (value_contDiff s zeroJet 0).continuous.aestronglyMeasurable
      (Filter.Eventually.of_forall (fun x => term_uniform_bound s hs zeroJet x))
  have hv_bound : ∀ x : Point, ‖v x‖ ≤
      (termBound s zeroJet : ℝ) * (termBound t zeroJet : ℝ) := by
    intro x
    simp only [hvdef]
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul (term_uniform_bound s hs zeroJet x)
      (term_uniform_bound t ht zeroJet x) (abs_nonneg _)
      (by positivity)
  have hne : ∀ᵐ x : Point ∂volume, x ≠ Cv :=
    compl_mem_ae_iff.mpr (by simp : (volume : Measure Point) ({Cv} : Set Point) = 0)
  have hv_cont : Continuous v := by
    rw [hvdef]
    exact (value_contDiff s zeroJet 0).continuous.mul
      (value_contDiff t zeroJet 0).continuous
  have hFmeas : AEStronglyMeasurable F
      ((volume : Measure (Point)).prod ((volume : Measure ℝ).restrict (Ioi 0))) := by
    have hc : Continuous F := by
      rw [hFdef]
      have h1 : Continuous (fun p : Point × ℝ => v p.1) :=
        hv_cont.comp continuous_fst
      have h3 : Continuous (fun p : Point × ℝ => distance (p.1 - Cv)) :=
        distance_continuous.comp (continuous_fst.sub continuous_const)
      have h5 : Continuous (fun p : Point × ℝ =>
          -(distance (p.1 - Cv))^2 * p.2^2) :=
        ((h3.pow 2).neg).mul (continuous_snd.pow 2)
      exact h1.mul (Real.continuous_exp.comp h5)
    exact hc.aestronglyMeasurable
  have hinner : ∀ᵐ x : Point ∂volume,
      Integrable (fun t : ℝ => v x * Real.exp (-(distance (x - Cv))^2 * t^2))
        ((volume : Measure ℝ).restrict (Ioi 0)) := by
    filter_upwards [hne] with x hx
    have hd : 0 < distance (x - Cv) :=
      lt_of_lt_of_le (norm_pos_iff.mpr (sub_ne_zero.mpr hx)) (pi_norm_le_distance _)
    have hg : IntegrableOn (fun t : ℝ => Real.exp (-(distance (x-Cv))^2 * t^2))
        (Ioi 0) :=
      integrableOn_Ioi_exp_neg_mul_sq_iff.mpr (sq_pos_of_ne_zero (ne_of_gt hd))
    exact hg.const_mul (v x)
  have hk : ∀ x : Point,
      (∫ t in Ioi (0:ℝ), Real.exp (-(distance (x-Cv))^2 * t^2)) =
        (Real.sqrt Real.pi/2) * kernel (x - Cv) := by
    intro x
    have kl := kernel_laplace (x - Cv)
    rw [kl]
    field_simp [Real.sqrt_ne_zero'.mpr Real.pi_pos]
  have hpt : ∀ x : Point,
      (∫ t in Ioi (0:ℝ), ‖v x * Real.exp (-(distance (x-Cv))^2 * t^2)‖) =
        |v x| * (Real.sqrt Real.pi/2) * kernel (x - Cv) := by
    intro x
    have normpt : ∀ t : ℝ, ‖v x * Real.exp (-(distance (x-Cv))^2*t^2)‖ =
        |v x| * Real.exp (-(distance (x-Cv))^2*t^2) := by
      intro t
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.exp_nonneg _)]
    rw [setIntegral_congr_fun measurableSet_Ioi (fun t _ => normpt t),
      integral_const_mul, hk x]
    ring
  have hker : Integrable (fun x : Point => |v x| * kernel (x - Cv)) := by
    have h := integrable_mul_shifted_kernel (fun x => |v x|) hv_int.abs
      ((termBound s zeroJet : ℝ) * (termBound t zeroJet : ℝ))
      (fun x => by rw [Real.norm_eq_abs, abs_abs]; exact hv_bound x) Cv
    exact h
  have houter : Integrable
      (fun x => ∫ t : ℝ, ‖F (x, t)‖ ∂(volume.restrict (Ioi 0))) := by
    have hae : (fun x => ∫ t in Ioi (0:ℝ), ‖v x *
        Real.exp (-(distance (x-Cv))^2 * t^2)‖) =ᵐ[volume]
        (fun x => |v x| * (√Real.pi/2) * kernel (x - Cv)) :=
      Filter.Eventually.of_forall hpt
    have hr : Integrable (fun x : Point => |v x| * (√Real.pi/2) * kernel (x - Cv)) := by
      have hconst := hker.const_mul (√Real.pi/2)
      have heq : (fun x : Point => |v x| * (√Real.pi/2) * kernel (x - Cv)) =
          fun x => √Real.pi/2 * (|v x| * kernel (x - Cv)) := by
        funext x; ring
      rw [heq]
      exact hconst
    exact hr.congr hae.symm
  have hFi : Integrable F
      ((volume : Measure (Point)).prod ((volume : Measure ℝ).restrict (Ioi 0))) :=
    (integrable_prod_iff hFmeas).mpr ⟨hinner, houter⟩
  calc ∫ x : Point, v x * kernel (x - Cv)
      = ∫ x : Point, v x * ((2/Real.sqrt Real.pi) *
          ∫ tt in Ioi (0:ℝ), Real.exp (-(distance (x-Cv))^2 * tt^2)) := by
        apply integral_congr_ae
        filter_upwards with x
        rw [kernel_laplace]
    _ = ∫ x : Point, (2/Real.sqrt Real.pi) *
          ∫ tt in Ioi (0:ℝ), v x * Real.exp (-(distance (x-Cv))^2 * tt^2) := by
        apply integral_congr_ae
        filter_upwards with x
        rw [← integral_const_mul]
        conv_rhs => rw [← integral_const_mul]
        rw [← integral_const_mul]
        apply setIntegral_congr_fun measurableSet_Ioi
        intro a _
        ring
    _ = (2/Real.sqrt Real.pi) * ∫ x : Point, ∫ tt in Ioi (0:ℝ),
          v x * Real.exp (-(distance (x-Cv))^2 * tt^2) := by
        rw [← integral_const_mul]
    _ = (2/Real.sqrt Real.pi) * ∫ tt in Ioi (0:ℝ), ∫ x : Point,
          v x * Real.exp (-(distance (x-Cv))^2 * tt^2) := by
        congr 1
        have hswap := (integral_prod F hFi).symm.trans (integral_prod_symm F hFi)
        exact hswap

end
end LAlanine40K2025.UnifiedOrbitals.Attraction
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
