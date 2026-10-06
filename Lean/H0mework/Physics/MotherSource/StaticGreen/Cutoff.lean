import H0mework.Physics.MotherSource.StaticGreen.KernelLimit

/-! Finite Gaussian cutoffs satisfy the exact source Laplacian pairing by proved Fubini and the fundamental theorem of calculus. -/

set_option autoImplicit false
set_option maxHeartbeats 150000
namespace SaturationMonoid.PhysicsCore.Stage10.StaticGreen
open MeasureTheory MeasureTheory.Measure Filter Set
open scoped Topology SchwartzMap LineDeriv
open SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025
open BasinRefinement SourceGaussianModel SourceCoulomb
noncomputable section

theorem cutoff_weighted_integrable (upper : ℝ) (coefficient : ℝ → Point → ℝ)
    (continuous : Continuous (Function.uncurry coefficient)) (constant quadratic : ℝ)
    (bound : ∀ t ∈ Ioc (0 : ℝ) upper, ∀ point, ‖coefficient t point‖ ≤ constant+quadratic*‖point‖^2)
    (test : 𝓢(Point, ℝ)) :
    Integrable (fun pair : ℝ × Point => coefficient pair.1 pair.2*test pair.2)
      ((volume.restrict (Ioc (0 : ℝ) upper)).prod volume) := by
  have majorant := (test.integrable.norm.const_mul constant).add
    ((test.integrable_pow_mul volume 2).const_mul quadratic)
  have majorantProduct := majorant.comp_snd (volume.restrict (Ioc (0 : ℝ) upper))
  apply majorantProduct.mono' (continuous.mul (test.continuous.comp continuous_snd)).aestronglyMeasurable
  have inSlice : ∀ᵐ pair : ℝ × Point ∂(volume.restrict (Ioc (0 : ℝ) upper)).prod volume,
      pair.1 ∈ Ioc (0 : ℝ) upper := by
    apply (ae_prod_iff_ae_ae (measurableSet_Ioc.preimage measurable_fst)).mpr
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact Eventually.of_forall (fun _ => ht)
  filter_upwards [inSlice] with pair ht
  change ‖coefficient pair.1 pair.2*test pair.2‖ ≤
    constant*‖test pair.2‖+quadratic*(‖pair.2‖^2*‖test pair.2‖)
  rw [norm_mul]
  calc
    ‖coefficient pair.1 pair.2‖*‖test pair.2‖ ≤
        (constant+quadratic*‖pair.2‖^2)*‖test pair.2‖ :=
      mul_le_mul_of_nonneg_right (bound pair.1 ht pair.2) (norm_nonneg _)
    _ = _ := by ring

theorem cutoff_heat_integrable (upper : ℝ) (test : 𝓢(Point, ℝ)) :
    Integrable (fun pair : ℝ × Point => spatialHeat pair.1 pair.2*test pair.2)
      ((volume.restrict (Ioc (0 : ℝ) upper)).prod volume) := by
  apply cutoff_weighted_integrable upper spatialHeat _ 1 0 _ test
  · unfold Function.uncurry spatialHeat
    exact ((continuous_fst.pow 2).neg.mul ((distance_continuous.comp continuous_snd).pow 2)).rexp
  · intro t _ point
    simpa only [zero_mul, add_zero, Real.norm_eq_abs, abs_of_pos (spatialHeat_positive t point)]
      using spatialHeat_le_one t point

theorem cutoff_second_integrable (upper : ℝ) (index : Fin 3) (test : 𝓢(Point, ℝ)) :
    Integrable (fun pair : ℝ × Point => heatSecond pair.1 index pair.2*test pair.2)
      ((volume.restrict (Ioc (0 : ℝ) upper)).prod volume) := by
  apply cutoff_weighted_integrable upper (fun t => heatSecond t index) _
    (2*upper^2) (4*upper^4) _ test
  · unfold Function.uncurry heatSecond spatialHeat distance
    fun_prop
  · intro t ht point
    apply (heatSecond_bound t point index).trans
    gcongr
    · exact ht.1.le
    · exact ht.2
    · exact ht.1.le
    · exact ht.2

theorem cutoff_laplacian_integrable (upper : ℝ) (test : 𝓢(Point, ℝ)) :
    Integrable (fun pair : ℝ × Point => -(∑ index : Fin 3, heatSecond pair.1 index pair.2)*test pair.2)
      ((volume.restrict (Ioc (0 : ℝ) upper)).prod volume) := by
  have each := integrable_finsetSum Finset.univ (fun i _ => cutoff_second_integrable upper i test)
  have result := each.neg
  change Integrable (fun pair : ℝ × Point => -(∑ i : Fin 3, heatSecond pair.1 i pair.2*test pair.2)) _ at result
  simpa only [← Finset.sum_mul, neg_mul] using result

theorem spatial_heat_primitive (parameter : ℝ) (point : Point) :
    HasDerivAt (fun t => 2*t^3*spatialHeat t point)
      (-(∑ index : Fin 3, heatSecond parameter index point)) parameter := by
  have generated := (((hasDerivAt_id parameter).pow 3).const_mul 2).mul
    ((((hasDerivAt_id parameter).pow 2).neg.mul_const ((distance point)^2)).exp)
  convert generated using 1 <;> try rfl
  rw [heatSecond_sum]
  simp only [spatialHeat, id_eq, Pi.pow_apply, Pi.neg_apply]
  ring

theorem cutoff_point (upper : ℝ) (point : Point) :
    (∫ t in 0..upper, -(∑ index : Fin 3, heatSecond t index point)) =
      2*upper^3*spatialHeat upper point := by
  have continuous : Continuous (fun t => -(∑ index : Fin 3, heatSecond t index point)) := by
    unfold heatSecond spatialHeat
    fun_prop
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => spatial_heat_primitive t point)
    (continuous.intervalIntegrable 0 upper)]
  simp

theorem cutoff_pairing (upper : ℝ) (nonnegative : 0 ≤ upper) (test : 𝓢(Point, ℝ)) :
    (∫ point : Point, truncatedHeat upper point*(-testLaplacian test point)) =
      2*(∫ point : Point, upper^3*spatialHeat upper point*test point) := by
  have heatIntegrable := cutoff_heat_integrable upper (-testLaplacian test)
  have lapIntegrable := cutoff_laplacian_integrable upper test
  rw [← uIoc_of_le nonnegative] at heatIntegrable lapIntegrable
  calc
    (∫ point : Point, truncatedHeat upper point*(-testLaplacian test point)) =
        ∫ point : Point, ∫ t in 0..upper, spatialHeat t point*(-testLaplacian test point) := by
      apply integral_congr_ae
      filter_upwards [] with point
      rw [truncatedHeat, intervalIntegral.integral_mul_const]
    _ = ∫ t in 0..upper, ∫ point : Point, spatialHeat t point*(-testLaplacian test point) := by
      exact (intervalIntegral_integral_swap heatIntegrable).symm
    _ = ∫ t in 0..upper, ∫ point : Point, -(∑ index : Fin 3, heatSecond t index point)*test point := by
      apply intervalIntegral.integral_congr
      intro t _
      simp only [mul_neg, integral_neg, neg_mul]
      rw [heat_pairing_laplacian]
      simp only [heatSecond_sum]
    _ = ∫ point : Point, ∫ t in 0..upper, -(∑ index : Fin 3, heatSecond t index point)*test point :=
      intervalIntegral_integral_swap lapIntegrable
    _ = ∫ point : Point, (2*upper^3*spatialHeat upper point)*test point := by
      apply integral_congr_ae
      filter_upwards [] with point
      rw [intervalIntegral.integral_mul_const, cutoff_point]
    _ = _ := by simp_rw [mul_assoc]; rw [integral_const_mul]

end
end SaturationMonoid.PhysicsCore.Stage10.StaticGreen
