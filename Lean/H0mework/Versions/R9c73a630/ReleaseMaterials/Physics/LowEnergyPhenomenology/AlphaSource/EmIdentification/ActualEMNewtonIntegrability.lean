import H0mework.Versions.R9c73a630.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualEMStaticFourier
import Mathlib.Analysis.SpecialFunctions.Pow.Integral

set_option autoImplicit false
set_option maxRecDepth 8192
noncomputable section
namespace LowEnergy.GaussComposite.ActualEMCarrierOwn
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open PreparationVacuumPhysicalCharacteristic PreparationVacuumStaticSpatialSource
open CanonicalGradedSpatialSource MeasureTheory Filter Set
open scoped Topology SchwartzMap

private theorem newton_spatial_nonnegative (k : PhysicalMomentum) : 0 ≤ spatialSquare k := by
  unfold spatialSquare
  positivity

private theorem newton_coordinate_square (k : PhysicalMomentum) (i : Fin 3) : (k i)^2 ≤ spatialSquare k := by
  fin_cases i
  · change (k 0)^2 ≤ (k 0)^2+(k 1)^2+(k 2)^2
    nlinarith [sq_nonneg (k 1),sq_nonneg (k 2)]
  · change (k 1)^2 ≤ (k 0)^2+(k 1)^2+(k 2)^2
    nlinarith [sq_nonneg (k 0),sq_nonneg (k 2)]
  · change (k 2)^2 ≤ (k 0)^2+(k 1)^2+(k 2)^2
    nlinarith [sq_nonneg (k 0),sq_nonneg (k 1)]

private theorem newton_pi_norm_square (k : PhysicalMomentum) : ‖k‖^2 ≤ spatialSquare k := by
  have radius := Real.sqrt_nonneg (spatialSquare k)
  have square := Real.sq_sqrt (newton_spatial_nonnegative k)
  have normBound : ‖k‖ ≤ Real.sqrt (spatialSquare k) := by
    apply (pi_norm_le_iff_of_nonneg radius).mpr
    intro i
    rw [Real.norm_eq_abs]
    nlinarith [newton_coordinate_square k i,sq_abs (k i),abs_nonneg (k i)]
  nlinarith [norm_nonneg k]

private theorem newton_schwartz_measurable (test : 𝓢(PhysicalMomentum,ℂ)) :
    Measurable (fun k=>‖test k‖/spatialSquare k) := by
  have squared : Continuous spatialSquare := by unfold spatialSquare;fun_prop
  exact test.continuous.measurable.norm.div squared.measurable

private theorem newton_schwartz_local_bound (test : 𝓢(PhysicalMomentum,ℂ)) (k : PhysicalMomentum) :
    ‖‖test k‖/spatialSquare k‖ ≤ (SchwartzMap.seminorm ℝ 0 0 test)*‖k‖^(-(2:ℝ)) := by
  by_cases zero : k=0
  · subst k
    simp [spatialSquare]
  have kp : 0 < ‖k‖ := norm_pos_iff.mpr zero
  have comparison := newton_pi_norm_square k
  have ap : 0 < spatialSquare k := lt_of_lt_of_le (sq_pos_of_pos kp) comparison
  have Mpos : 0 ≤ SchwartzMap.seminorm ℝ 0 0 test := apply_nonneg _ _
  rw [Real.norm_eq_abs,abs_of_nonneg (div_nonneg (norm_nonneg _) ap.le)]
  simp only [Real.rpow_neg_eq_inv_rpow,Real.rpow_ofNat]
  calc
    _ ≤ (SchwartzMap.seminorm ℝ 0 0 test)/spatialSquare k :=
      div_le_div_of_nonneg_right (SchwartzMap.norm_le_seminorm ℝ test k) ap.le
    _ ≤ (SchwartzMap.seminorm ℝ 0 0 test)*(‖k‖^2)⁻¹ := by
      rw [div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_left (inv_anti₀ (sq_pos_of_pos kp) comparison) Mpos
    _ = _ := by rw [inv_pow]

/-- Three-dimensional Newton singularity is locally integrable against every source Schwartz packet; no target-integrability premise is used. -/
theorem em_newton_schwartz_local (test : 𝓢(PhysicalMomentum,ℂ)) (radius : ℝ) :
    IntegrableOn (fun k=>‖test k‖/spatialSquare k) (Metric.ball 0 radius) := by
  exact integrableOn_ball_of_norm_le_rpow (E:=PhysicalMomentum) (α:=(2:ℝ))
    (C:=SchwartzMap.seminorm ℝ 0 0 test)
    (by norm_num [Module.finrank_fin_fun]) (by norm_num [Module.finrank_fin_fun])
    (Eventually.of_forall (newton_schwartz_local_bound test))
    (newton_schwartz_measurable test).aestronglyMeasurable

/-- Local dimension-three integrability and Schwartz decay jointly pay the entire Newton weight. -/
theorem em_newton_schwartz_integrable (test : 𝓢(PhysicalMomentum,ℂ)) :
    Integrable (fun k=>‖test k‖/spatialSquare k) := by
  have near:=em_newton_schwartz_local test 1
  have far : IntegrableOn (fun k=>‖test k‖/spatialSquare k) (Metric.ball (0:PhysicalMomentum) 1)ᶜ := by
    apply test.integrable.norm.integrableOn.mono' (newton_schwartz_measurable test).aestronglyMeasurable.restrict
    filter_upwards [ae_restrict_mem measurableSet_ball.compl] with k outside
    have kp : 1 ≤ ‖k‖ := by
      simpa only [mem_compl_iff,Metric.mem_ball,dist_zero_right,not_lt] using outside
    have ap : 1 ≤ spatialSquare k := by nlinarith [newton_pi_norm_square k]
    rw [Real.norm_eq_abs,abs_of_nonneg (div_nonneg (norm_nonneg _) (by linarith))]
    exact (div_le_iff₀ (by linarith : 0 < spatialSquare k)).mpr
      (by nlinarith [norm_nonneg (test k)])
  simpa only [Set.union_compl_self,integrableOn_univ] using near.union far

private theorem newton_physical_square (frequency : PhysicalMomentum) :
    spatialSquare (sourceSpatialMomentum frequency)=(2*Real.pi)^2*spatialSquare frequency := by
  simp only [sourceSpatialMomentum,spatialSquare,Pi.smul_apply,smul_eq_mul]
  ring

/-- The original k=2pi*frequency map retains its exact factor in the full Coulomb domination payer. -/
theorem em_physical_newton_schwartz_integrable (test : 𝓢(PhysicalMomentum,ℂ)) :
    Integrable (fun frequency=>‖test frequency‖/spatialSquare (sourceSpatialMomentum frequency)) := by
  have generated:=(em_newton_schwartz_integrable test).const_mul ((2*Real.pi)^2)⁻¹
  convert generated using 1
  funext frequency
  rw [newton_physical_square]
  simp only [div_eq_mul_inv,mul_inv_rev]
  ring

/-- A source-produced whole-Green norm budget can be consumed without postulating its Coulomb integral. -/
theorem em_physical_coulomb_budget_integrable (B : ℝ) (test : 𝓢(PhysicalMomentum,ℂ)) :
    Integrable (fun frequency=>B*‖test frequency‖/spatialSquare (sourceSpatialMomentum frequency)) := by
  simpa only [mul_div_assoc] using (em_physical_newton_schwartz_integrable test).const_mul B

/-- The same physical Fourier phase preserves Newton-Schwartz integrability. -/
theorem em_physical_newton_packet_integrable (test : 𝓢(PhysicalMomentum,ℂ)) (x : PhysicalMomentum) :
    Integrable (fun frequency=>sourceSpatialPhase frequency x*test frequency/
      (spatialSquare (sourceSpatialMomentum frequency):ℂ)) := by
  have measurable : Measurable (fun frequency=>sourceSpatialPhase frequency x*test frequency/
      (spatialSquare (sourceSpatialMomentum frequency):ℂ)) := by
    unfold sourceSpatialPhase sourceSpatialMomentum spatialSquare
    fun_prop
  apply (em_physical_newton_schwartz_integrable test).mono' measurable.aestronglyMeasurable
  filter_upwards with frequency
  have phase : ‖sourceSpatialPhase frequency x‖=1 := by simp [sourceSpatialPhase,Complex.norm_exp]
  simp only [norm_div,norm_mul,phase,one_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (newton_spatial_nonnegative _)]
  exact le_rfl

end LowEnergy.GaussComposite.ActualEMCarrierOwn
