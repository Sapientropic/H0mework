import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualWholeStaticPair
import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualEMNewtonIntegrability
import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualEMStaticIRPacket

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualWholeStatic
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open PreparationVacuumOriginalGreenFeedback PreparationVacuumPhysicalCharacteristic
open PreparationVacuumStaticPoleResponse PreparationPhysicalStaticSpatialCouplingReturn
open PreparationVacuumStaticSpatialSource CanonicalGradedSpatialSource
open PreparationPhysicalCausalSpatialDilation
open ActualEMCarrierOwn MeasureTheory Filter Set
open scoped Matrix BigOperators Topology Matrix.Norms.Operator SchwartzMap
local instance : MeasurableSpace WholeMatrix := borel _
local instance : BorelSpace WholeMatrix := ⟨rfl⟩
attribute [local irreducible] originalChange originalReadback contactInverse activeKernel
  sourceGreen wholeStaticLimit

def wholeSourceIRRadius : ℝ := min staticRadius (Classical.choose whole_static_green_domination)

theorem whole_source_ir_radius_positive : 0 < wholeSourceIRRadius :=
  lt_min staticRadius_pos (Classical.choose_spec whole_static_green_domination).1

private def wholeDirection (k : PhysicalMomentum) : PhysicalMomentum :=
  (Real.sqrt (spatialSquare k))⁻¹ • k

private theorem whole_direction_unit (k : PhysicalMomentum) (positive : 0 < spatialSquare k) :
    spatialSquare (wholeDirection k) = 1 := by
  have rp := (Real.sqrt_pos.mpr positive).ne'
  have square := Real.sq_sqrt positive.le
  calc
    _ = (Real.sqrt (spatialSquare k))⁻¹^2 * spatialSquare k := by
      simp only [wholeDirection, spatialSquare, Pi.smul_apply, smul_eq_mul]
      ring
    _ = 1 := by field_simp [rp]; exact square.symm

private theorem whole_spatial_ray (k : PhysicalMomentum) (scale radius : ℝ) (nonzero : radius ≠ 0) :
    sourceStaticSpatialMomentum k scale =
      sourceStaticSpatialMomentum (radius⁻¹ • k) (scale * radius) := by
  ext j
  fin_cases j <;> simp [sourceStaticSpatialMomentum, Pi.smul_apply, smul_eq_mul,
    Complex.ofReal_mul, Complex.ofReal_inv]
  all_goals field_simp [Complex.ofReal_ne_zero.mpr nonzero]

private def wholeOriginalGreen (p : Fin 4 → ℂ) : WholeMatrix :=
  originalChange p * (contactInverse p + activeProjection * (extendedKernel p)⁻¹) * originalReadback p

private theorem whole_original_green_actual (p : regularSource) : wholeOriginalGreen p.val = sourceGreen p := by
  unfold wholeOriginalGreen sourceGreen
  rfl

/-- The original full289 Green on its generated IR window, with the actual Coulomb scaling. -/
def wholeCoulombIRSymbol (scale : ℝ) (k : PhysicalMomentum) : WholeMatrix :=
  if 0 < scale ∧ 0 < spatialSquare k ∧
      scale * Real.sqrt (spatialSquare k) < wholeSourceIRRadius then
    (scale^2 : ℝ) • wholeOriginalGreen (sourceStaticSpatialMomentum k scale)
  else 0

attribute [local irreducible] wholeCoulombIRSymbol wholeOriginalGreen

theorem whole_coulomb_ir_symbol_actual (scale : ℝ) (k : PhysicalMomentum)
    (positive : 0 < scale) (spatial : 0 < spatialSquare k)
    (inside : scale * Real.sqrt (spatialSquare k) < wholeSourceIRRadius) :
    wholeCoulombIRSymbol scale k = (spatialSquare k)⁻¹ •
      (((scale * Real.sqrt (spatialSquare k))^2 : ℝ) •
        sourceGreen (sourceSpatialStaticRegularPoint (wholeDirection k) (whole_direction_unit k spatial)
          ⟨scale * Real.sqrt (spatialSquare k), mul_pos positive (Real.sqrt_pos.mpr spatial),
            inside.le.trans (min_le_left _ _)⟩)) := by
  rw [wholeCoulombIRSymbol, if_pos ⟨positive, spatial, inside⟩]
  rw [←whole_original_green_actual]
  change (scale^2 : ℝ) • wholeOriginalGreen (sourceStaticSpatialMomentum k scale) =
    (spatialSquare k)⁻¹ • (((scale * Real.sqrt (spatialSquare k))^2 : ℝ) •
      wholeOriginalGreen (sourceStaticSpatialMomentum (wholeDirection k)
        (scale * Real.sqrt (spatialSquare k))))
  rw [whole_spatial_ray k scale _ (Real.sqrt_pos.mpr spatial).ne']
  rw [smul_smul, mul_pow, Real.sq_sqrt spatial.le]
  congr 1
  field_simp [spatial.ne']

private theorem whole_spatial_nonnegative (k : PhysicalMomentum) : 0 ≤ spatialSquare k := by
  unfold spatialSquare
  positivity

/-- The source-fixed residue norm pays the exact Newton weight, including its singular origin. -/
theorem whole_coulomb_ir_symbol_bound (scale : ℝ) (k : PhysicalMomentum) :
    ‖wholeCoulombIRSymbol scale k‖ ≤ wholeStaticBudget / spatialSquare k := by
  by_cases active : 0 < scale ∧ 0 < spatialSquare k ∧
      scale * Real.sqrt (spatialSquare k) < wholeSourceIRRadius
  · rw [whole_coulomb_ir_symbol_actual scale k active.1 active.2.1 active.2.2,
      norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr active.2.1)]
    let r : staticDomain := ⟨scale * Real.sqrt (spatialSquare k),
      mul_pos active.1 (Real.sqrt_pos.mpr active.2.1), active.2.2.le.trans (min_le_left _ _)⟩
    have paid := (Classical.choose_spec whole_static_green_domination).2 r
      (active.2.2.trans_le (min_le_right _ _)) (wholeDirection k) (whole_direction_unit k active.2.1)
    calc
      _ ≤ (spatialSquare k)⁻¹ * wholeStaticBudget :=
        mul_le_mul_of_nonneg_left paid (inv_nonneg.mpr active.2.1.le)
      _ = _ := by rw [div_eq_mul_inv, mul_comm]
  · simp only [wholeCoulombIRSymbol, if_neg active, norm_zero]
    exact div_nonneg whole_static_budget_nonnegative (whole_spatial_nonnegative k)

private theorem whole_matrix_continuous (terms : List SourceTerm) : Continuous (sourceMatrix terms) := by
  induction terms with
  | nil => exact continuous_const
  | cons a rest ih =>
    have term : Continuous a.matrix := by
      apply continuous_matrix
      intro i j
      simp only [SourceTerm.matrix, Matrix.single_apply]
      split_ifs
      · unfold Powers.value
        fun_prop
      · exact continuous_const
    exact term.add ih

private theorem whole_original_measurable : Measurable wholeOriginalGreen := by
  unfold wholeOriginalGreen
  have O : Continuous originalChange := by unfold originalChange; exact whole_matrix_continuous originalChangeTerms
  have C : Continuous contactInverse := by unfold contactInverse; exact whole_matrix_continuous contactInverseTerms
  have R : Continuous originalReadback := by unfold originalReadback; exact (O.comp continuous_neg).matrix_transpose
  have K : Continuous extendedKernel := by
    have A : Continuous activeKernel := by unfold activeKernel; exact whole_matrix_continuous activeTerms
    exact A.add continuous_const
  have inverse : Measurable (fun p : Fin 4 → ℂ => (extendedKernel p)⁻¹) := by
    simp only [Matrix.inv_def, Ring.inverse_eq_inv]
    exact K.matrix_det.measurable.inv.smul K.matrix_adjugate.measurable
  have P : Measurable (fun _ : Fin 4 → ℂ => activeProjection) := measurable_const
  exact (O.measurable.mul (C.measurable.add (P.mul inverse))).mul R.measurable

private theorem whole_ir_symbol_measurable (scale : ℝ) : Measurable (wholeCoulombIRSymbol scale) := by
  have squared : Continuous spatialSquare := by unfold spatialSquare; fun_prop
  have active : MeasurableSet {k : PhysicalMomentum | 0 < scale ∧ 0 < spatialSquare k ∧
      scale * Real.sqrt (spatialSquare k) < wholeSourceIRRadius} := by
    have h1 : MeasurableSet {k : PhysicalMomentum | 0 < scale} := by
      by_cases positive : 0 < scale <;> simp [positive]
    have h2 := measurableSet_lt (measurable_const : Measurable (fun _ : PhysicalMomentum => (0:ℝ))) squared.measurable
    have hr : Measurable (fun k : PhysicalMomentum => scale * Real.sqrt (spatialSquare k)) := by
      unfold spatialSquare
      fun_prop
    exact h1.inter (h2.inter (measurableSet_lt hr measurable_const))
  have momentum : Continuous (fun k : PhysicalMomentum => sourceStaticSpatialMomentum k scale) := by
    unfold sourceStaticSpatialMomentum
    fun_prop
  unfold wholeCoulombIRSymbol
  exact Measurable.ite active
    ((measurable_const : Measurable (fun _ : PhysicalMomentum => scale^2)).smul
      (whole_original_measurable.comp momentum.measurable)) measurable_const

set_option maxHeartbeats 400000 in
private theorem whole_ir_symbol_limit (k : PhysicalMomentum) (spatial : 0 < spatialSquare k) :
    Tendsto (fun scale : ℝ => wholeCoulombIRSymbol scale k) (𝓝[>] 0)
      (𝓝 ((spatialSquare k)⁻¹ • wholeStaticLimit)) := by
  let radial := Real.sqrt (spatialSquare k)
  have rp : 0 < radial := Real.sqrt_pos.mpr spatial
  apply Metric.tendsto_nhds.mpr
  intro epsilon ep
  obtain ⟨radius, positive, paid⟩ := whole_static_green_uniform
    (epsilon * spatialSquare k / 2) (by positivity)
  have near : ∀ᶠ scale : ℝ in 𝓝[>] 0, scale < min wholeSourceIRRadius radius / radial :=
    nhdsWithin_le_nhds (gt_mem_nhds (div_pos (lt_min whole_source_ir_radius_positive positive) rp))
  filter_upwards [self_mem_nhdsWithin, near] with scale scalePos small
  have product : scale * radial < min wholeSourceIRRadius radius := (lt_div_iff₀ rp).mp small
  have inside := product.trans_le (min_le_left _ _)
  have errorRadius := product.trans_le (min_le_right _ _)
  let r : staticDomain := ⟨scale * radial, mul_pos scalePos rp,
    inside.le.trans (min_le_left _ _)⟩
  have error := paid r errorRadius (wholeDirection k) (whole_direction_unit k spatial)
  rw [whole_coulomb_ir_symbol_actual scale k scalePos spatial inside,
    dist_eq_norm, ←smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr spatial)]
  calc
    _ ≤ (spatialSquare k)⁻¹ * (epsilon * spatialSquare k / 2) :=
      mul_le_mul_of_nonneg_left error
        (inv_nonneg.mpr spatial.le)
    _ = epsilon / 2 := by field_simp [spatial.ne']
    _ < epsilon := by linarith

private theorem whole_spatial_positive (k : PhysicalMomentum) (nonzero : k ≠ 0) : 0 < spatialSquare k := by
  have positive := whole_spatial_nonnegative k
  by_contra failed
  have zero : spatialSquare k = 0 := le_antisymm (not_lt.mp failed) positive
  have h0 : k 0 = 0 := by
    unfold spatialSquare at zero
    nlinarith [sq_nonneg (k 0), sq_nonneg (k 1), sq_nonneg (k 2)]
  have h1 : k 1 = 0 := by
    unfold spatialSquare at zero
    nlinarith [sq_nonneg (k 0), sq_nonneg (k 1), sq_nonneg (k 2)]
  have h2 : k 2 = 0 := by
    unfold spatialSquare at zero
    nlinarith [sq_nonneg (k 0), sq_nonneg (k 1), sq_nonneg (k 2)]
  apply nonzero
  funext j
  fin_cases j
  · exact h0
  · exact h1
  · exact h2

/-- The complete original Coulomb-scaled Fourier observation, before choosing any field or charge read. -/
def wholeCoulombIRPacket (scale : ℝ) (test : 𝓢(PhysicalMomentum, ℂ)) (x : PhysicalMomentum) : WholeMatrix :=
  ∫ frequency, (sourceSpatialPhase frequency x * test frequency) •
    wholeCoulombIRSymbol scale (sourceSpatialMomentum frequency)

private theorem whole_ir_integrand_measurable (scale : ℝ) (test : 𝓢(PhysicalMomentum, ℂ))
    (x : PhysicalMomentum) : Measurable (fun frequency =>
      (sourceSpatialPhase frequency x * test frequency) • wholeCoulombIRSymbol scale (sourceSpatialMomentum frequency)) := by
  have phase : Continuous (fun frequency => sourceSpatialPhase frequency x) := by
    unfold sourceSpatialPhase sourceSpatialMomentum
    fun_prop
  have momentum : Continuous sourceSpatialMomentum := by unfold sourceSpatialMomentum; fun_prop
  exact (phase.measurable.mul test.continuous.measurable).smul
    ((whole_ir_symbol_measurable scale).comp momentum.measurable)

private theorem whole_ir_integrand_bound (scale : ℝ) (test : 𝓢(PhysicalMomentum, ℂ))
    (x frequency : PhysicalMomentum) :
    ‖(sourceSpatialPhase frequency x * test frequency) •
      wholeCoulombIRSymbol scale (sourceSpatialMomentum frequency)‖ ≤
      wholeStaticBudget * ‖test frequency‖ / spatialSquare (sourceSpatialMomentum frequency) := by
  have phase : ‖sourceSpatialPhase frequency x‖ = 1 := by simp [sourceSpatialPhase, Complex.norm_exp]
  simp only [norm_smul, norm_mul, phase, one_mul]
  calc
    _ ≤ ‖test frequency‖ * (wholeStaticBudget / spatialSquare (sourceSpatialMomentum frequency)) :=
      mul_le_mul_of_nonneg_left (whole_coulomb_ir_symbol_bound scale _) (norm_nonneg _)
    _ = _ := by ring

theorem whole_coulomb_ir_packet_integrable (scale : ℝ) (test : 𝓢(PhysicalMomentum, ℂ))
    (x : PhysicalMomentum) : Integrable (fun frequency =>
      (sourceSpatialPhase frequency x * test frequency) • wholeCoulombIRSymbol scale (sourceSpatialMomentum frequency)) :=
  (em_physical_coulomb_budget_integrable wholeStaticBudget test).mono'
    (whole_ir_integrand_measurable scale test x).aestronglyMeasurable
    (Eventually.of_forall (whole_ir_integrand_bound scale test x))

private theorem whole_real_smul (a : ℝ) (M : WholeMatrix) : a • M = (a : ℂ) • M := by
  ext i j
  simp only [Matrix.smul_apply, Complex.real_smul, smul_eq_mul]

private theorem whole_newton_integral (test : 𝓢(PhysicalMomentum, ℂ)) (x : PhysicalMomentum) :
    (∫ frequency, (sourceSpatialPhase frequency x * test frequency) •
      ((spatialSquare (sourceSpatialMomentum frequency))⁻¹ • wholeStaticLimit)) =
      emNewtonPacket 0 0 test x • wholeStaticLimit := by
  simp only [whole_real_smul, smul_smul, Complex.ofReal_inv]
  rw [integral_smul_const]
  congr 1
  change (∫ frequency, sourceSpatialPhase frequency x * test frequency *
    (spatialSquare (sourceSpatialMomentum frequency) : ℂ)⁻¹) =
    ∫ frequency, (1:ℂ) * sourceSpatialPhase frequency x * test frequency *
      ((spatialSquare (sourceSpatialMomentum frequency) : ℂ) + (0:ℂ)^2 * (0:ℂ)^2)⁻¹
  simp only [one_mul, zero_pow (by norm_num : 2 ≠ 0), zero_mul, add_zero]

/-- Full289 Green, including its constraints and contacts, enters the true Newton Fourier packet. -/
theorem whole_coulomb_ir_packet_limit (test : 𝓢(PhysicalMomentum, ℂ)) (x : PhysicalMomentum) :
    Tendsto (fun scale : ℝ => wholeCoulombIRPacket scale test x) (𝓝[>] 0)
      (𝓝 (emNewtonPacket 0 0 test x • wholeStaticLimit)) := by
  unfold wholeCoulombIRPacket
  rw [←whole_newton_integral]
  apply tendsto_integral_filter_of_dominated_convergence (μ := volume)
    (fun frequency => wholeStaticBudget * ‖test frequency‖ / spatialSquare (sourceSpatialMomentum frequency))
  · exact Eventually.of_forall (fun scale => (whole_ir_integrand_measurable scale test x).aestronglyMeasurable)
  · exact Eventually.of_forall (fun scale => Eventually.of_forall (whole_ir_integrand_bound scale test x))
  · exact em_physical_coulomb_budget_integrable wholeStaticBudget test
  · filter_upwards [volume.ae_ne (0 : PhysicalMomentum)] with frequency nonzero
    have kNonzero : sourceSpatialMomentum frequency ≠ 0 :=
      smul_ne_zero (mul_ne_zero (by norm_num) Real.pi_pos.ne') nonzero
    exact (tendsto_const_nhds (x := sourceSpatialPhase frequency x * test frequency)).smul
      (whole_ir_symbol_limit (sourceSpatialMomentum frequency) (whole_spatial_positive _ kNonzero))

private theorem whole_spatial_scaled_square (scale : ℝ) (k : PhysicalMomentum) :
    spatialSquare (scale • k) = scale^2 * spatialSquare k := by
  simp only [spatialSquare, Pi.smul_apply, smul_eq_mul]
  ring

/-- The Coulomb weight is generated by the same original momentum dilation. -/
theorem whole_coulomb_ir_symbol_scaling (scale : ℝ) (positive : 0 < scale)
    (k : PhysicalMomentum) :
    wholeCoulombIRSymbol scale k = (scale^2 : ℝ) • wholeCoulombIRSymbol 1 (scale • k) := by
  have radius : Real.sqrt (spatialSquare (scale • k)) = scale * Real.sqrt (spatialSquare k) := by
    rw [whole_spatial_scaled_square, Real.sqrt_mul (sq_nonneg _),
      Real.sqrt_sq_eq_abs, abs_of_pos positive]
  have spatial : 0 < spatialSquare (scale • k) ↔ 0 < spatialSquare k := by
    rw [whole_spatial_scaled_square]
    exact mul_pos_iff_of_pos_left (sq_pos_of_pos positive)
  have momentum : sourceStaticSpatialMomentum (scale • k) 1 = sourceStaticSpatialMomentum k scale := by
    ext j
    fin_cases j <;> simp [sourceStaticSpatialMomentum, Pi.smul_apply, smul_eq_mul, Complex.ofReal_mul]
  simp only [wholeCoulombIRSymbol, radius, spatial, show (0:ℝ) < 1 by norm_num,
    positive, true_and, one_mul, momentum, one_pow, one_smul]
  split_ifs <;> simp only [smul_zero]

private theorem whole_physical_momentum_dilation (scale : ℝ) (frequency : PhysicalMomentum) :
    sourceSpatialMomentum (scale • frequency) = scale • sourceSpatialMomentum frequency := by
  simp only [sourceSpatialMomentum, smul_smul]
  congr 1
  ring

private theorem whole_physical_phase_dilation (scale : ℝ) (frequency x : PhysicalMomentum) :
    sourceSpatialPhase (scale • frequency) x = sourceSpatialPhase frequency (scale • x) := by
  unfold sourceSpatialPhase
  rw [whole_physical_momentum_dilation]
  congr 3
  apply Finset.sum_congr rfl
  intro j _
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

/-- The full original packet dilates with Coulomb degree minus one, from its actual 3D Jacobian. -/
theorem whole_coulomb_ir_packet_original_dilation (scale : ℝ) (positive : 0 < scale)
    (test : 𝓢(PhysicalMomentum, ℂ)) (x : PhysicalMomentum) :
    wholeCoulombIRPacket scale test x = scale⁻¹ •
      wholeCoulombIRPacket 1 (sourceDilatedTest scale⁻¹ (inv_ne_zero positive.ne') test) (scale⁻¹ • x) := by
  let f : PhysicalMomentum → WholeMatrix := fun frequency =>
    (sourceSpatialPhase frequency (scale⁻¹ • x) *
      sourceDilatedTest scale⁻¹ (inv_ne_zero positive.ne') test frequency) •
      wholeCoulombIRSymbol 1 (sourceSpatialMomentum frequency)
  have point (frequency : PhysicalMomentum) : (scale^2 : ℝ) • f (scale • frequency) =
      (sourceSpatialPhase frequency x * test frequency) •
        wholeCoulombIRSymbol scale (sourceSpatialMomentum frequency) := by
    simp only [f, whole_physical_phase_dilation, sourceDilatedTest_apply, smul_smul,
      inv_mul_cancel₀ positive.ne', mul_inv_cancel₀ positive.ne', one_smul, whole_physical_momentum_dilation,
      whole_coulomb_ir_symbol_scaling scale positive]
    simpa only [smul_smul] using smul_comm (scale^2 : ℝ)
      (sourceSpatialPhase frequency x * test frequency)
      (wholeCoulombIRSymbol 1 (scale • sourceSpatialMomentum frequency))
  have generated := MeasureTheory.Measure.integral_comp_smul (μ := volume) f scale
  have scaled := congrArg (fun M : WholeMatrix => (scale^2 : ℝ) • M) generated
  rw [←integral_smul] at scaled
  simp only [point, Module.finrank_fin_fun, abs_of_pos (inv_pos.mpr (pow_pos positive 3)),
    smul_smul] at scaled
  have price : scale^2 * (scale^3)⁻¹ = scale⁻¹ := by field_simp [positive.ne']
  simpa only [price, wholeCoulombIRPacket, f] using scaled

end LowEnergy.GaussComposite.ActualWholeStatic
