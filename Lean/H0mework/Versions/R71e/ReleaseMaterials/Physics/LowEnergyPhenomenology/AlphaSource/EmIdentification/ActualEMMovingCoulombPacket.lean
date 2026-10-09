import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualWholeCoulombIR
import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualEMNewtonConvolution
import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualEMMovingWholeStatic

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualEMMovingCoulombPacket
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open Stage10 CanonicalGradedSpatialSource PreparationVacuumStaticSpatialSource
open PreparationVacuumPhysicalFeedback PreparationVacuumPhysicalCharacteristic
open PreparationVacuumPhysicalPoleSheet PreparationVacuumStaticPoleResponse
open PreparationPhysicalStaticSpatialCouplingReturn ActualWholeStatic ActualEMCarrierOwn
open PreparationVacuumOriginalGreenFeedback MeasureTheory Filter Set
open scoped Matrix BigOperators Topology Matrix.Norms.Operator SchwartzMap
local instance : MeasurableSpace WholeMatrix := borel _
local instance : BorelSpace WholeMatrix := ⟨rfl⟩
attribute [local irreducible] wholeCoulombIRSymbol wholeStaticLimit
  emUnitTransferTest emUnitTransferCurrent emMovingUnitTest emMovingUnitCurrent
  emMovingUnitOperator emMovingFieldKernel

private theorem moving_read_complex_smul (detector source : ActualEMObservationEnd) (branch : Fin 2)
    (transfer : PhysicalMomentum × ℂ) (a : ℂ) (M : WholeMatrix) :
    emMovingWholeRead detector source branch transfer (a • M) =
      a * emMovingWholeRead detector source branch transfer M := by
  simp only [emMovingWholeRead, Matrix.smul_mulVec, map_smul, smul_eq_mul]
  ring

private theorem moving_read_real_smul (detector source : ActualEMObservationEnd) (branch : Fin 2)
    (transfer : PhysicalMomentum × ℂ) (a : ℝ) (M : WholeMatrix) :
    emMovingWholeRead detector source branch transfer (a • M) =
      (a : ℂ) * emMovingWholeRead detector source branch transfer M := by
  have scalar : a • M = (a : ℂ) • M := by
    ext i j
    simp only [Matrix.smul_apply, Complex.real_smul, smul_eq_mul]
  rw [scalar, moving_read_complex_smul]

private theorem moving_read_zero (detector source : ActualEMObservationEnd) (branch : Fin 2)
    (transfer : PhysicalMomentum × ℂ) : emMovingWholeRead detector source branch transfer 0 = 0 := by
  simp only [emMovingWholeRead, Matrix.zero_mulVec, map_zero, mul_zero]

private theorem moving_read_joint_continuous (detector source : ActualEMObservationEnd) (branch : Fin 2)
    (hzd : detector.q.z.im≠0) (hwd : detector.q.w.im≠0) (hzs : source.q.z.im≠0) (hws : source.q.w.im≠0) :
    Continuous (fun p : (PhysicalMomentum × ℂ) × WholeMatrix => emMovingWholeRead detector source branch p.1 p.2) := by
  have d : Continuous (fun p : (PhysicalMomentum × ℂ) × WholeMatrix => emUnitTransferTest detector 1 p.1) :=
    (em_unit_transfer_test_continuous detector 1 hzd hwd).comp continuous_fst
  have s : Continuous (fun p : (PhysicalMomentum × ℂ) × WholeMatrix => emUnitTransferCurrent source (-1) p.1) :=
    (em_unit_transfer_current_continuous source (-1) hzs hws).comp continuous_fst
  unfold emMovingWholeRead
  exact (d.clm_apply (continuous_snd.matrix_mulVec s)).const_mul
    (((ActionNormalization.phaseMomentum * sourceSpeed branch : ℝ) : ℂ)⁻¹)

/-- Both moving currents and the whole source Green generate this common IR window. -/
def movingCoulombRadius (detector source : ActualEMObservationEnd) (branch : Fin 2)
    (hzd : detector.q.z.im≠0) (hwd : detector.q.w.im≠0) (hzs : source.q.z.im≠0) (hws : source.q.w.im≠0) : ℝ :=
  min wholeSourceIRRadius (Classical.choose (em_moving_whole_static_domination detector source branch hzd hwd hzs hws))

theorem moving_coulomb_radius_positive (detector source : ActualEMObservationEnd) (branch : Fin 2)
    (hzd : detector.q.z.im≠0) (hwd : detector.q.w.im≠0) (hzs : source.q.z.im≠0) (hws : source.q.w.im≠0) :
    0 < movingCoulombRadius detector source branch hzd hwd hzs hws :=
  lt_min whole_source_ir_radius_positive
    (Classical.choose_spec (em_moving_whole_static_domination detector source branch hzd hwd hzs hws)).1

/-- The full source and detector move at opposite momenta of this same static Fourier event. -/
def movingCoulombSymbol (detector source : ActualEMObservationEnd) (branch : Fin 2)
    (hzd : detector.q.z.im≠0) (hwd : detector.q.w.im≠0) (hzs : source.q.z.im≠0) (hws : source.q.w.im≠0)
    (scale : ℝ) (k : PhysicalMomentum) : ℂ :=
  if 0 < scale ∧ 0 < spatialSquare k ∧
      scale * Real.sqrt (spatialSquare k) < movingCoulombRadius detector source branch hzd hwd hzs hws then
    emMovingWholeRead detector source branch (scale • k, 0) (wholeCoulombIRSymbol scale k)
  else 0

private def movingDirection (k : PhysicalMomentum) : PhysicalMomentum := (Real.sqrt (spatialSquare k))⁻¹ • k

private theorem moving_direction_unit (k : PhysicalMomentum) (spatial : 0 < spatialSquare k) :
    spatialSquare (movingDirection k) = 1 := by
  have nz := (Real.sqrt_pos.mpr spatial).ne'
  have square := Real.sq_sqrt spatial.le
  calc
    _ = (Real.sqrt (spatialSquare k))⁻¹^2 * spatialSquare k := by
      simp only [movingDirection, spatialSquare, Pi.smul_apply, smul_eq_mul]
      ring
    _ = 1 := by field_simp [nz]; exact square.symm

private theorem moving_same_ray (scale : ℝ) (k : PhysicalMomentum) (spatial : 0 < spatialSquare k) :
    scale • k = (scale * Real.sqrt (spatialSquare k)) • movingDirection k := by
  rw [movingDirection, smul_smul, mul_inv_cancel_right₀ (Real.sqrt_pos.mpr spatial).ne']

private theorem moving_symbol_actual (detector source : ActualEMObservationEnd) (branch : Fin 2)
    (hzd : detector.q.z.im≠0) (hwd : detector.q.w.im≠0) (hzs : source.q.z.im≠0) (hws : source.q.w.im≠0)
    (scale : ℝ) (k : PhysicalMomentum) (positive : 0 < scale) (spatial : 0 < spatialSquare k)
    (inside : scale * Real.sqrt (spatialSquare k) < movingCoulombRadius detector source branch hzd hwd hzs hws) :
    movingCoulombSymbol detector source branch hzd hwd hzs hws scale k =
      (((spatialSquare k)⁻¹ : ℝ) : ℂ) *
        emMovingWholeRead detector source branch ((scale * Real.sqrt (spatialSquare k)) • movingDirection k, 0)
          (((scale * Real.sqrt (spatialSquare k))^2 : ℝ) •
            sourceGreen (sourceSpatialStaticRegularPoint (movingDirection k) (moving_direction_unit k spatial)
              ⟨scale * Real.sqrt (spatialSquare k), mul_pos positive (Real.sqrt_pos.mpr spatial),
                inside.le.trans ((min_le_left _ _).trans (min_le_left _ _))⟩)) := by
  rw [movingCoulombSymbol, if_pos ⟨positive, spatial, inside⟩,
    whole_coulomb_ir_symbol_actual scale k positive spatial (inside.trans_le (min_le_left _ _)),
    moving_read_real_smul, moving_same_ray scale k spatial]
  rfl

/-- A source-fixed all-direction price pays the full moving Coulomb response under its true Newton singularity. -/
theorem moving_coulomb_symbol_bound (detector source : ActualEMObservationEnd) (branch : Fin 2)
    (hzd : detector.q.z.im≠0) (hwd : detector.q.w.im≠0) (hzs : source.q.z.im≠0) (hws : source.q.w.im≠0)
    (scale : ℝ) (k : PhysicalMomentum) :
    ‖movingCoulombSymbol detector source branch hzd hwd hzs hws scale k‖ ≤
      emMovingWholeBudget detector source branch / spatialSquare k := by
  have budget : 0 ≤ emMovingWholeBudget detector source branch := by
    unfold emMovingWholeBudget
    exact mul_nonneg (mul_nonneg (mul_nonneg (norm_nonneg _)
      (em_moving_unit_budget_positive detector 1).le) whole_static_budget_nonnegative)
      (em_moving_unit_budget_positive source (-1)).le
  have square : 0 ≤ spatialSquare k := by unfold spatialSquare; positivity
  by_cases active : 0 < scale ∧ 0 < spatialSquare k ∧
      scale * Real.sqrt (spatialSquare k) < movingCoulombRadius detector source branch hzd hwd hzs hws
  · rw [moving_symbol_actual detector source branch hzd hwd hzs hws scale k active.1 active.2.1 active.2.2,
      norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr active.2.1)]
    let r : staticDomain := ⟨scale * Real.sqrt (spatialSquare k),
      mul_pos active.1 (Real.sqrt_pos.mpr active.2.1),
      active.2.2.le.trans ((min_le_left _ _).trans (min_le_left _ _))⟩
    have paid := (Classical.choose_spec (em_moving_whole_static_domination detector source branch hzd hwd hzs hws)).2
      r (active.2.2.trans_le (min_le_right _ _)) (movingDirection k) (moving_direction_unit k active.2.1)
    calc
      _ ≤ (spatialSquare k)⁻¹ * emMovingWholeBudget detector source branch :=
        mul_le_mul_of_nonneg_left paid (inv_nonneg.mpr active.2.1.le)
      _ = _ := by rw [div_eq_mul_inv, mul_comm]
  · simp only [movingCoulombSymbol, if_neg active, norm_zero]
    exact div_nonneg budget square

private theorem moving_symbol_limit (detector source : ActualEMObservationEnd) (branch : Fin 2)
    (hzd : detector.q.z.im≠0) (hwd : detector.q.w.im≠0) (hzs : source.q.z.im≠0) (hws : source.q.w.im≠0)
    (k : PhysicalMomentum) (spatial : 0 < spatialSquare k) :
    Tendsto (fun scale : ℝ => movingCoulombSymbol detector source branch hzd hwd hzs hws scale k) (𝓝[>] 0)
      (𝓝 ((((spatialSquare k)⁻¹ : ℝ) : ℂ) * emMovingWholeRead detector source branch 0 wholeStaticLimit)) := by
  let radial := Real.sqrt (spatialSquare k)
  have rp : 0 < radial := Real.sqrt_pos.mpr spatial
  apply Metric.tendsto_nhds.mpr
  intro epsilon ep
  obtain ⟨radius, positive, paid⟩ := em_moving_whole_static_uniform detector source branch hzd hwd hzs hws
    (epsilon * spatialSquare k / 2) (by positivity)
  have near : ∀ᶠ scale : ℝ in 𝓝[>] 0,
      scale < min (movingCoulombRadius detector source branch hzd hwd hzs hws) radius / radial :=
    nhdsWithin_le_nhds (gt_mem_nhds (div_pos
      (lt_min (moving_coulomb_radius_positive detector source branch hzd hwd hzs hws) positive) rp))
  filter_upwards [self_mem_nhdsWithin, near] with scale scalePos small
  have product : scale * radial < min (movingCoulombRadius detector source branch hzd hwd hzs hws) radius :=
    (lt_div_iff₀ rp).mp small
  have inside := product.trans_le (min_le_left _ _)
  let r : staticDomain := ⟨scale * radial, mul_pos scalePos rp,
    inside.le.trans ((min_le_left _ _).trans (min_le_left _ _))⟩
  have error := paid r (product.trans_le (min_le_right _ _)) (movingDirection k) (moving_direction_unit k spatial)
  rw [moving_symbol_actual detector source branch hzd hwd hzs hws scale k scalePos spatial inside,
    dist_eq_norm, ←mul_sub, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr spatial)]
  calc
    _ ≤ (spatialSquare k)⁻¹ * (epsilon * spatialSquare k / 2) :=
      mul_le_mul_of_nonneg_left error (inv_nonneg.mpr spatial.le)
    _ = epsilon / 2 := by field_simp [spatial.ne']
    _ < epsilon := by linarith

/-- Both independent moving currents are observed inside this actual original Fourier integral. -/
def movingCoulombPacket (detector source : ActualEMObservationEnd) (branch : Fin 2)
    (hzd : detector.q.z.im≠0) (hwd : detector.q.w.im≠0) (hzs : source.q.z.im≠0) (hws : source.q.w.im≠0)
    (scale : ℝ) (test : 𝓢(PhysicalMomentum, ℂ)) (x : PhysicalMomentum) : ℂ :=
  ∫ frequency, sourceSpatialPhase frequency x * test frequency *
    movingCoulombSymbol detector source branch hzd hwd hzs hws scale (sourceSpatialMomentum frequency)

private theorem moving_integrand_measurable (detector source : ActualEMObservationEnd) (branch : Fin 2)
    (hzd : detector.q.z.im≠0) (hwd : detector.q.w.im≠0) (hzs : source.q.z.im≠0) (hws : source.q.w.im≠0)
    (scale : ℝ) (test : 𝓢(PhysicalMomentum, ℂ)) (x : PhysicalMomentum) :
    AEStronglyMeasurable (fun frequency => sourceSpatialPhase frequency x * test frequency *
      movingCoulombSymbol detector source branch hzd hwd hzs hws scale (sourceSpatialMomentum frequency)) volume := by
  have transfer : Continuous (fun frequency => ((scale • sourceSpatialMomentum frequency, (0:ℂ)) : PhysicalMomentum × ℂ)) := by
    unfold sourceSpatialMomentum
    fun_prop
  have base := (whole_coulomb_ir_packet_integrable scale test x).aestronglyMeasurable
  have joint := (moving_read_joint_continuous detector source branch hzd hwd hzs hws).comp_aestronglyMeasurable
    (transfer.aestronglyMeasurable.prodMk base)
  have active : MeasurableSet {frequency : PhysicalMomentum | 0 < scale ∧
      0 < spatialSquare (sourceSpatialMomentum frequency) ∧
      scale * Real.sqrt (spatialSquare (sourceSpatialMomentum frequency)) < movingCoulombRadius detector source branch hzd hwd hzs hws} := by
    have h1 : MeasurableSet {frequency : PhysicalMomentum | 0 < scale} := by
      by_cases positive : 0 < scale <;> simp [positive]
    have square : Measurable (fun frequency => spatialSquare (sourceSpatialMomentum frequency)) := by
      unfold spatialSquare sourceSpatialMomentum
      fun_prop
    have hr : Measurable (fun frequency => scale * Real.sqrt (spatialSquare (sourceSpatialMomentum frequency))) := by
      unfold spatialSquare sourceSpatialMomentum
      fun_prop
    exact h1.inter ((measurableSet_lt measurable_const square).inter (measurableSet_lt hr measurable_const))
  have indicator := joint.indicator active
  convert indicator using 1 <;> first
  | rfl
  | (funext frequency
     simp only [Set.indicator_apply, Set.mem_ofPred_eq, movingCoulombSymbol]
     split_ifs <;> simp only [moving_read_complex_smul, mul_zero])

private theorem moving_integrand_bound (detector source : ActualEMObservationEnd) (branch : Fin 2)
    (hzd : detector.q.z.im≠0) (hwd : detector.q.w.im≠0) (hzs : source.q.z.im≠0) (hws : source.q.w.im≠0)
    (scale : ℝ) (test : 𝓢(PhysicalMomentum, ℂ)) (x frequency : PhysicalMomentum) :
    ‖sourceSpatialPhase frequency x * test frequency *
      movingCoulombSymbol detector source branch hzd hwd hzs hws scale (sourceSpatialMomentum frequency)‖ ≤
      emMovingWholeBudget detector source branch * ‖test frequency‖ / spatialSquare (sourceSpatialMomentum frequency) := by
  have phase : ‖sourceSpatialPhase frequency x‖ = 1 := by simp [sourceSpatialPhase, Complex.norm_exp]
  simp only [norm_mul, phase, one_mul]
  calc
    _ ≤ ‖test frequency‖ * (emMovingWholeBudget detector source branch / spatialSquare (sourceSpatialMomentum frequency)) :=
      mul_le_mul_of_nonneg_left (moving_coulomb_symbol_bound detector source branch hzd hwd hzs hws scale _) (norm_nonneg _)
    _ = _ := by ring

theorem moving_coulomb_packet_integrable (detector source : ActualEMObservationEnd) (branch : Fin 2)
    (hzd : detector.q.z.im≠0) (hwd : detector.q.w.im≠0) (hzs : source.q.z.im≠0) (hws : source.q.w.im≠0)
    (scale : ℝ) (test : 𝓢(PhysicalMomentum, ℂ)) (x : PhysicalMomentum) :
    Integrable (fun frequency => sourceSpatialPhase frequency x * test frequency *
      movingCoulombSymbol detector source branch hzd hwd hzs hws scale (sourceSpatialMomentum frequency)) :=
  (em_physical_coulomb_budget_integrable (emMovingWholeBudget detector source branch) test).mono'
    (moving_integrand_measurable detector source branch hzd hwd hzs hws scale test x)
    (Eventually.of_forall (moving_integrand_bound detector source branch hzd hwd hzs hws scale test x))

private theorem moving_spatial_positive (k : PhysicalMomentum) (nonzero : k ≠ 0) : 0 < spatialSquare k := by
  have positive : 0 ≤ spatialSquare k := by unfold spatialSquare; positivity
  by_contra failed
  have zero : spatialSquare k = 0 := le_antisymm (not_lt.mp failed) positive
  apply nonzero
  ext i
  fin_cases i
  · change k 0 = 0
    unfold spatialSquare at zero
    nlinarith [sq_nonneg (k 0), sq_nonneg (k 1), sq_nonneg (k 2)]
  · change k 1 = 0
    unfold spatialSquare at zero
    nlinarith [sq_nonneg (k 0), sq_nonneg (k 1), sq_nonneg (k 2)]
  · change k 2 = 0
    unfold spatialSquare at zero
    nlinarith [sq_nonneg (k 0), sq_nonneg (k 1), sq_nonneg (k 2)]

private theorem moving_newton_integral (detector source : ActualEMObservationEnd) (branch : Fin 2)
    (test : 𝓢(PhysicalMomentum, ℂ)) (x : PhysicalMomentum) :
    (∫ frequency, sourceSpatialPhase frequency x * test frequency *
      ((((spatialSquare (sourceSpatialMomentum frequency))⁻¹ : ℝ) : ℂ) *
        emMovingWholeRead detector source branch 0 wholeStaticLimit)) =
      emNewtonPacket 0 0 test x * emMovingWholeRead detector source branch 0 wholeStaticLimit := by
  simp only [←mul_assoc, Complex.ofReal_inv]
  rw [integral_mul_const]
  congr 1
  change (∫ frequency, sourceSpatialPhase frequency x * test frequency *
    (spatialSquare (sourceSpatialMomentum frequency) : ℂ)⁻¹) =
    ∫ frequency, (1:ℂ) * sourceSpatialPhase frequency x * test frequency *
      ((spatialSquare (sourceSpatialMomentum frequency) : ℂ) + (0:ℂ)^2 * (0:ℂ)^2)⁻¹
  simp only [one_mul, zero_pow (by norm_num : 2 ≠ 0), zero_mul, add_zero]

/-- The genuine same-transfer moving full289 response enters the source Newton integral. -/
theorem moving_coulomb_packet_limit (detector source : ActualEMObservationEnd) (branch : Fin 2)
    (hzd : detector.q.z.im≠0) (hwd : detector.q.w.im≠0) (hzs : source.q.z.im≠0) (hws : source.q.w.im≠0)
    (test : 𝓢(PhysicalMomentum, ℂ)) (x : PhysicalMomentum) :
    Tendsto (fun scale : ℝ => movingCoulombPacket detector source branch hzd hwd hzs hws scale test x)
      (𝓝[>] 0) (𝓝 (emNewtonPacket 0 0 test x * emMovingWholeRead detector source branch 0 wholeStaticLimit)) := by
  unfold movingCoulombPacket
  rw [←moving_newton_integral]
  apply tendsto_integral_filter_of_dominated_convergence (μ := volume)
    (fun frequency => emMovingWholeBudget detector source branch * ‖test frequency‖ / spatialSquare (sourceSpatialMomentum frequency))
  · exact Eventually.of_forall (fun scale => moving_integrand_measurable detector source branch hzd hwd hzs hws scale test x)
  · exact Eventually.of_forall (fun scale => Eventually.of_forall (moving_integrand_bound detector source branch hzd hwd hzs hws scale test x))
  · exact em_physical_coulomb_budget_integrable (emMovingWholeBudget detector source branch) test
  · filter_upwards [volume.ae_ne (0 : PhysicalMomentum)] with frequency nonzero
    have kNonzero : sourceSpatialMomentum frequency ≠ 0 :=
      smul_ne_zero (mul_ne_zero (by norm_num) Real.pi_pos.ne') nonzero
    exact (tendsto_const_nhds (x := sourceSpatialPhase frequency x * test frequency)).mul
      (moving_symbol_limit detector source branch hzd hwd hzs hws _ (moving_spatial_positive _ kNonzero))

/-- The full moving source/detector observation consumes one actual Fourier4pi. -/
theorem moving_coulomb_spatial_limit (detector source : ActualEMObservationEnd) (branch : Fin 2)
    (hzd : detector.q.z.im≠0) (hwd : detector.q.w.im≠0) (hzs : source.q.z.im≠0) (hws : source.q.w.im≠0)
    (test : 𝓢(PhysicalMomentum, ℂ)) (x : PhysicalMomentum) :
    Tendsto (fun scale : ℝ => movingCoulombPacket detector source branch hzd hwd hzs hws scale test x)
      (𝓝[>] 0) (𝓝 ((∫ y, (4*(Real.pi:ℂ)*(Real.sqrt (spatialSquare y):ℂ))⁻¹ * emPacket test (x-y)) *
        emMovingWholeRead detector source branch 0 wholeStaticLimit)) := by
  simpa only [em_newton_massless_convolution] using
    moving_coulomb_packet_limit detector source branch hzd hwd hzs hws test x

/-- The original charged rest preparations are the zero-transfer limit of the actual moving integral. -/
theorem moving_coulomb_spatial_limit_rest (branch : Fin 2) (qd qs : PhysicalResponsePoint)
    (dL dR sL sR : Fin 2) (T S : ℝ)
    (hzd : qd.z.im≠0) (hwd : qd.w.im≠0) (hzs : qs.z.im≠0) (hws : qs.w.im≠0)
    (test : 𝓢(PhysicalMomentum, ℂ)) (x : PhysicalMomentum) :
    Tendsto (fun scale : ℝ => movingCoulombPacket
      ⟨qd,0,dL,0,dR,0,T⟩ ⟨qs,0,sL,0,sR,0,S⟩ branch hzd hwd hzs hws scale test x)
      (𝓝[>] 0) (𝓝 ((∫ y, (4*(Real.pi:ℂ)*(Real.sqrt (spatialSquare y):ℂ))⁻¹ * emPacket test (x-y)) *
        (ActualMasslessStaticPair.actualStaticPairSeed *
          ActualMasslessCurrent.actualUnitMasslessWeight qd dL dR 0 T *
          ActualMasslessCurrent.actualUnitMasslessWeight qs sL sR 0 S /
          ((ActionNormalization.phaseMomentum * sourceSpeed branch : ℝ) : ℂ)))) := by
  simpa only [em_moving_whole_origin_rest] using
    moving_coulomb_spatial_limit ⟨qd,0,dL,0,dR,0,T⟩ ⟨qs,0,sL,0,sR,0,S⟩ branch hzd hwd hzs hws test x

end LowEnergy.GaussComposite.ActualEMMovingCoulombPacket
