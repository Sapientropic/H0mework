import H0mework.Versions.R9c73a630.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedFullCoulomb

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualDressedMovingCoulomb
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open Stage10 CanonicalGradedSpatialSource PreparationVacuumStaticSpatialSource
open PreparationVacuumPhysicalFeedback PreparationVacuumPhysicalCharacteristic
open PreparationVacuumPhysicalPoleSheet PreparationVacuumStaticPoleResponse
open PreparationPhysicalStaticSpatialCouplingReturn ActualWholeStatic ActualEMCarrierOwn
open PreparationVacuumOriginalGreenFeedback MeasureTheory Filter Set
open ActualDressedFullCoulomb
open scoped Matrix BigOperators Topology Matrix.Norms.Operator SchwartzMap
local instance : MeasurableSpace WholeMatrix := borel _
local instance : BorelSpace WholeMatrix := ⟨rfl⟩
attribute [local irreducible] wholeCoulombIRSymbol wholeStaticLimit dressedCurrent

private theorem moving_read_complex_smul (detector source : DressedEvent)
    (transfer : PhysicalMomentum) (a : ℂ) (M : WholeMatrix) :
    dressedMatrixRead detector source transfer (a • M)=a*dressedMatrixRead detector source transfer M :=
  dressed_matrix_read_complex_smul detector source transfer a M

private theorem moving_read_real_smul (detector source : DressedEvent)
    (transfer : PhysicalMomentum) (a : ℝ) (M : WholeMatrix) :
    dressedMatrixRead detector source transfer (a • M)=(a : ℂ)*dressedMatrixRead detector source transfer M := by
  exact (dressedMatrixRead detector source transfer).map_smul a M

private theorem moving_read_zero (detector source : DressedEvent) (transfer : PhysicalMomentum) :
    dressedMatrixRead detector source transfer 0=0 := map_zero _

theorem dressed_matrix_joint_continuous (detector source : DressedEvent) :
    Continuous (fun p : PhysicalMomentum × WholeMatrix => dressedMatrixRead detector source p.1 p.2) := by
  have d : Continuous (fun p : PhysicalMomentum × WholeMatrix => dressedCurrent detector (-p.1)) :=
    (dressed_current_continuous detector).comp continuous_fst.neg
  have s : Continuous (fun p : PhysicalMomentum × WholeMatrix => dressedCurrent source p.1) :=
    (dressed_current_continuous source).comp continuous_fst
  change Continuous (fun p : PhysicalMomentum × WholeMatrix =>
    ∑ i, dressedCurrent detector (-p.1) i * ∑ j, p.2 i j * dressedCurrent source p.1 j)
  exact continuous_finsetSum _ fun i _ => ((continuous_apply i).comp d).mul
    (continuous_finsetSum _ fun j _ =>
      (((continuous_apply j).comp ((continuous_apply i).comp continuous_snd)).mul ((continuous_apply j).comp s)))

private theorem moving_direction_bound (n : PhysicalMomentum) (unit : spatialSquare n=1) : ‖n‖≤1 := by
  apply (pi_norm_le_iff_of_nonneg (by norm_num : (0:ℝ)≤1)).mpr
  intro j
  have paid:=sourceStaticSpatialMomentum_price n unit 1 (by norm_num) j.succ
  fin_cases j
  all_goals simpa [sourceStaticSpatialMomentum] using paid

/-- Same-source continuous currents consume the full289 all-direction static limit. -/
theorem dressed_moving_static_uniform (detector source : DressedEvent)
    (epsilon : ℝ) (positive : 0<epsilon) :
    ∃ radius : ℝ, 0<radius ∧ ∀ r : staticDomain, r.val<radius →
      ∀ n : PhysicalMomentum, ∀ unit : spatialSquare n=1,
        ‖dressedMatrixRead detector source (r.val • n)
          ((r.val^2:ℝ) • sourceGreen (sourceSpatialStaticRegularPoint n unit r))-
            dressedMatrixRead detector source 0 wholeStaticLimit‖≤epsilon := by
  have near:=((dressed_matrix_joint_continuous detector source).continuousAt (x:=(0,wholeStaticLimit))).tendsto.eventually
    (Metric.ball_mem_nhds (dressedMatrixRead detector source 0 wholeStaticLimit) positive)
  obtain ⟨rho,rhop,inside⟩:=Metric.mem_nhds_iff.mp near
  obtain ⟨matrixRadius,mrp,matrixPaid⟩:=whole_static_green_uniform (rho/2) (by positivity)
  refine ⟨min matrixRadius (rho/2),lt_min mrp (by positivity),?_⟩
  intro r small n unit
  have matrixBound := matrixPaid r (lt_of_lt_of_le small (min_le_left _ _)) n unit
  have transferBound : ‖r.val • n‖ < rho/2 := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos r.property.1]
    exact (mul_le_mul_of_nonneg_left (moving_direction_bound n unit) r.property.1.le).trans_lt
      (by simpa only [mul_one] using (lt_of_lt_of_le small (min_le_right _ _)))
  have membership : ((r.val • n,(r.val^2:ℝ) • sourceGreen (sourceSpatialStaticRegularPoint n unit r)):
      PhysicalMomentum × WholeMatrix)∈Metric.ball (0,wholeStaticLimit) rho := by
    rw [Metric.mem_ball,Prod.dist_eq,max_lt_iff,dist_zero_right,dist_eq_norm]
    exact ⟨transferBound.trans (by linarith),matrixBound.trans_lt (by linarith)⟩
  have paid:=inside membership
  change dist (dressedMatrixRead detector source (r.val • n)
    ((r.val^2:ℝ) • sourceGreen (sourceSpatialStaticRegularPoint n unit r)))
      (dressedMatrixRead detector source 0 wholeStaticLimit)<epsilon at paid
  simpa only [dist_eq_norm] using paid.le

/-- The actual moving observable generates its own local domination price. -/
def dressedMovingBudget (detector source : DressedEvent) : ℝ :=
  1+‖dressedMatrixRead detector source 0 wholeStaticLimit‖

theorem dressed_moving_static_domination (detector source : DressedEvent) :
    ∃ radius : ℝ, 0<radius ∧ ∀ r : staticDomain, r.val<radius →
      ∀ n : PhysicalMomentum, ∀ unit : spatialSquare n=1,
        ‖dressedMatrixRead detector source (r.val • n)
          ((r.val^2:ℝ) • sourceGreen (sourceSpatialStaticRegularPoint n unit r))‖≤dressedMovingBudget detector source := by
  obtain ⟨radius,positive,paid⟩:=dressed_moving_static_uniform detector source 1 (by norm_num)
  refine ⟨radius,positive,?_⟩
  intro r small n unit
  unfold dressedMovingBudget
  exact (norm_le_norm_sub_add _ (dressedMatrixRead detector source 0 wholeStaticLimit)).trans
    (add_le_add (paid r small n unit) (le_refl _))

/-- Both moving currents and the whole source Green generate this common IR window. -/
def movingCoulombRadius (detector source : DressedEvent)
 : ℝ :=
  min wholeSourceIRRadius (Classical.choose (dressed_moving_static_domination detector source))

theorem moving_coulomb_radius_positive (detector source : DressedEvent)
 :
    0 < movingCoulombRadius detector source :=
  lt_min whole_source_ir_radius_positive
    (Classical.choose_spec (dressed_moving_static_domination detector source)).1

/-- The full source and detector move at opposite momenta of this same static Fourier event. -/
def movingCoulombSymbol (detector source : DressedEvent)
    (scale : ℝ) (k : PhysicalMomentum) : ℂ :=
  if 0 < scale ∧ 0 < spatialSquare k ∧
      scale * Real.sqrt (spatialSquare k) < movingCoulombRadius detector source then
    dressedMatrixRead detector source (scale • k) (wholeCoulombIRSymbol scale k)
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

private theorem moving_symbol_actual (detector source : DressedEvent)
    (scale : ℝ) (k : PhysicalMomentum) (positive : 0 < scale) (spatial : 0 < spatialSquare k)
    (inside : scale * Real.sqrt (spatialSquare k) < movingCoulombRadius detector source) :
    movingCoulombSymbol detector source scale k =
      (((spatialSquare k)⁻¹ : ℝ) : ℂ) *
        dressedMatrixRead detector source ((scale * Real.sqrt (spatialSquare k)) • movingDirection k)
          (((scale * Real.sqrt (spatialSquare k))^2 : ℝ) •
            sourceGreen (sourceSpatialStaticRegularPoint (movingDirection k) (moving_direction_unit k spatial)
              ⟨scale * Real.sqrt (spatialSquare k), mul_pos positive (Real.sqrt_pos.mpr spatial),
                inside.le.trans ((min_le_left _ _).trans (min_le_left _ _))⟩)) := by
  rw [movingCoulombSymbol, if_pos ⟨positive, spatial, inside⟩,
    whole_coulomb_ir_symbol_actual scale k positive spatial (inside.trans_le (min_le_left _ _)),
    moving_read_real_smul, moving_same_ray scale k spatial]
  rfl

/-- A source-fixed all-direction price pays the full moving Coulomb response under its true Newton singularity. -/
theorem moving_coulomb_symbol_bound (detector source : DressedEvent)
    (scale : ℝ) (k : PhysicalMomentum) :
    ‖movingCoulombSymbol detector source scale k‖ ≤
      dressedMovingBudget detector source / spatialSquare k := by
  have budget : 0 ≤ dressedMovingBudget detector source := by unfold dressedMovingBudget; positivity
  have square : 0 ≤ spatialSquare k := by unfold spatialSquare; positivity
  by_cases active : 0 < scale ∧ 0 < spatialSquare k ∧
      scale * Real.sqrt (spatialSquare k) < movingCoulombRadius detector source
  · rw [moving_symbol_actual detector source scale k active.1 active.2.1 active.2.2,
      norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr active.2.1)]
    let r : staticDomain := ⟨scale * Real.sqrt (spatialSquare k),
      mul_pos active.1 (Real.sqrt_pos.mpr active.2.1),
      active.2.2.le.trans ((min_le_left _ _).trans (min_le_left _ _))⟩
    have paid := (Classical.choose_spec (dressed_moving_static_domination detector source)).2
      r (active.2.2.trans_le (min_le_right _ _)) (movingDirection k) (moving_direction_unit k active.2.1)
    calc
      _ ≤ (spatialSquare k)⁻¹ * dressedMovingBudget detector source :=
        mul_le_mul_of_nonneg_left paid (inv_nonneg.mpr active.2.1.le)
      _ = _ := by rw [div_eq_mul_inv, mul_comm]
  · simp only [movingCoulombSymbol, if_neg active, norm_zero]
    exact div_nonneg budget square

private theorem moving_symbol_limit (detector source : DressedEvent)
    (k : PhysicalMomentum) (spatial : 0 < spatialSquare k) :
    Tendsto (fun scale : ℝ => movingCoulombSymbol detector source scale k) (𝓝[>] 0)
      (𝓝 ((((spatialSquare k)⁻¹ : ℝ) : ℂ) * dressedMatrixRead detector source 0 wholeStaticLimit)) := by
  let radial := Real.sqrt (spatialSquare k)
  have rp : 0 < radial := Real.sqrt_pos.mpr spatial
  apply Metric.tendsto_nhds.mpr
  intro epsilon ep
  obtain ⟨radius, positive, paid⟩ := dressed_moving_static_uniform detector source
    (epsilon * spatialSquare k / 2) (by positivity)
  have near : ∀ᶠ scale : ℝ in 𝓝[>] 0,
      scale < min (movingCoulombRadius detector source) radius / radial :=
    nhdsWithin_le_nhds (gt_mem_nhds (div_pos
      (lt_min (moving_coulomb_radius_positive detector source) positive) rp))
  filter_upwards [self_mem_nhdsWithin, near] with scale scalePos small
  have product : scale * radial < min (movingCoulombRadius detector source) radius :=
    (lt_div_iff₀ rp).mp small
  have inside := product.trans_le (min_le_left _ _)
  let r : staticDomain := ⟨scale * radial, mul_pos scalePos rp,
    inside.le.trans ((min_le_left _ _).trans (min_le_left _ _))⟩
  have error := paid r (product.trans_le (min_le_right _ _)) (movingDirection k) (moving_direction_unit k spatial)
  rw [moving_symbol_actual detector source scale k scalePos spatial inside,
    dist_eq_norm, ←mul_sub, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr spatial)]
  calc
    _ ≤ (spatialSquare k)⁻¹ * (epsilon * spatialSquare k / 2) :=
      mul_le_mul_of_nonneg_left error (inv_nonneg.mpr spatial.le)
    _ = epsilon / 2 := by field_simp [spatial.ne']
    _ < epsilon := by linarith

/-- Both independent moving currents are observed inside this actual original Fourier integral. -/
def movingCoulombPacket (detector source : DressedEvent)
    (scale : ℝ) (test : 𝓢(PhysicalMomentum, ℂ)) (x : PhysicalMomentum) : ℂ :=
  ∫ frequency, sourceSpatialPhase frequency x * test frequency *
    movingCoulombSymbol detector source scale (sourceSpatialMomentum frequency)

private theorem moving_integrand_measurable (detector source : DressedEvent)
    (scale : ℝ) (test : 𝓢(PhysicalMomentum, ℂ)) (x : PhysicalMomentum) :
    AEStronglyMeasurable (fun frequency => sourceSpatialPhase frequency x * test frequency *
      movingCoulombSymbol detector source scale (sourceSpatialMomentum frequency)) volume := by
  have transfer : Continuous (fun frequency => (scale • sourceSpatialMomentum frequency : PhysicalMomentum)) := by
    unfold sourceSpatialMomentum
    fun_prop
  have base := (whole_coulomb_ir_packet_integrable scale test x).aestronglyMeasurable
  have joint := (dressed_matrix_joint_continuous detector source).comp_aestronglyMeasurable
    (transfer.aestronglyMeasurable.prodMk base)
  have active : MeasurableSet {frequency : PhysicalMomentum | 0 < scale ∧
      0 < spatialSquare (sourceSpatialMomentum frequency) ∧
      scale * Real.sqrt (spatialSquare (sourceSpatialMomentum frequency)) < movingCoulombRadius detector source} := by
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

private theorem moving_integrand_bound (detector source : DressedEvent)
    (scale : ℝ) (test : 𝓢(PhysicalMomentum, ℂ)) (x frequency : PhysicalMomentum) :
    ‖sourceSpatialPhase frequency x * test frequency *
      movingCoulombSymbol detector source scale (sourceSpatialMomentum frequency)‖ ≤
      dressedMovingBudget detector source * ‖test frequency‖ / spatialSquare (sourceSpatialMomentum frequency) := by
  have phase : ‖sourceSpatialPhase frequency x‖ = 1 := by simp [sourceSpatialPhase, Complex.norm_exp]
  simp only [norm_mul, phase, one_mul]
  calc
    _ ≤ ‖test frequency‖ * (dressedMovingBudget detector source / spatialSquare (sourceSpatialMomentum frequency)) :=
      mul_le_mul_of_nonneg_left (moving_coulomb_symbol_bound detector source scale _) (norm_nonneg _)
    _ = _ := by ring

theorem moving_coulomb_packet_integrable (detector source : DressedEvent)
    (scale : ℝ) (test : 𝓢(PhysicalMomentum, ℂ)) (x : PhysicalMomentum) :
    Integrable (fun frequency => sourceSpatialPhase frequency x * test frequency *
      movingCoulombSymbol detector source scale (sourceSpatialMomentum frequency)) :=
  (em_physical_coulomb_budget_integrable (dressedMovingBudget detector source) test).mono'
    (moving_integrand_measurable detector source scale test x)
    (Eventually.of_forall (moving_integrand_bound detector source scale test x))

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

private theorem moving_newton_integral (detector source : DressedEvent)
    (test : 𝓢(PhysicalMomentum, ℂ)) (x : PhysicalMomentum) :
    (∫ frequency, sourceSpatialPhase frequency x * test frequency *
      ((((spatialSquare (sourceSpatialMomentum frequency))⁻¹ : ℝ) : ℂ) *
        dressedMatrixRead detector source 0 wholeStaticLimit)) =
      emNewtonPacket 0 0 test x * dressedMatrixRead detector source 0 wholeStaticLimit := by
  simp only [←mul_assoc, Complex.ofReal_inv]
  rw [integral_mul_const]
  congr 1
  change (∫ frequency, sourceSpatialPhase frequency x * test frequency *
    (spatialSquare (sourceSpatialMomentum frequency) : ℂ)⁻¹) =
    ∫ frequency, (1:ℂ) * sourceSpatialPhase frequency x * test frequency *
      ((spatialSquare (sourceSpatialMomentum frequency) : ℂ) + (0:ℂ)^2 * (0:ℂ)^2)⁻¹
  simp only [one_mul, zero_pow (by norm_num : 2 ≠ 0), zero_mul, add_zero]

/-- The genuine same-transfer moving full289 response enters the source Newton integral. -/
theorem moving_coulomb_packet_limit (detector source : DressedEvent)
    (test : 𝓢(PhysicalMomentum, ℂ)) (x : PhysicalMomentum) :
    Tendsto (fun scale : ℝ => movingCoulombPacket detector source scale test x)
      (𝓝[>] 0) (𝓝 (emNewtonPacket 0 0 test x * dressedMatrixRead detector source 0 wholeStaticLimit)) := by
  unfold movingCoulombPacket
  rw [←moving_newton_integral]
  apply tendsto_integral_filter_of_dominated_convergence (μ := volume)
    (fun frequency => dressedMovingBudget detector source * ‖test frequency‖ / spatialSquare (sourceSpatialMomentum frequency))
  · exact Eventually.of_forall (fun scale => moving_integrand_measurable detector source scale test x)
  · exact Eventually.of_forall (fun scale => Eventually.of_forall (moving_integrand_bound detector source scale test x))
  · exact em_physical_coulomb_budget_integrable (dressedMovingBudget detector source) test
  · filter_upwards [volume.ae_ne (0 : PhysicalMomentum)] with frequency nonzero
    have kNonzero : sourceSpatialMomentum frequency ≠ 0 :=
      smul_ne_zero (mul_ne_zero (by norm_num) Real.pi_pos.ne') nonzero
    exact (tendsto_const_nhds (x := sourceSpatialPhase frequency x * test frequency)).mul
      (moving_symbol_limit detector source _ (moving_spatial_positive _ kNonzero))

/-- The full moving source/detector observation consumes one actual Fourier4pi. -/
theorem moving_coulomb_spatial_limit (detector source : DressedEvent)
    (test : 𝓢(PhysicalMomentum, ℂ)) (x : PhysicalMomentum) :
    Tendsto (fun scale : ℝ => movingCoulombPacket detector source scale test x)
      (𝓝[>] 0) (𝓝 ((∫ y, (4*(Real.pi:ℂ)*(Real.sqrt (spatialSquare y):ℂ))⁻¹ * emPacket test (x-y)) *
        dressedMatrixRead detector source 0 wholeStaticLimit)) := by
  simpa only [em_newton_massless_convolution] using
    moving_coulomb_packet_limit detector source test x


end LowEnergy.GaussComposite.ActualDressedMovingCoulomb
