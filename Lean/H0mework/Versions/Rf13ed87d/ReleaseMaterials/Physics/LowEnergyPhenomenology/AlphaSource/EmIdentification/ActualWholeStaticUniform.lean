import H0mework.Versions.Rf13ed87d.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualEMStaticUniform
import H0mework.Versions.Rf13ed87d.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualMasslessFullKernel

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualWholeStatic
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open PreparationVacuumOriginalGreenFeedback PreparationVacuumFullOriginResponse
open PreparationVacuumPhysicalCharacteristic PreparationVacuumPhysicalPoleSheet
open PreparationVacuumWholeOrigin PreparationVacuumFullSlowFieldResponse
open PreparationVacuumNativePoleTensor PreparationVacuumSoftPoleSelection
open PreparationVacuumNativeSlowCoupling
open PreparationPhysicalNativePolarizationEmitter
open PreparationVacuumPhysicalChargedFieldFactor PreparationPhysicalCurvatureSheetLimit
open PreparationPhysicalStaticSpatialCouplingReturn PreparationVacuumStaticPoleResponse
open CanonicalGradedSpatialSource ActualEMCarrierOwn
open Filter Set
open scoped Matrix BigOperators Topology Matrix.Norms.Operator
attribute [local irreducible] sourceNativeFrame originalChange originalReadback contactInverse
  unrestrictedGreen fullInverse fullKernelFrame fullNativeOrigin sourceGreen staticResidue

abbrev WholeMatrix := Matrix (Fin 289) (Fin 289) ℂ

def wholeFrame (p : Fin 4 → ℂ) : WholeMatrix := emStaticRawFrame p

def wholeRegular (p : Fin 4 → ℂ) : WholeMatrix :=
  originalChange p * contactInverse p * originalReadback p +
    originalChange p * unrestrictedGreen p * activeProjection * originalReadback p

private def wholeFrameProjection : WholeMatrix →L[ℝ] WholeMatrix :=
  ({toFun := fun M => M * slowFastInverse
    map_add' := fun M N => by simp only [Matrix.add_mul]
    map_smul' := fun r M => by simp only [Matrix.smul_mul, RingHom.id_apply]} :
      WholeMatrix →ₗ[ℝ] WholeMatrix).toContinuousLinearMap

private theorem whole_frame_continuous : ContinuousAt wholeFrame (0 : Fin 4 → ℂ) := by
  have result := wholeFrameProjection.continuous.continuousAt.comp sourceNativeFrame_smooth.continuousAt
  have same (p : Fin 4 → ℂ) : wholeFrameProjection (sourceNativeFrame p) = wholeFrame p := by
    change sourceNativeFrame p * slowFastInverse = emStaticRawFrame p
    exact em_static_frame_from_native p
  simpa only [Function.comp_def, same] using result

private theorem source_matrix_continuous (terms : List SourceTerm) : Continuous (sourceMatrix terms) := by
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

private theorem whole_regular_continuous : ContinuousAt wholeRegular (0 : Fin 4 → ℂ) := by
  have Oc : Continuous originalChange := by
    unfold originalChange
    exact source_matrix_continuous originalChangeTerms
  have O := Oc.continuousAt (x := (0 : Fin 4 → ℂ))
  have C : ContinuousAt contactInverse (0 : Fin 4 → ℂ) := by
    unfold contactInverse
    exact (source_matrix_continuous contactInverseTerms).continuousAt
  have Rc : Continuous originalReadback := by
    unfold originalReadback
    exact (Oc.comp continuous_neg).matrix_transpose
  exact ((O.mul C).mul Rc.continuousAt).add
    (((O.mul unrestrictedGreen_smooth_origin.continuousAt).mul continuousAt_const).mul Rc.continuousAt)

private def wholeTranspose : WholeMatrix →L[ℝ] WholeMatrix :=
  ({toFun := Matrix.transpose
    map_add' := Matrix.transpose_add
    map_smul' := fun r M => by simp only [Matrix.transpose_smul, RingHom.id_apply]} :
      WholeMatrix →ₗ[ℝ] WholeMatrix).toContinuousLinearMap

private def wholeReflected (p : Fin 4 → ℂ) : WholeMatrix := (wholeFrame (-p)).transpose

private theorem whole_reflected_continuous : ContinuousAt wholeReflected (0 : Fin 4 → ℂ) := by
  have atNeg : ContinuousAt wholeFrame (-(0 : Fin 4 → ℂ)) := by
    simpa only [neg_zero] using whole_frame_continuous
  have F := atNeg.comp (continuous_neg.continuousAt (x := (0 : Fin 4 → ℂ)))
  have same (p : Fin 4 → ℂ) : wholeTranspose (wholeFrame (-p)) = wholeReflected p := rfl
  simpa only [Function.comp_def, same] using wholeTranspose.continuous.continuousAt.comp F

private theorem whole_frame_origin : wholeFrame 0 = fullNativeOrigin := by
  rw [wholeFrame, emStaticRawFrame, rawEffectiveFrame_origin, fullNativeOrigin]

private theorem whole_frame_five (p : Fin 4 → ℂ) : wholeFrame p * fiveProjection = wholeFrame p := by
  simp only [wholeFrame, emStaticRawFrame, rawEffectiveFrame, Matrix.mul_sub,
    Matrix.sub_mul, Matrix.mul_assoc, fullKernel_five]

private theorem whole_frame_native (n : PhysicalMomentum) (unit : spatialSquare n = 1) (r : staticDomain) :
    PreparationVacuumFullOriginResponse.nativeEffectiveFrame (sourceStaticSpatialPoint n unit r) =
      wholeFrame (sourceStaticSpatialMomentum n r.val) := by
  unfold PreparationVacuumFullOriginResponse.nativeEffectiveFrame PreparationVacuumFullOriginResponse.effectiveFrame
    wholeFrame emStaticRawFrame rawEffectiveFrame
    unrestrictedGreen PreparationVacuumFullOriginResponse.complementGreen
  rfl

private theorem whole_regular_field (n : PhysicalMomentum) (unit : spatialSquare n = 1)
    (r : staticDomain) (f : Fin 289 → ℂ) :
    sourceSpatialStaticRegularField n unit r f = wholeRegular (sourceStaticSpatialMomentum n r.val) *ᵥ f := by
  simp only [sourceSpatialStaticRegularField, sourceSpatialStaticContactField,
    sourceSpatialStaticActiveForcing, wholeRegular, Matrix.add_mulVec, Matrix.mulVec_mulVec]
  unfold unrestrictedGreen PreparationVacuumFullOriginResponse.complementGreen
  simp only [Matrix.mul_assoc]
  rfl

private theorem whole_source_reader (n : PhysicalMomentum) (unit : spatialSquare n = 1)
    (r : staticDomain) (f : Fin 289 → ℂ) :
    sourceSpatialStaticSourceReader n unit r f =
      wholeReflected (sourceStaticSpatialMomentum n r.val) *ᵥ f := by
  have raw : sourceSpatialStaticSourceReader n unit r f =
      sourceNativeReader (sourceStaticSpatialMomentum n r.val) *ᵥ f := by
    simp only [sourceSpatialStaticSourceReader, sourceSpatialStaticActiveForcing,
      sourceNativeReader, Matrix.mulVec_mulVec, Matrix.mul_assoc]
    unfold PreparationVacuumFullOriginResponse.effectiveReader rawEffectiveReader
      PreparationVacuumFullOriginResponse.complementGreen unrestrictedGreen
    rfl
  rw [raw, em_static_reader_reciprocity]
  rfl

/-- The complete source Green retains its regular/contact term around the original full-five inverse. -/
theorem whole_static_green_scaled (n : PhysicalMomentum) (unit : spatialSquare n = 1) (r : staticDomain) :
    (r.val^2 : ℝ) • sourceGreen (sourceSpatialStaticRegularPoint n unit r) =
      (r.val^2 : ℝ) • wholeRegular (sourceStaticSpatialMomentum n r.val) -
      wholeFrame (sourceStaticSpatialMomentum n r.val) * (sourceStaticSpatialKernel n unit r)⁻¹ *
        wholeReflected (sourceStaticSpatialMomentum n r.val) := by
  ext i j
  have paid := congrFun
    (sourceSpatialStaticNativeFieldPoleFactor n unit r (Pi.single j (1 : ℂ))) i
  rw [whole_regular_field, whole_frame_native, whole_source_reader] at paid
  simp only [sourceSpatialStaticNativeField, PreparationVacuumOriginalGreenFeedback.sourceField,
    Matrix.mulVec_single_one, Pi.smul_apply, Pi.sub_apply, Matrix.mulVec_mulVec,
    Matrix.col_apply, smul_eq_mul] at paid
  simp only [Matrix.mulVec, dotProduct, Matrix.mul_apply, Matrix.col_apply] at paid
  simp only [Matrix.smul_apply, Matrix.sub_apply, Complex.real_smul,
    Complex.ofReal_pow]
  simp only [Matrix.mul_apply]
  linear_combination -paid

/-- The original momentum-space residue, before any physical charge identification or Fourier normalization. -/
def wholeStaticLimit : WholeMatrix := -(fullNativeOrigin * staticInverse * fullNativeOrigin.transpose)

theorem whole_static_limit_actual_field (f : Fin 289 → ℂ) :
    wholeStaticLimit *ᵥ f = -staticResidue f := by
  simp only [wholeStaticLimit, staticResidue, Matrix.neg_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc]

private theorem whole_static_limit_schur :
    wholeStaticLimit = -wholeFrame 0 * paddedStaticInverse * wholeReflected 0 := by
  have five := whole_frame_five 0
  have padded : wholeFrame 0 * paddedStaticInverse = wholeFrame 0 * staticInverse := by
    rw [paddedStaticInverse, Matrix.mul_add, Matrix.mul_sub, Matrix.mul_one,
      five, sub_self, add_zero]
  rw [Matrix.neg_mul, padded, Matrix.neg_mul, wholeReflected, neg_zero, whole_frame_origin]
  rfl

private theorem source_direction_norm (n : PhysicalMomentum) (unit : spatialSquare n = 1)
    (r : ℝ) (positive : 0 < r) : ‖sourceStaticSpatialMomentum n r‖ ≤ r := by
  apply (pi_norm_le_iff_of_nonneg positive.le).mpr
  intro j
  exact sourceStaticSpatialMomentum_price n unit r positive.le j

private theorem uniform_source_continuity {E : Type*} [NormedAddCommGroup E]
    (f : (Fin 4 → ℂ) → E) (continuous : ContinuousAt f 0) (eta : ℝ) (positive : 0 < eta) :
    ∃ radius : ℝ, 0 < radius ∧ ∀ r : ℝ, 0 < r → r < radius →
      ∀ n : PhysicalMomentum, spatialSquare n = 1 →
        ‖f (sourceStaticSpatialMomentum n r) - f 0‖ ≤ eta := by
  have near : ∀ᶠ p in 𝓝 (0 : Fin 4 → ℂ), dist (f p) (f 0) < eta :=
    continuous.tendsto.eventually (Metric.ball_mem_nhds (f 0) positive)
  obtain ⟨radius, rp, inside⟩ := Metric.mem_nhds_iff.mp near
  refine ⟨radius, rp, ?_⟩
  intro r positiveR small n unit
  have p := inside (show sourceStaticSpatialMomentum n r ∈ Metric.ball 0 radius by
    simpa only [Metric.mem_ball, dist_zero_right] using (source_direction_norm n unit r positiveR).trans_lt small)
  change dist (f (sourceStaticSpatialMomentum n r)) (f 0) < eta at p
  rw [dist_eq_norm] at p
  exact p.le

private abbrev SchurInput := ℝ × (WholeMatrix × (WholeMatrix × (WholeMatrix × WholeMatrix)))

private def schurRead (z : SchurInput) : WholeMatrix :=
  z.1^2 • z.2.1 - z.2.2.1 * z.2.2.2.1 * z.2.2.2.2

private theorem schurRead_continuous : Continuous schurRead := by
  unfold schurRead
  fun_prop

private def schurOrigin : SchurInput :=
  (0, wholeRegular 0, wholeFrame 0, paddedStaticInverse, wholeReflected 0)

private theorem schur_origin : schurRead schurOrigin = wholeStaticLimit := by
  rw [whole_static_limit_schur]
  simp only [schurRead, schurOrigin, pow_two, zero_mul, zero_smul, zero_sub, Matrix.neg_mul]

/-- One source-generated radius controls every original field row and all physical directions. -/
theorem whole_static_green_uniform (epsilon : ℝ) (positive : 0 < epsilon) :
    ∃ radius : ℝ, 0 < radius ∧ ∀ r : staticDomain, r.val < radius →
      ∀ n : PhysicalMomentum, ∀ unit : spatialSquare n = 1,
        ‖(r.val^2 : ℝ) • sourceGreen (sourceSpatialStaticRegularPoint n unit r) - wholeStaticLimit‖ ≤ epsilon := by
  have near : ∀ᶠ z in 𝓝 schurOrigin, dist (schurRead z) (schurRead schurOrigin) < epsilon :=
    schurRead_continuous.continuousAt.tendsto.eventually
      (Metric.ball_mem_nhds (schurRead schurOrigin) positive)
  obtain ⟨rho, rhop, inside⟩ := Metric.mem_nhds_iff.mp near
  let eta := rho / 2
  have ep : 0 < eta := div_pos rhop (by norm_num)
  have smallEta : eta < rho := by dsimp only [eta]; linarith
  obtain ⟨rf, rfp, frame⟩ := uniform_source_continuity wholeFrame whole_frame_continuous eta ep
  obtain ⟨rc, rcp, reflected⟩ := uniform_source_continuity wholeReflected whole_reflected_continuous eta ep
  obtain ⟨rg, rgp, regular⟩ := uniform_source_continuity wholeRegular whole_regular_continuous eta ep
  let D := 2 * staticInverseBudget^2 * effectiveErrorBudget
  have dp : 0 ≤ D := by
    dsimp only [D]
    exact mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) effectiveErrorBudget_nonneg
  have dplus : 0 < 1 + D := by linarith
  let radius := min eta (min rf (min rc (min rg (eta / (1 + D)))))
  have rp : 0 < radius := lt_min ep (lt_min rfp (lt_min rcp (lt_min rgp (div_pos ep dplus))))
  refine ⟨radius, rp, ?_⟩
  intro r small n unit
  have sr : r.val < eta := small.trans_le (min_le_left _ _)
  have sf : r.val < rf := small.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have sc : r.val < rc := small.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have sg : r.val < rg := small.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))))
  have sd : r.val < eta / (1 + D) :=
    small.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))))
  have A := frame r.val r.property.1 sf n unit
  have C := reflected r.val r.property.1 sc n unit
  have R := regular r.val r.property.1 sg n unit
  have B : ‖(sourceStaticSpatialKernel n unit r)⁻¹ - paddedStaticInverse‖ ≤ eta := by
    apply (sourceStaticSpatialKernel_inverse_delta n unit r).trans
    change D * r.val ≤ eta
    have smallD := (lt_div_iff₀ dplus).mp sd
    nlinarith [r.property.1]
  let z : SchurInput := (r.val, wholeRegular (sourceStaticSpatialMomentum n r.val),
    wholeFrame (sourceStaticSpatialMomentum n r.val), (sourceStaticSpatialKernel n unit r)⁻¹,
    wholeReflected (sourceStaticSpatialMomentum n r.val))
  have distance : ‖z - schurOrigin‖ ≤ eta := by
    change max ‖r.val - 0‖ (max ‖wholeRegular (sourceStaticSpatialMomentum n r.val) - wholeRegular 0‖
      (max ‖wholeFrame (sourceStaticSpatialMomentum n r.val) - wholeFrame 0‖
        (max ‖(sourceStaticSpatialKernel n unit r)⁻¹ - paddedStaticInverse‖
          ‖wholeReflected (sourceStaticSpatialMomentum n r.val) - wholeReflected 0‖))) ≤ eta
    refine max_le ?_ (max_le R (max_le A (max_le B C)))
    simpa only [sub_zero, Real.norm_eq_abs, abs_of_pos r.property.1] using sr.le
  have paid := inside (show z ∈ Metric.ball schurOrigin rho by
    simpa only [Metric.mem_ball, dist_eq_norm] using distance.trans_lt smallEta)
  change dist (schurRead z) (schurRead schurOrigin) < epsilon at paid
  rw [dist_eq_norm, schur_origin] at paid
  rw [whole_static_green_scaled]
  exact paid.le

/-- The dominating price is fixed by the original full residue, independently of direction and scale. -/
def wholeStaticBudget : ℝ := 1 + ‖wholeStaticLimit‖

theorem whole_static_budget_nonnegative : 0 ≤ wholeStaticBudget := by
  unfold wholeStaticBudget
  positivity

theorem whole_static_green_domination :
    ∃ radius : ℝ, 0 < radius ∧ ∀ r : staticDomain, r.val < radius →
      ∀ n : PhysicalMomentum, ∀ unit : spatialSquare n = 1,
        ‖(r.val^2 : ℝ) • sourceGreen (sourceSpatialStaticRegularPoint n unit r)‖ ≤ wholeStaticBudget := by
  obtain ⟨radius, rp, paid⟩ := whole_static_green_uniform 1 (by norm_num)
  refine ⟨radius, rp, ?_⟩
  intro r small n unit
  calc
    _ ≤ ‖(r.val^2 : ℝ) • sourceGreen (sourceSpatialStaticRegularPoint n unit r) - wholeStaticLimit‖ +
      ‖wholeStaticLimit‖ := norm_le_norm_sub_add _ _
    _ ≤ wholeStaticBudget := add_le_add (paid r small n unit) le_rfl

end LowEnergy.GaussComposite.ActualWholeStatic
