import H0mework.Versions.Rf13ed87d.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualEMStaticTable

set_option autoImplicit false
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualEMCarrierOwn
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open PreparationVacuumOriginalGreenFeedback PreparationVacuumPhysicalCharacteristic PreparationVacuumPhysicalPoleSheet
open PreparationVacuumWholeOrigin PreparationVacuumFullOriginResponse PreparationVacuumFullSlowFieldResponse
open PreparationVacuumPhysicalChargedFieldFactor PreparationPhysicalCurvatureSheetLimit
open PreparationPhysicalStaticSpatialCouplingReturn PreparationVacuumStaticPoleResponse
open CanonicalGradedSpatialSource Filter Set Asymptotics
open scoped Matrix BigOperators Topology ContDiff Matrix.Norms.Operator
attribute [local irreducible] emInsertion sourceNativeFrame sourceChargedNativeFrameJet
  originalChange originalReadback contactInverse unrestrictedGreen fullInverse fullKernelFrame

private def emRawProjection :
    (Matrix (Fin 289) (Fin 289) ℂ) →L[ℝ] Matrix (Fin 4) (Fin 289) ℂ :=
  ({toFun:=fun M=>emInsertion.transpose*M*slowFastInverse
    map_add':=fun M N=>by simp only [Matrix.mul_add,Matrix.add_mul]
    map_smul':=fun r M=>by simp only [Matrix.mul_smul,Matrix.smul_mul,RingHom.id_apply]} :
    (Matrix (Fin 289) (Fin 289) ℂ) →ₗ[ℝ] Matrix (Fin 4) (Fin 289) ℂ).toContinuousLinearMap

private theorem em_raw_projection_frame (p : Fin 4→ℂ) :
    emRawProjection (sourceNativeFrame p)=emStaticFrame p := by
  change emInsertion.transpose*sourceNativeFrame p*slowFastInverse=emInsertion.transpose*emStaticRawFrame p
  rw [Matrix.mul_assoc,em_static_frame_from_native]

private theorem em_raw_frame_origin : emStaticFrame 0=0 := by
  have infrared : emInfraredFrame 0=0 := by ext mu j;exact em_infrared_origin mu j
  rw [←em_raw_projection_frame]
  change emInfraredFrame 0*slowFastInverse=0
  rw [infrared,Matrix.zero_mul]

private theorem em_raw_frame_smooth : ContDiffAt ℝ ∞ emStaticFrame (0:Fin 4→ℂ) := by
  have generated:=emRawProjection.contDiff.contDiffAt.comp (0:Fin 4→ℂ) sourceNativeFrame_smooth
  simpa only [Function.comp_def,em_raw_projection_frame] using generated

private theorem em_raw_frame_frechet (v : Fin 4→ℂ) :
    (fderiv ℝ emStaticFrame 0) v=emStaticJet v := by
  have ray : HasDerivAt (fun r : ℝ=>r • v) v 0 := by
    simpa using (hasDerivAt_id (0:ℝ)).smul_const v
  have left:=(em_raw_frame_smooth.differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt_of_eq
    (0:ℝ) ray (show (0:Fin 4→ℂ)=(0:ℝ) • v by simp)
  have right:=emRawProjection.hasFDerivAt.comp_hasDerivAt (0:ℝ) (sourceChargedNativeFrame_derivative v)
  have curve : (fun r : ℝ=>emRawProjection (sourceNativeFrame ((r:ℂ) • v)))=
      fun r : ℝ=>emStaticFrame (r • v) := by
    funext r
    rw [em_raw_projection_frame]
    congr 1
  simp only [Function.comp_def] at right
  rw [curve] at right
  exact left.unique right

private theorem em_uniform_slope {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W] (f : V→W) (L : V→L[ℝ] W)
    (derivative : HasFDerivAt f L 0) (origin : f 0=0) (eta : ℝ) (positive : 0<eta) :
    ∃ radius : ℝ, 0 < radius ∧ ∀ r : ℝ, 0 < r → r < radius → ∀ v : V, ‖v‖ ≤ 1 →
      ‖r⁻¹ • f (r • v)-L v‖≤eta := by
  have little:=hasFDerivAt_iff_isLittleO_nhds_zero.mp derivative
  simp only [zero_add,origin,sub_zero] at little
  obtain ⟨radius,dp,inside⟩:=Metric.mem_nhds_iff.mp (little.bound positive)
  refine ⟨radius,dp,?_⟩
  intro r rp small v bounded
  have ray : ‖r • v‖≤r := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos rp]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left bounded rp.le
  have paid:=inside (show r • v∈Metric.ball 0 radius by simpa only [Metric.mem_ball,dist_zero_right] using ray.trans_lt small)
  have identity : r⁻¹ • (f (r • v)-L (r • v))=r⁻¹ • f (r • v)-L v := by
    rw [smul_sub,map_smul,smul_smul,inv_mul_cancel₀ rp.ne',one_smul]
  rw [←identity,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr rp)]
  calc
    _≤r⁻¹*(eta*‖r • v‖) := mul_le_mul_of_nonneg_left paid (inv_nonneg.mpr rp.le)
    _≤r⁻¹*(eta*r) := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ray positive.le) (inv_nonneg.mpr rp.le)
    _=eta := by field_simp

private theorem em_static_real_ray (n : PhysicalMomentum) (r : ℝ) :
    sourceStaticSpatialMomentum n r=r • physicalFrequencyMomentum 0 n := by
  ext j
  fin_cases j <;> simp [sourceStaticSpatialMomentum,physicalFrequencyMomentum,Fin.cases,Fin.induction,Fin.induction.go,
    Pi.smul_apply,Complex.real_smul]
  all_goals ring

private theorem em_static_direction_bound (n : PhysicalMomentum) (unit : spatialSquare n=1) :
    ‖physicalFrequencyMomentum 0 n‖≤1 := by
  rw [←show sourceStaticSpatialMomentum n 1=physicalFrequencyMomentum 0 n by rw [em_static_real_ray,one_smul]]
  apply (pi_norm_le_iff_of_nonneg (by norm_num : (0:ℝ)≤1)).mpr
  intro j
  exact sourceStaticSpatialMomentum_price n unit 1 (by norm_num) j

/-- Original full-frame differentiability pays a single angular-uniform remainder radius for all source directions and all EM rows/columns. -/
theorem em_static_frame_uniform (eta : ℝ) (positive : 0<eta) :
    ∃ radius : ℝ, 0 < radius ∧ ∀ r : ℝ, 0 < r → r < radius → ∀ n : PhysicalMomentum, spatialSquare n = 1 →
      ‖r⁻¹ • emStaticFrame (sourceStaticSpatialMomentum n r)-emStaticJet (physicalFrequencyMomentum 0 n)‖≤eta := by
  obtain ⟨radius,dp,paid⟩:=em_uniform_slope emStaticFrame (fderiv ℝ emStaticFrame 0)
    (em_raw_frame_smooth.differentiableAt (by simp)).hasFDerivAt em_raw_frame_origin eta positive
  refine ⟨radius,dp,?_⟩
  intro r rp small n unit
  simpa only [em_static_real_ray,em_raw_frame_frechet] using paid r rp small (physicalFrequencyMomentum 0 n)
    (em_static_direction_bound n unit)


private def emRegularProjection :
    (Matrix (Fin 289) (Fin 289) ℂ) →L[ℝ] Matrix (Fin 4) (Fin 4) ℂ :=
  ({toFun:=fun M=>emInsertion.transpose*M*emInsertion
    map_add':=fun M N=>by simp only [Matrix.mul_add,Matrix.add_mul]
    map_smul':=fun r M=>by simp only [Matrix.mul_smul,Matrix.smul_mul,RingHom.id_apply]} :
    (Matrix (Fin 289) (Fin 289) ℂ) →ₗ[ℝ] Matrix (Fin 4) (Fin 4) ℂ).toContinuousLinearMap

private def emRegularCore (p : Fin 4→ℂ) : Matrix (Fin 289) (Fin 289) ℂ :=
  originalChange p*contactInverse p*originalReadback p+
    originalChange p*unrestrictedGreen p*activeProjection*originalReadback p

private def emRegularAt (p : Fin 4→ℂ) : Matrix (Fin 4) (Fin 4) ℂ := emRegularProjection (emRegularCore p)

private theorem em_source_matrix_continuous (terms : List SourceTerm) : Continuous (sourceMatrix terms) := by
  induction terms with
  | nil=>exact continuous_const
  | cons a rest ih=>
    have term : Continuous a.matrix := by
      apply continuous_matrix
      intro i j
      simp only [SourceTerm.matrix,Matrix.single_apply]
      split_ifs
      · unfold Powers.value
        fun_prop
      · exact continuous_const
    exact term.add ih

private theorem em_regular_continuous : ContinuousAt emRegularAt (0:Fin 4→ℂ) := by
  have Oc : Continuous originalChange := by unfold originalChange;exact em_source_matrix_continuous originalChangeTerms
  have O:=Oc.continuousAt (x:=(0:Fin 4→ℂ))
  have C : ContinuousAt contactInverse (0:Fin 4→ℂ) := by
    unfold contactInverse
    exact (em_source_matrix_continuous contactInverseTerms).continuousAt
  have Rc : Continuous originalReadback := by
    unfold originalReadback
    exact (Oc.comp continuous_neg).matrix_transpose
  have R:=Rc.continuousAt (x:=(0:Fin 4→ℂ))
  have G:=unrestrictedGreen_smooth_origin.continuousAt
  exact emRegularProjection.continuous.continuousAt.comp (((O.mul C).mul R).add
    ((((O.mul G).mul continuousAt_const).mul R)))

private theorem em_regular_original (n : PhysicalMomentum) (unit : spatialSquare n=1) (r : staticDomain) :
    emRegularAt (sourceStaticSpatialMomentum n r.val)=emStaticRegularTensor n unit r := by
  ext mu nu
  change (emInsertion.transpose*emRegularCore (sourceStaticSpatialMomentum n r.val)*emInsertion) mu nu=_
  simp only [emRegularCore,emStaticRegularTensor,sourceSpatialStaticRegularField,sourceSpatialStaticContactField,
    sourceSpatialStaticActiveForcing,Matrix.mulVec_add,Matrix.mulVec_mulVec,Pi.add_apply,
    Matrix.mul_add,Matrix.add_mul,Matrix.add_apply,←Matrix.mul_assoc]
  unfold unrestrictedGreen PreparationVacuumFullOriginResponse.complementGreen
  rfl

private theorem em_regular_origin : emRegularAt 0=emStaticRegularOrigin := by
  have green0 : unrestrictedGreen 0=fullInverse := by
    simpa only [unrestrictedGreen,PreparationVacuumFullOriginResponse.complementGreen,
      PreparationVacuumFullOriginResponse.complementOrigin] using PreparationVacuumFullOriginResponse.complementGreen_origin
  ext mu nu
  change (emInsertion.transpose*emRegularCore 0*emInsertion) mu nu=_
  simp only [emRegularCore,green0,emStaticRegularOrigin,Matrix.mulVec_add,Matrix.mulVec_mulVec,
    Pi.add_apply,Matrix.mul_add,Matrix.add_mul,Matrix.add_apply,←Matrix.mul_assoc]
  rfl

private theorem em_uniform_continuous {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] (f : V→W) (continuous : ContinuousAt f 0)
    (eta : ℝ) (positive : 0<eta) :
    ∃ radius : ℝ, 0 < radius ∧ ∀ r : ℝ, 0 < r → r < radius → ∀ v : V, ‖v‖ ≤ 1 →
      ‖f (r • v)-f 0‖≤eta := by
  have near : ∀ᶠ p in 𝓝 (0:V),dist (f p) (f 0)<eta :=
    continuous.tendsto.eventually (Metric.ball_mem_nhds (f 0) positive)
  obtain ⟨radius,rp,inside⟩:=Metric.mem_nhds_iff.mp near
  refine ⟨radius,rp,?_⟩
  intro r positiveR small v bounded
  have ray : ‖r • v‖≤r := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos positiveR]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left bounded positiveR.le
  have paid:=inside (show r • v∈Metric.ball 0 radius by simpa only [Metric.mem_ball,dist_zero_right] using ray.trans_lt small)
  change dist (f (r • v)) (f 0)<eta at paid
  rw [dist_eq_norm] at paid
  exact paid.le

/-- Original contact and full complementary inverse have one source-generated remainder radius for all static directions. -/
theorem em_static_regular_uniform (eta : ℝ) (positive : 0<eta) :
    ∃ radius : ℝ, 0 < radius ∧ ∀ r : staticDomain, r.val < radius → ∀ n : PhysicalMomentum,
      ∀ unit : spatialSquare n=1, ‖emStaticRegularTensor n unit r-emStaticRegularOrigin‖≤eta := by
  obtain ⟨radius,rp,paid⟩:=em_uniform_continuous emRegularAt em_regular_continuous eta positive
  refine ⟨radius,rp,?_⟩
  intro r small n unit
  have generated:=paid r.val r.property.1 small (physicalFrequencyMomentum 0 n) (em_static_direction_bound n unit)
  rw [←em_static_real_ray,em_regular_original n unit r,em_regular_origin] at generated
  exact generated

private def emFrameTranspose :
    (Matrix (Fin 4) (Fin 289) ℂ) →L[ℝ] Matrix (Fin 289) (Fin 4) ℂ :=
  ({toFun:=Matrix.transpose
    map_add':=fun M N=>Matrix.transpose_add M N
    map_smul':=fun r M=>by simp only [Matrix.transpose_smul,RingHom.id_apply]} :
    (Matrix (Fin 4) (Fin 289) ℂ) →ₗ[ℝ] Matrix (Fin 289) (Fin 4) ℂ).toContinuousLinearMap

private theorem em_static_jet_bound (n : PhysicalMomentum) (unit : spatialSquare n=1) :
    ‖emStaticJet (physicalFrequencyMomentum 0 n)‖≤‖fderiv ℝ emStaticFrame 0‖ := by
  rw [←em_raw_frame_frechet]
  exact ((fderiv ℝ emStaticFrame 0).le_opNorm _).trans
    (by simpa only [mul_one] using mul_le_mul_of_nonneg_left (em_static_direction_bound n unit) (norm_nonneg _))


private def emScaledFrame (r : ℝ) (p : Fin 4→ℂ) : Matrix (Fin 4) (Fin 289) ℂ := r⁻¹ • emStaticFrame p

private theorem em_static_green_matrix (n : PhysicalMomentum) (unit : spatialSquare n=1) (r : staticDomain) :
    emStaticGreenTensor n unit r=emStaticRegularTensor n unit r-
      emScaledFrame r.val (sourceStaticSpatialMomentum n r.val)*(sourceStaticSpatialKernel n unit r)⁻¹*
        (emScaledFrame r.val (-(sourceStaticSpatialMomentum n r.val))).transpose := by
  ext mu nu
  rw [em_static_green_schur]
  simp only [Matrix.sub_apply,sub_eq_add_neg]
  congr 1
  simp only [emStaticFinitePole,emScaledFrame,Matrix.mul_apply,Matrix.transpose_apply,
    emStaticDividedRow,emStaticReflectedDividedRow,Matrix.mulVec,dotProduct,Matrix.smul_apply,
    Pi.smul_apply,Complex.real_smul,Complex.ofReal_inv,smul_eq_mul]
  simp only [Finset.mul_sum,Finset.sum_mul,mul_assoc]
  rw [Finset.sum_comm]

private theorem em_static_limit_matrix (n : PhysicalMomentum) :
    emStaticLimitTensor n=emStaticRegularOrigin-
      emStaticJet (physicalFrequencyMomentum 0 n)*paddedStaticInverse*
        (-emStaticJet (physicalFrequencyMomentum 0 n)).transpose := by
  ext mu nu
  simp only [emStaticLimitTensor,Matrix.transpose_neg,Matrix.mul_neg,Matrix.sub_apply,
    Matrix.neg_apply,sub_neg_eq_add,Matrix.mul_assoc,Matrix.mul_apply,Matrix.transpose_apply,Matrix.mulVec,dotProduct]

private theorem em_static_jet_negate (v : Fin 4→ℂ) : emStaticJet (-v)=-emStaticJet v := by
  rw [←em_raw_frame_frechet (-v),←em_raw_frame_frechet v,map_neg]

private theorem em_matrix_triple_price (A : Matrix (Fin 4) (Fin 289) ℂ)
    (B : Matrix (Fin 289) (Fin 289) ℂ) (C : Matrix (Fin 289) (Fin 4) ℂ) :
    ‖A*B*C‖≤‖A‖*‖B‖*‖C‖ :=
  (Matrix.linfty_opNorm_mul _ _).trans
    (mul_le_mul_of_nonneg_right (Matrix.linfty_opNorm_mul _ _) (norm_nonneg _))

private theorem em_matrix_difference_price (A a : Matrix (Fin 4) (Fin 289) ℂ)
    (B b : Matrix (Fin 289) (Fin 289) ℂ) (C c : Matrix (Fin 289) (Fin 4) ℂ) :
    ‖A*B*C-a*b*c‖≤‖A-a‖*‖B‖*‖C‖+‖a‖*‖B-b‖*‖C‖+‖a‖*‖b‖*‖C-c‖ := by
  have identity : A*B*C-a*b*c=(A-a)*B*C+a*(B-b)*C+a*b*(C-c) := by
    simp only [Matrix.sub_mul,Matrix.mul_sub]
    abel
  rw [identity]
  exact (norm_add_le _ _).trans (add_le_add
    ((norm_add_le _ _).trans (add_le_add (em_matrix_triple_price _ _ _) (em_matrix_triple_price _ _ _)))
    (em_matrix_triple_price _ _ _))

/-- The complete original static EM Green converges uniformly over all physical unit directions, including its regular/contact part. -/
theorem em_static_green_uniform (epsilon : ℝ) (positive : 0<epsilon) :
    ∃ radius : ℝ, 0 < radius ∧ ∀ r : staticDomain, r.val < radius → ∀ n : PhysicalMomentum,
      ∀ unit : spatialSquare n=1, ‖emStaticGreenTensor n unit r-emStaticLimitTensor n‖≤epsilon := by
  let M:=‖fderiv ℝ emStaticFrame 0‖
  let T:=‖emFrameTranspose‖
  let I:=staticInverseBudget
  let Z:=T*(M+1)
  let P:=1+(2*I)*Z+M*Z+M*I*T
  have mp : 0≤M:=norm_nonneg _
  have tp : 0≤T:=norm_nonneg _
  have ip : 0≤I:=le_trans (by norm_num) staticInverseBudget_ge_one
  have zp : 0≤Z:=by dsimp only [Z];positivity
  have pp : 0<P:=by dsimp only [P];positivity
  let eta:=min 1 (epsilon/P)
  have ep : 0<eta:=lt_min (by norm_num) (div_pos positive pp)
  have eone : eta≤1:=min_le_left _ _
  have etotal : eta*P≤epsilon:=(le_div_iff₀ pp).mp (min_le_right _ _)
  obtain ⟨rf,rfp,frame⟩:=em_uniform_slope emStaticFrame (fderiv ℝ emStaticFrame 0)
    (em_raw_frame_smooth.differentiableAt (by simp)).hasFDerivAt em_raw_frame_origin eta ep
  obtain ⟨rg,rgp,regular⟩:=em_static_regular_uniform eta ep
  let D:=2*staticInverseBudget^2*effectiveErrorBudget
  have dp : 0≤D:=by dsimp only [D];exact mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) effectiveErrorBudget_nonneg
  have dplus : 0<1+D:=by linarith
  let radius:=min rf (min rg (eta/(1+D)))
  have rp : 0<radius:=lt_min rfp (lt_min rgp (div_pos ep dplus))
  refine ⟨radius,rp,?_⟩
  intro r small n unit
  have sf : r.val<rf:=small.trans_le (min_le_left _ _)
  have sg : r.val<rg:=small.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have sd : r.val<eta/(1+D):=small.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  let v:=physicalFrequencyMomentum 0 n
  let A:=emScaledFrame r.val (sourceStaticSpatialMomentum n r.val)
  let a:=emStaticJet v
  let B:=(sourceStaticSpatialKernel n unit r)⁻¹
  let b:=paddedStaticInverse
  let F:=emScaledFrame r.val (-(sourceStaticSpatialMomentum n r.val))
  let C:=emFrameTranspose F
  let c:=emFrameTranspose (-a)
  have aPrice : ‖a‖≤M:=em_static_jet_bound n unit
  have plus : ‖A-a‖≤eta := by
    simpa only [A,a,v,emScaledFrame,em_static_real_ray,em_raw_frame_frechet] using
      frame r.val r.property.1 sf v (em_static_direction_bound n unit)
  have minus : ‖F-(-a)‖≤eta := by
    have paid:=frame r.val r.property.1 sf (-v) (by simpa only [norm_neg] using em_static_direction_bound n unit)
    simpa only [F,a,v,emScaledFrame,smul_neg,←em_static_real_ray,em_raw_frame_frechet,em_static_jet_negate] using paid
  have fPrice : ‖F‖≤M+1 := by
    calc
      _≤‖F-(-a)‖+‖-a‖:=norm_le_norm_sub_add _ _
      _≤eta+M:=add_le_add minus (by simpa only [norm_neg] using aPrice)
      _≤M+1:=by linarith
  have cPrice : ‖C‖≤Z := (emFrameTranspose.le_opNorm F).trans (mul_le_mul_of_nonneg_left fPrice tp)
  have cDelta : ‖C-c‖≤T*eta := by
    change ‖emFrameTranspose F-emFrameTranspose (-a)‖≤_
    rw [←map_sub]
    exact (emFrameTranspose.le_opNorm _).trans (mul_le_mul_of_nonneg_left minus tp)
  have bPrice : ‖b‖≤I:=paddedStaticInverse_price
  have BPrice : ‖B‖≤2*I:=sourceStaticSpatialKernel_inverse_price n unit r
  have BDelta : ‖B-b‖≤eta := by
    apply (sourceStaticSpatialKernel_inverse_delta n unit r).trans
    change D*r.val≤eta
    have scaled:=(le_div_iff₀ dplus).mp sd.le
    nlinarith [r.property.1.le]
  have pole : ‖A*B*C-a*b*c‖≤eta*(2*I)*Z+M*eta*Z+M*I*(T*eta) := by
    apply (em_matrix_difference_price A a B b C c).trans
    gcongr
  have identity : emStaticGreenTensor n unit r-emStaticLimitTensor n=
      (emStaticRegularTensor n unit r-emStaticRegularOrigin)-(A*B*C-a*b*c) := by
    rw [em_static_green_matrix,em_static_limit_matrix]
    change _=(_-_)-(A*B*(F.transpose)-a*b*((-a).transpose))
    dsimp only [A,B,F,a,b,v]
    abel
  rw [identity]
  calc
    _≤‖emStaticRegularTensor n unit r-emStaticRegularOrigin‖+‖A*B*C-a*b*c‖:=norm_sub_le _ _
    _≤eta+(eta*(2*I)*Z+M*eta*Z+M*I*(T*eta)):=add_le_add (regular r sg n unit) pole
    _=eta*P:=by dsimp only [P];ring
    _≤epsilon:=etotal


/-- One source-fixed norm price for the complete static EM Green; it is not a coupling normalization. -/
def emStaticDominatingNorm : ℝ :=
  1+‖emStaticRegularOrigin‖+‖fderiv ℝ emStaticFrame 0‖*staticInverseBudget*‖emFrameTranspose‖*‖fderiv ℝ emStaticFrame 0‖

theorem em_static_dominating_nonnegative : 0≤emStaticDominatingNorm := by
  have inverse : 0≤ staticInverseBudget:=le_trans (by norm_num) staticInverseBudget_ge_one
  unfold emStaticDominatingNorm
  positivity

private theorem em_static_limit_price (n : PhysicalMomentum) (unit : spatialSquare n=1) :
    ‖emStaticLimitTensor n‖≤emStaticDominatingNorm-1 := by
  let M:=‖fderiv ℝ emStaticFrame 0‖
  have ip : 0 ≤ staticInverseBudget := le_trans (by norm_num) staticInverseBudget_ge_one
  have jp : ‖emStaticJet (physicalFrequencyMomentum 0 n)‖≤M:=em_static_jet_bound n unit
  have transpose : ‖(-emStaticJet (physicalFrequencyMomentum 0 n)).transpose‖≤‖emFrameTranspose‖*M := by
    have bound:=emFrameTranspose.le_opNorm (-emStaticJet (physicalFrequencyMomentum 0 n))
    exact bound.trans (mul_le_mul_of_nonneg_left (by simpa only [norm_neg] using jp) (norm_nonneg _))
  rw [em_static_limit_matrix]
  calc
    _≤‖emStaticRegularOrigin‖+
      ‖emStaticJet (physicalFrequencyMomentum 0 n)*paddedStaticInverse*(-emStaticJet (physicalFrequencyMomentum 0 n)).transpose‖ := norm_sub_le _ _
    _≤‖emStaticRegularOrigin‖+M*staticInverseBudget*(‖emFrameTranspose‖*M) := by
      apply add_le_add le_rfl
      apply (em_matrix_triple_price _ _ _).trans
      gcongr
      exact paddedStaticInverse_price
    _=_ := by dsimp only [emStaticDominatingNorm,M];ring

/-- Full Green norm domination holds on one source-generated radius for every physical unit direction. -/
theorem em_static_green_uniform_bound :
    ∃ radius : ℝ, 0 < radius ∧ ∀ r : staticDomain, r.val < radius → ∀ n : PhysicalMomentum,
      ∀ unit : spatialSquare n=1, ‖emStaticGreenTensor n unit r‖≤emStaticDominatingNorm := by
  obtain ⟨radius,rp,paid⟩:=em_static_green_uniform 1 (by norm_num)
  refine ⟨radius,rp,?_⟩
  intro r small n unit
  calc
    _≤‖emStaticGreenTensor n unit r-emStaticLimitTensor n‖+‖emStaticLimitTensor n‖:=norm_le_norm_sub_add _ _
    _≤1+(emStaticDominatingNorm-1):=add_le_add (paid r small n unit) (em_static_limit_price n unit)
    _=_:=by ring

end LowEnergy.GaussComposite.ActualEMCarrierOwn
