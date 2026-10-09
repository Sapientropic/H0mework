import H0mework.Versions.Rc015842c.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualEMInfrared
import H0mework.Versions.Rc015842c.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceStaticSpatialCoupling

set_option autoImplicit false
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualEMCarrierOwn
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open PreparationVacuumOriginalGreenFeedback PreparationVacuumFullOriginResponse
open PreparationVacuumPhysicalCharacteristic PreparationVacuumPhysicalPoleSheet
open PreparationVacuumMixedPrincipal PreparationVacuumMixedEffective
open PreparationVacuumWholeOrigin PreparationVacuumFullSlowFieldResponse
open PreparationVacuumNativeSlowCoupling PreparationVacuumNativePoleTensor
open PreparationVacuumPhysicalChargedFieldFactor PreparationVacuumSoftPoleSelection
open PreparationVacuumStaticPoleResponse PreparationPhysicalStaticSpatialCouplingReturn
open PreparationPhysicalNativePoleChargeReturn PreparationPhysicalNativePolarizationEmitter
open PreparationPhysicalNativePhotonFluxReturn PreparationPhysicalCurvatureSheetLimit
open PreparationPhysicalNormalizedFullField CanonicalGradedSpatialSource
open PreparationVacuumMixedFieldReturn
open Filter Set
open scoped Matrix BigOperators Topology Matrix.Norms.Operator
attribute [local irreducible] sourceNativeFrame originalChange originalReadback sourceNativeReader
  sourceChargedNativeFrameJet sourceSpatialStaticNativeField sourceSpatialStaticRegularField
  sourceStaticSpatialKernel sourceGreen fullKernelFrame fullNativeOrigin
  PreparationVacuumFullOriginResponse.complementGreen PreparationVacuumFullOriginResponse.effectiveReader
  PreparationVacuumFullOriginResponse.nativeEffectiveFrame sourceSpatialStaticActiveForcing sourceSpatialStaticContactField

/-- The original field frame before the source's slow/fast presentation. -/
def emStaticRawFrame (p : Fin 4 → ℂ) : Matrix (Fin 289) (Fin 289) ℂ :=
  originalChange p * rawEffectiveFrame p

private theorem em_static_frame_five (p : Fin 4 → ℂ) :
    emStaticRawFrame p * fiveProjection = emStaticRawFrame p := by
  simp only [emStaticRawFrame,rawEffectiveFrame,Matrix.mul_sub,Matrix.sub_mul,Matrix.mul_assoc,fullKernel_five]

theorem em_static_frame_from_native (p : Fin 4 → ℂ) :
    sourceNativeFrame p * slowFastInverse = emStaticRawFrame p := by
  rw [sourceNativeFrame,Matrix.mul_assoc,slowFastFrame_inverse_right]
  exact em_static_frame_five p

private theorem em_static_reader_five (p : Fin 4 → ℂ) : fiveProjection * sourceNativeReader p = sourceNativeReader p := by
  simp only [sourceNativeReader,rawEffectiveReader,Matrix.mul_sub,Matrix.sub_mul,
    ←Matrix.mul_assoc,fullKernelTranspose_five]

/-- Exact reflected source reader before presentation changes, on the same original carrier. -/
theorem em_static_reader_reciprocity (p : Fin 4 → ℂ) :
    sourceNativeReader p = (emStaticRawFrame (-p)).transpose := by
  have generated := congrArg (fun M : Matrix (Fin 289) (Fin 289) ℂ => slowFastInverse.transpose*M)
    (em_reader_frame_reciprocity p)
  have left : slowFastInverse.transpose * (slowFastFrame.transpose * sourceNativeReader p) = sourceNativeReader p := by
    rw [←Matrix.mul_assoc,←Matrix.transpose_mul,slowFastFrame_inverse_right]
    have trans : fiveProjection.transpose=fiveProjection := by
      have checked : reflectedTerms fiveProjectionTerms=fiveProjectionTerms := by decide +kernel
      have h := reflectedTerms_value fiveProjectionTerms (0:Fin 4→ℂ)
      rw [checked,neg_zero] at h
      exact h.symm
    rw [trans,em_static_reader_five]
  rw [left,←Matrix.transpose_mul,em_static_frame_from_native] at generated
  exact generated

def emStaticFrame (p : Fin 4 → ℂ) : Matrix (Fin 4) (Fin 289) ℂ := emInsertion.transpose * emStaticRawFrame p

def emStaticJet (v : Fin 4 → ℂ) : Matrix (Fin 4) (Fin 289) ℂ :=
  emInsertion.transpose * sourceChargedNativeFrameJet v * slowFastInverse

private theorem em_static_origin (mu : Fin 4) (j : Fin 289) : emStaticFrame 0 mu j=0 := by
  have raw : emStaticRawFrame 0=fullNativeOrigin := by
    rw [emStaticRawFrame,rawEffectiveFrame_origin,fullNativeOrigin]
  have projected := em_origin_projection (Pi.single j (1:ℂ)) mu
  rw [Matrix.mulVec_mulVec,Matrix.mulVec_single_one] at projected
  simpa only [emStaticFrame,raw,Matrix.col_apply] using projected

private def emStaticEntry (mu : Fin 4) (j : Fin 289) :
    (Matrix (Fin 289) (Fin 289) ℂ) →L[ℝ] ℂ :=
  ({ toFun := fun M => (emInsertion.transpose*M*slowFastInverse) mu j
     map_add' := fun M N => by simp [Matrix.mul_add,Matrix.add_mul]
     map_smul' := fun r M => by simp [Matrix.mul_smul,Matrix.smul_mul] } :
    (Matrix (Fin 289) (Fin 289) ℂ) →ₗ[ℝ] ℂ).toContinuousLinearMap

private theorem em_static_derivative (v : Fin 4 → ℂ) (mu : Fin 4) (j : Fin 289) :
    HasDerivAt (fun kappa : ℝ => emStaticFrame ((kappa:ℂ) • v) mu j) (emStaticJet v mu j) 0 := by
  have result := (emStaticEntry mu j).hasFDerivAt.comp_hasDerivAt (0:ℝ) (sourceChargedNativeFrame_derivative v)
  have same (kappa : ℝ) : emStaticEntry mu j (sourceNativeFrame ((kappa:ℂ) • v)) =
      emStaticFrame ((kappa:ℂ) • v) mu j := by
    change (emInsertion.transpose * sourceNativeFrame _ * slowFastInverse) mu j = _
    rw [Matrix.mul_assoc,em_static_frame_from_native]
    rfl
  have result' := result.congr_deriv (show emStaticEntry mu j (sourceChargedNativeFrameJet v) = emStaticJet v mu j from rfl)
  simpa only [Function.comp_def,same] using result'

private theorem em_static_ray (n : PhysicalMomentum) (kappa : ℝ) :
    sourceStaticSpatialMomentum n kappa = (kappa:ℂ) • physicalFrequencyMomentum 0 n := by
  funext i
  fin_cases i <;> simp [sourceStaticSpatialMomentum,physicalFrequencyMomentum,Fin.cases,Fin.induction,Fin.induction.go,Pi.smul_apply,smul_eq_mul]
  all_goals ring

/-- The actual static EM frame has a paid first order; no pole cancellation is assumed. -/
theorem em_static_frame_divided (n : PhysicalMomentum) (mu : Fin 4) (j : Fin 289) :
    Tendsto (fun kappa : staticDomain => emStaticFrame (sourceStaticSpatialMomentum n kappa.val) mu j/(kappa.val:ℂ))
      staticApproach (𝓝 (emStaticJet (physicalFrequencyMomentum 0 n) mu j)) := by
  have derivative := em_static_derivative (physicalFrequencyMomentum 0 n) mu j
  have near : Tendsto (fun kappa : staticDomain => kappa.val) staticApproach (𝓝[≠] (0:ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    exact ⟨staticVal_tendsto,Eventually.of_forall (fun kappa => kappa.property.1.ne')⟩
  have result := derivative.tendsto_slope_zero.comp near
  simp only [em_static_ray,Complex.ofReal_zero,zero_smul,em_static_origin,sub_zero,zero_add] at result ⊢
  simpa only [Function.comp_def,Complex.real_smul,Complex.ofReal_inv,div_eq_mul_inv,mul_comm] using result

private theorem em_static_jet_neg (v : Fin 4 → ℂ) : emStaticJet (-v) = -emStaticJet v := by
  have linear (terms : List SourceTerm) : sourceLinearPart terms (-v) = -sourceLinearPart terms v := by
    rw [show -v=(-1:ℂ) • v by simp,sourceLinearPart,degreeTensor_scaled,pow_one,neg_one_smul]
    rfl
  have jet : sourceChargedNativeFrameJet (-v) = -(sourceChargedNativeFrameJet v) := by
    simp only [sourceChargedNativeFrameJet,linear]
    noncomm_ring
  simp only [emStaticJet,jet,Matrix.mul_neg,Matrix.neg_mul]

/-- The reflected static end has the opposite first derivative from the same source frame. -/
theorem em_static_reflected_frame_divided (n : PhysicalMomentum) (mu : Fin 4) (j : Fin 289) :
    Tendsto (fun kappa : staticDomain => emStaticFrame (-(sourceStaticSpatialMomentum n kappa.val)) mu j/(kappa.val:ℂ))
      staticApproach (𝓝 (-emStaticJet (physicalFrequencyMomentum 0 n) mu j)) := by
  have negative : physicalFrequencyMomentum 0 (-n) = -physicalFrequencyMomentum 0 n := by
    funext i
    fin_cases i <;> simp [physicalFrequencyMomentum,Fin.cases,Fin.induction,Fin.induction.go,Pi.neg_apply]
  have point (kappa : ℝ) : sourceStaticSpatialMomentum (-n) kappa = -(sourceStaticSpatialMomentum n kappa) := by
    rw [em_static_ray,em_static_ray,negative,smul_neg]
  have result := em_static_frame_divided (-n) mu j
  simpa only [point,negative,em_static_jet_neg,Matrix.neg_apply] using result


/-- The original full static Green, read on both literal EM ends. -/
def emStaticGreenTensor (n : PhysicalMomentum) (unit : spatialSquare n=1) (kappa : staticDomain) :
    Matrix (Fin 4) (Fin 4) ℂ := fun mu nu =>
  (emInsertion.transpose *ᵥ sourceSpatialStaticNativeField n unit kappa (emSourceColumn nu)) mu

theorem em_static_green_original (n : PhysicalMomentum) (unit : spatialSquare n=1) (kappa : staticDomain) :
    emStaticGreenTensor n unit kappa =
      emInsertion.transpose * sourceGreen (sourceSpatialStaticRegularPoint n unit kappa) * emInsertion := by
  ext mu nu
  unfold emStaticGreenTensor sourceSpatialStaticNativeField PreparationVacuumOriginalGreenFeedback.sourceField
  rw [Matrix.mulVec_mulVec]
  rfl

def emStaticRegularTensor (n : PhysicalMomentum) (unit : spatialSquare n=1) (kappa : staticDomain) :
    Matrix (Fin 4) (Fin 4) ℂ := fun mu nu =>
  (emInsertion.transpose *ᵥ sourceSpatialStaticRegularField n unit kappa (emSourceColumn nu)) mu

def emStaticDividedRow (n : PhysicalMomentum) (kappa : staticDomain) (mu : Fin 4) : Fin 289 → ℂ :=
  (kappa.val:ℂ)⁻¹ • emStaticFrame (sourceStaticSpatialMomentum n kappa.val) mu

def emStaticReflectedDividedRow (n : PhysicalMomentum) (kappa : staticDomain) (mu : Fin 4) : Fin 289 → ℂ :=
  (kappa.val:ℂ)⁻¹ • emStaticFrame (-(sourceStaticSpatialMomentum n kappa.val)) mu

/-- Both first-order EM factors remain around the original complete static inverse. -/
def emStaticFinitePole (n : PhysicalMomentum) (unit : spatialSquare n=1) (kappa : staticDomain) :
    Matrix (Fin 4) (Fin 4) ℂ := fun mu nu =>
  -dotProduct (emStaticDividedRow n kappa mu)
    ((sourceStaticSpatialKernel n unit kappa)⁻¹ *ᵥ emStaticReflectedDividedRow n kappa nu)

private theorem em_static_source_reader (n : PhysicalMomentum) (unit : spatialSquare n=1)
    (kappa : staticDomain) (nu : Fin 4) :
    sourceSpatialStaticSourceReader n unit kappa (emSourceColumn nu) =
      emStaticFrame (-(sourceStaticSpatialMomentum n kappa.val)) nu := by
  have raw : sourceSpatialStaticSourceReader n unit kappa (emSourceColumn nu) =
      sourceNativeReader (sourceStaticSpatialMomentum n kappa.val) *ᵥ emSourceColumn nu := by
    simp only [sourceSpatialStaticSourceReader,sourceSpatialStaticActiveForcing,sourceNativeReader,
      Matrix.mulVec_mulVec,Matrix.mul_assoc]
    unfold PreparationVacuumFullOriginResponse.effectiveReader rawEffectiveReader
      PreparationVacuumFullOriginResponse.complementGreen unrestrictedGreen
    rfl
  rw [raw,em_static_reader_reciprocity]
  funext j
  simp only [emStaticFrame,emSourceColumn,Matrix.mulVec,Matrix.mul_apply,Matrix.transpose_apply,dotProduct]
  apply Finset.sum_congr rfl
  intro i _
  ring

private theorem em_static_rescaled_pair (z : ℂ) (nonzero : z≠0) (x y : Fin 289 → ℂ)
    (M : Matrix (Fin 289) (Fin 289) ℂ) :
    (-z^2)⁻¹ * dotProduct x (M*ᵥy) = -dotProduct (z⁻¹ • x) (M*ᵥ(z⁻¹ • y)) := by
  rw [Matrix.mulVec_smul,smul_dotProduct,dotProduct_smul]
  simp only [smul_eq_mul]
  field_simp [nonzero]

/-- Exact static cancellation uses both paid EM frame factors, preserving original contact and full complement. -/
theorem em_static_green_schur (n : PhysicalMomentum) (unit : spatialSquare n=1) (kappa : staticDomain)
    (mu nu : Fin 4) :
    emStaticGreenTensor n unit kappa mu nu =
      emStaticRegularTensor n unit kappa mu nu + emStaticFinitePole n unit kappa mu nu := by
  have field := sourceSpatialStaticNativeFieldSchur n unit kappa (emSourceColumn nu)
  have paired := congrArg (fun V : Fin 289 → ℂ => (emInsertion.transpose *ᵥ V) mu) field
  simp only [Matrix.mulVec_add,Matrix.mulVec_smul,Pi.add_apply,Pi.smul_apply,smul_eq_mul] at paired
  have reg : emStaticRegularTensor n unit kappa mu nu =
      (emInsertion.transpose *ᵥ sourceSpatialStaticContactField n unit kappa (emSourceColumn nu)) mu +
      (emInsertion.transpose *ᵥ (originalChange (sourceStaticSpatialMomentum n kappa.val) *ᵥ
        (PreparationVacuumFullOriginResponse.complementGreen (sourceStaticSpatialPoint n unit kappa) *ᵥ
          sourceSpatialStaticActiveForcing n unit kappa (emSourceColumn nu)))) mu := by
    simp only [emStaticRegularTensor,sourceSpatialStaticRegularField,Matrix.mulVec_add,Pi.add_apply]
  have pole : (-(kappa.val:ℂ)^2)⁻¹ *
      (emInsertion.transpose *ᵥ (PreparationVacuumFullOriginResponse.nativeEffectiveFrame (sourceStaticSpatialPoint n unit kappa) *ᵥ
        ((sourceStaticSpatialKernel n unit kappa)⁻¹ *ᵥ
          (PreparationVacuumFullOriginResponse.effectiveReader (sourceStaticSpatialPoint n unit kappa) *ᵥ
            sourceSpatialStaticActiveForcing n unit kappa (emSourceColumn nu))))) mu =
      emStaticFinitePole n unit kappa mu nu := by
    change (-(kappa.val:ℂ)^2)⁻¹ *
      (emInsertion.transpose *ᵥ (PreparationVacuumFullOriginResponse.nativeEffectiveFrame (sourceStaticSpatialPoint n unit kappa) *ᵥ
        ((sourceStaticSpatialKernel n unit kappa)⁻¹ *ᵥ sourceSpatialStaticSourceReader n unit kappa (emSourceColumn nu)))) mu = _
    rw [em_static_source_reader,Matrix.mulVec_mulVec]
    have frame : PreparationVacuumFullOriginResponse.nativeEffectiveFrame (sourceStaticSpatialPoint n unit kappa) =
        emStaticRawFrame (sourceStaticSpatialMomentum n kappa.val) := by
      unfold PreparationVacuumFullOriginResponse.nativeEffectiveFrame emStaticRawFrame
        PreparationVacuumFullOriginResponse.effectiveFrame rawEffectiveFrame
        PreparationVacuumFullOriginResponse.complementGreen unrestrictedGreen
      rfl
    rw [frame]
    exact em_static_rescaled_pair (kappa.val:ℂ) (Complex.ofReal_ne_zero.mpr kappa.property.1.ne') _ _ _
  change emStaticGreenTensor n unit kappa mu nu = _ at paired
  rw [pole] at paired
  rw [reg]
  linear_combination paired

private theorem em_static_row_limit (n : PhysicalMomentum) (mu : Fin 4) :
    Tendsto (fun kappa : staticDomain => emStaticDividedRow n kappa mu) staticApproach
      (𝓝 (emStaticJet (physicalFrequencyMomentum 0 n) mu)) := by
  apply tendsto_pi_nhds.mpr
  intro j
  simpa only [emStaticDividedRow,Pi.smul_apply,smul_eq_mul,div_eq_mul_inv,mul_comm] using
    em_static_frame_divided n mu j

private theorem em_static_reflected_row_limit (n : PhysicalMomentum) (mu : Fin 4) :
    Tendsto (fun kappa : staticDomain => emStaticReflectedDividedRow n kappa mu) staticApproach
      (𝓝 (-emStaticJet (physicalFrequencyMomentum 0 n) mu)) := by
  apply tendsto_pi_nhds.mpr
  intro j
  simpa only [emStaticReflectedDividedRow,Pi.smul_apply,smul_eq_mul,div_eq_mul_inv,mul_comm,Pi.neg_apply] using
    em_static_reflected_frame_divided n mu j

/-- The complete five-mode static term has a finite original-source directional tensor, after both ends were paid. -/
theorem em_static_finite_pole_limit (n : PhysicalMomentum) (unit : spatialSquare n=1) (mu nu : Fin 4) :
    Tendsto (fun kappa : staticDomain => emStaticFinitePole n unit kappa mu nu) staticApproach
      (𝓝 (dotProduct (emStaticJet (physicalFrequencyMomentum 0 n) mu)
        (paddedStaticInverse *ᵥ emStaticJet (physicalFrequencyMomentum 0 n) nu))) := by
  have matrix := sourceSpatialNormalizedInverseTendsto n unit
  have right := em_static_reflected_row_limit n nu
  have mulVecContinuous : Continuous (fun p : Matrix (Fin 289) (Fin 289) ℂ × (Fin 289 → ℂ) => p.1 *ᵥ p.2) :=
    continuous_fst.matrix_mulVec continuous_snd
  have inner := (mulVecContinuous.tendsto _).comp (matrix.prodMk_nhds right)
  have dotContinuous : Continuous (fun p : (Fin 289 → ℂ) × (Fin 289 → ℂ) => dotProduct p.1 p.2) :=
    continuous_fst.dotProduct continuous_snd
  have result := ((dotContinuous.tendsto _).comp ((em_static_row_limit n mu).prodMk_nhds inner)).neg
  simpa only [Function.comp_def,emStaticFinitePole,Matrix.mulVec_neg,dotProduct_neg,neg_neg] using result

/-- Original static contact and full complementary inverse at zero momentum. -/
def emStaticRegularOrigin : Matrix (Fin 4) (Fin 4) ℂ := fun mu nu =>
  (emInsertion.transpose *ᵥ
    (originalChange 0 *ᵥ (contactInverse 0 *ᵥ (originalReadback 0 *ᵥ emSourceColumn nu)) +
      originalChange 0 *ᵥ (fullInverse *ᵥ (activeProjection *ᵥ (originalReadback 0 *ᵥ emSourceColumn nu))))) mu

theorem em_static_regular_limit (n : PhysicalMomentum) (unit : spatialSquare n=1) (mu nu : Fin 4) :
    Tendsto (fun kappa : staticDomain => emStaticRegularTensor n unit kappa mu nu) staticApproach
      (𝓝 (emStaticRegularOrigin mu nu)) := by
  have cont : Continuous (fun V : Fin 289 → ℂ => (emInsertion.transpose *ᵥ V) mu) :=
    (continuous_apply mu).comp (continuous_const.matrix_mulVec continuous_id)
  exact (cont.tendsto _).comp (sourceSpatialStaticRegularFieldTendsto n unit (emSourceColumn nu))

/-- The true EM static response contains the original regular term and the computed directional Schur term. -/
def emStaticLimitTensor (n : PhysicalMomentum) : Matrix (Fin 4) (Fin 4) ℂ := fun mu nu =>
  emStaticRegularOrigin mu nu + dotProduct (emStaticJet (physicalFrequencyMomentum 0 n) mu)
    (paddedStaticInverse *ᵥ emStaticJet (physicalFrequencyMomentum 0 n) nu)

/-- Finite zero-momentum limit of the original unscaled full Green projected on true EM source and detector. -/
theorem em_static_green_limit (n : PhysicalMomentum) (unit : spatialSquare n=1) (mu nu : Fin 4) :
    Tendsto (fun kappa : staticDomain => emStaticGreenTensor n unit kappa mu nu) staticApproach
      (𝓝 (emStaticLimitTensor n mu nu)) := by
  have result := (em_static_regular_limit n unit mu nu).add (em_static_finite_pole_limit n unit mu nu)
  exact result.congr' (Eventually.of_forall (fun kappa => (em_static_green_schur n unit kappa mu nu).symm))

/-- The genuine EM-EM static Green has zero Coulomb pole coefficient on every source direction. -/
theorem em_static_coulomb_pole_zero (n : PhysicalMomentum) (unit : spatialSquare n=1) (mu nu : Fin 4) :
    Tendsto (fun kappa : staticDomain => (-(kappa.val:ℂ)^2)*emStaticGreenTensor n unit kappa mu nu)
      staticApproach (𝓝 (0:ℂ)) := by
  have scale : Tendsto (fun kappa : staticDomain => -(kappa.val:ℂ)^2) staticApproach (𝓝 (0:ℂ)) := by
    simpa only [Function.comp_def,Complex.ofReal_zero,zero_pow (by decide : 2≠0),neg_zero] using
      ((Complex.continuous_ofReal.continuousAt.tendsto.comp staticVal_tendsto).pow 2).neg
  simpa only [zero_mul] using scale.mul (em_static_green_limit n unit mu nu)

end LowEnergy.GaussComposite.ActualEMCarrierOwn
