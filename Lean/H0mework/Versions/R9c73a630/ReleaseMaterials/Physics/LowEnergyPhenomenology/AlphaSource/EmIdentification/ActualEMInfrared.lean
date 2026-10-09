import H0mework.Versions.R9c73a630.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualEMPreparedResidue
import H0mework.Versions.R9c73a630.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceCurvaturePoleReturn

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
open PreparationPhysicalNativePoleChargeReturn PreparationPhysicalNativePolarizationEmitter
open PreparationPhysicalNativePhotonFluxReturn PreparationPhysicalCurvatureSheetLimit
open PreparationPhysicalNormalizedFullField CanonicalGradedSpatialSource
open PreparationVacuumMixedFieldReturn
open Filter Set Asymptotics
open scoped Matrix BigOperators Topology ContDiff Matrix.Norms.Operator
attribute [local irreducible] sourceNativeFrame sourceNativeReader originalChange originalReadback
  sourceChargedNativeFrameJet sourceResidue sourceWholePhotonFrequencyResidue

private theorem em_full_active : fullComplementProjection * activeProjection = fullComplementProjection := by
  unfold fullComplementProjection activeProjection projectionMatrix
  rw [Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  cases h : activeFlag i <;> simp [fullComplementFlag,h]

private theorem em_active_transpose : activeProjection.transpose = activeProjection := by
  simp [activeProjection,projectionMatrix]

private theorem em_full_transpose : fullComplementProjection.transpose = fullComplementProjection := by
  simp [fullComplementProjection,projectionMatrix]

private theorem em_complement_reflect (p : Fin 4 → ℂ) :
    (PreparationVacuumFullOriginResponse.complementKernel (-p)).transpose =
      PreparationVacuumFullOriginResponse.complementKernel p := by
  simp only [PreparationVacuumFullOriginResponse.complementKernel,Matrix.transpose_add,
    Matrix.transpose_mul,Matrix.transpose_sub,Matrix.transpose_one,em_full_transpose,
    activeKernel_reflect,Matrix.mul_assoc]

private theorem em_unrestricted_reflect (p : Fin 4 → ℂ) :
    (unrestrictedGreen (-p)).transpose = unrestrictedGreen p := by
  simp only [unrestrictedGreen,Matrix.transpose_mul,Matrix.transpose_nonsing_inv,
    em_full_transpose,em_complement_reflect,Matrix.mul_assoc]

private theorem em_raw_reader_active (p : Fin 4 → ℂ) :
    rawEffectiveReader p * activeProjection = rawEffectiveReader p := by
  have kernel := congrArg Matrix.transpose PreparationVacuumStaticPoleResponse.fullKernel_active
  rw [Matrix.transpose_mul,em_active_transpose] at kernel
  have green : unrestrictedGreen p * activeProjection = unrestrictedGreen p := by
    simp only [unrestrictedGreen,Matrix.mul_assoc,em_full_active]
  unfold rawEffectiveReader
  rw [Matrix.sub_mul,kernel,Matrix.mul_assoc,green]

/-- Both apparent endpoints are restrictions of the same reflected full source frame. -/
theorem em_reader_frame_reciprocity (p : Fin 4 → ℂ) :
    slowFastFrame.transpose * sourceNativeReader p = (sourceNativeFrame (-p)).transpose := by
  have raw : (rawEffectiveFrame (-p)).transpose = rawEffectiveReader p := by
    simp only [rawEffectiveFrame,rawEffectiveReader,Matrix.transpose_sub,Matrix.transpose_mul,
      activeKernel_reflect,em_unrestricted_reflect,Matrix.mul_assoc]
  simp only [sourceNativeReader,sourceNativeFrame,Matrix.transpose_mul,raw,
    originalReadback,em_raw_reader_active,Matrix.mul_assoc]

/-- True source EM insertion column. -/
def emSourceColumn (mu : Fin 4) : Fin 289 → ℂ := fun j => emInsertion j mu

/-- Full frame projection, before slow/fast restriction or pole selection. -/
def emInfraredFrame (p : Fin 4 → ℂ) : Matrix (Fin 4) (Fin 289) ℂ :=
  emInsertion.transpose * sourceNativeFrame p

def emInfraredJet (v : Fin 4 → ℂ) : Matrix (Fin 4) (Fin 289) ℂ :=
  emInsertion.transpose * sourceChargedNativeFrameJet v

theorem em_infrared_origin (mu : Fin 4) (j : Fin 289) : emInfraredFrame 0 mu j = 0 := by
  have source := em_origin_projection (slowFastFrame *ᵥ Pi.single j (1:ℂ)) mu
  rw [Matrix.mulVec_mulVec,Matrix.mulVec_mulVec,Matrix.mulVec_single_one] at source
  simpa only [emInfraredFrame,sourceChargedNativeFrame_origin,Matrix.mul_assoc,Matrix.col_apply] using source

private def emFrameEntry (mu : Fin 4) (j : Fin 289) :
    (Matrix (Fin 289) (Fin 289) ℂ) →L[ℝ] ℂ :=
  ({ toFun := fun M => (emInsertion.transpose*M) mu j
     map_add' := fun M N => by simp [Matrix.mul_add]
     map_smul' := fun r M => by simp [Matrix.mul_smul] } :
    (Matrix (Fin 289) (Fin 289) ℂ) →ₗ[ℝ] ℂ).toContinuousLinearMap

private theorem em_frame_smooth (mu : Fin 4) (j : Fin 289) :
    ContDiffAt ℝ ∞ (fun p => emInfraredFrame p mu j) 0 :=
  (emFrameEntry mu j).contDiff.contDiffAt.comp 0 sourceNativeFrame_smooth

private theorem em_frame_frechet (v : Fin 4 → ℂ) (mu : Fin 4) (j : Fin 289) :
    (fderiv ℝ (fun p => emInfraredFrame p mu j) 0) v = emInfraredJet v mu j := by
  have ray : HasDerivAt (fun d : ℝ => (d:ℂ) • v) v 0 := by
    simpa using (hasDerivAt_id (0:ℝ)).ofReal_comp.smul_const v
  have left := ((em_frame_smooth mu j).differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt_of_eq
    (0:ℝ) ray (show (0:Fin 4→ℂ)=(0:ℂ) • v by simp)
  have right := (emFrameEntry mu j).hasFDerivAt.comp_hasDerivAt (0:ℝ) (sourceChargedNativeFrame_derivative v)
  exact left.unique right


private theorem em_moving_divided (f : (Fin 4 → ℂ) → ℂ)
    (smooth : DifferentiableAt ℝ f 0) (origin : f 0=0)
    (direction : scaleDomain → Fin 4 → ℂ) (v : Fin 4 → ℂ)
    (moving : Tendsto direction scaleApproach (𝓝 v)) :
    Tendsto (fun e : scaleDomain => f ((e.val^2:ℝ) • direction e)/(e.val:ℂ)^2)
      scaleApproach (𝓝 ((fderiv ℝ f 0) v)) := by
  have ray : Tendsto (fun e : scaleDomain => (e.val^2:ℝ) • direction e) scaleApproach (𝓝 0) := by
    simpa only [zero_pow (by decide : 2≠0),zero_smul] using (scaleVal_tendsto.pow 2).smul moving
  have little := (hasFDerivAt_iff_isLittleO_nhds_zero.mp smooth.hasFDerivAt).comp_tendsto ray
  have dirPrice : direction =O[scaleApproach] (fun _ => (1:ℝ)) :=
    isBigO_const_of_tendsto moving one_ne_zero
  have price : (fun e : scaleDomain => (e.val^2:ℝ) • direction e) =O[scaleApproach]
      (fun e : scaleDomain => e.val^2) := by
    simpa only [smul_eq_mul,mul_one] using
      (isBigO_refl (fun e : scaleDomain => e.val^2) scaleApproach).smul dirPrice
  have quotient := (little.trans_isBigO price).norm_left.tendsto_div_nhds_zero
  have linear (e : scaleDomain) :
      (fderiv ℝ f 0) ((e.val^2:ℝ) • direction e) =
        (e.val:ℂ)^2*(fderiv ℝ f 0) (direction e) := by
    rw [map_smul]
    simp only [Complex.real_smul,Complex.ofReal_pow]
  have remainder : Tendsto (fun e : scaleDomain =>
      (f ((e.val^2:ℝ) • direction e) - (e.val:ℂ)^2*(fderiv ℝ f 0) (direction e))/(e.val:ℂ)^2)
      scaleApproach (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    simpa only [Function.comp_apply,zero_add,origin,sub_zero,linear,norm_div,norm_pow,
      Complex.norm_real,Real.norm_eq_abs,sq_abs] using quotient
  have derivative := (fderiv ℝ f 0).continuous.tendsto v |>.comp moving
  have result := remainder.add derivative
  simp only [zero_add] at result
  apply result.congr'
  filter_upwards [] with e
  have nonzero : (e.val:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr e.property.1.ne'
  simp only [Function.comp_apply]
  field_simp [nonzero]
  ring

private theorem em_ray_real (e s : ℝ) (n : PhysicalMomentum) :
    frequencyRay e s n = (e^2:ℝ) • physicalFrequencyMomentum s n := by
  rw [frequencyRay_scaled]
  funext i
  simp only [Pi.smul_apply,Complex.real_smul,Complex.ofReal_pow,smul_eq_mul]

/-- The complete reflected or forward EM frame pays its epsilon-squared first term on the actual moving sheet. -/
theorem em_frame_divided_limit (sign : ℝ) (branch : Fin 2) (n : PhysicalMomentum)
    (unit : spatialSquare n=1) (mu : Fin 4) (j : Fin 289) :
    Tendsto (fun e : scaleDomain =>
      emInfraredFrame (sign • frequencyRay e.val (sourceSheet branch n unit e.val) n) mu j/(e.val:ℂ)^2)
      scaleApproach (𝓝 (sign • emInfraredJet (physicalFrequencyMomentum (sourceSpeed branch) n) mu j)) := by
  have moving := (tendsto_const_nhds (x:=sign)).smul (sourceCurvatureDirection_tendsto branch n unit)
  have result := em_moving_divided (fun p => emInfraredFrame p mu j)
    ((em_frame_smooth mu j).differentiableAt (by simp)) (em_infrared_origin mu j)
    (fun e => sign • physicalFrequencyMomentum (sourceSheet branch n unit e.val) n)
    (sign • physicalFrequencyMomentum (sourceSpeed branch) n) moving
  rw [map_smul,em_frame_frechet] at result
  apply result.congr'
  filter_upwards [] with e
  rw [em_ray_real,smul_comm]

private theorem em_reflected_row (p : Fin 4 → ℂ) (mu : Fin 4) (i : Fin 5) :
    (slowFastFrame.transpose *ᵥ (rawEffectiveReader p *ᵥ activeForcing p (emSourceColumn mu))) (fiveIndex i) =
      emInfraredFrame (-p) mu (fiveIndex i) := by
  have reflected := congrArg (fun M : Matrix (Fin 289) (Fin 289) ℂ =>
    (M *ᵥ emSourceColumn mu) (fiveIndex i)) (em_reader_frame_reciprocity p)
  have left : slowFastFrame.transpose *ᵥ (rawEffectiveReader p *ᵥ activeForcing p (emSourceColumn mu)) =
      (slowFastFrame.transpose * sourceNativeReader p) *ᵥ emSourceColumn mu := by
    simp only [sourceNativeReader,activeForcing,Matrix.mulVec_mulVec,Matrix.mul_assoc]
  rw [left,reflected]
  simp only [emInfraredFrame,emSourceColumn,Matrix.mul_apply,Matrix.mulVec,Matrix.transpose_apply,dotProduct]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Actual epsilon powers on the left are paid by the same reflected EM frame; no bounded-cofactor premise enters. -/
theorem em_mode_forcing_scaled (epsilon s : ℝ) (n : PhysicalMomentum) (nonzero : epsilon≠0)
    (mu : Fin 4) :
    nativeModeForcing epsilon s n (emSourceColumn mu) =
      regularScaling epsilon *ᵥ (fun i : Fin 5 =>
        emInfraredFrame (-(frequencyRay epsilon s n)) mu (fiveIndex i)/(epsilon:ℂ)^2) := by
  have ne : (epsilon:ℂ)≠0 := Complex.ofReal_ne_zero.mpr nonzero
  funext i
  unfold nativeModeForcing
  simp only [wideRayScaling,Matrix.mulVec_diagonal]
  rw [em_reflected_row]
  simp only [regularScaling,Matrix.mulVec_diagonal,fiveIndex,i.isLt,if_true]
  split_ifs <;> field_simp [ne]

private theorem em_regular_continuous : Continuous regularScaling := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  unfold regularScaling
  simp only [Matrix.diagonal_apply]
  split_ifs <;> fun_prop

private theorem em_mulVec_limit {X : Type*} {m n : ℕ} {L : Filter X}
    {A : X → Matrix (Fin m) (Fin n) ℂ} {v : X → Fin n → ℂ}
    {B : Matrix (Fin m) (Fin n) ℂ} {w : Fin n → ℂ}
    (matrix : Tendsto A L (𝓝 B)) (vector : Tendsto v L (𝓝 w)) :
    Tendsto (fun x => A x *ᵥ v x) L (𝓝 (B *ᵥ w)) := by
  have cont : Continuous (fun p : Matrix (Fin m) (Fin n) ℂ × (Fin n → ℂ) => p.1 *ᵥ p.2) :=
    continuous_fst.matrix_mulVec continuous_snd
  exact (cont.tendsto _).comp (matrix.prodMk_nhds vector)

/-- The real EM source left forcing has a finite generated limit after all original scale factors. -/
theorem em_mode_forcing_limit (branch : Fin 2) (n : PhysicalMomentum) (unit : spatialSquare n=1)
    (mu : Fin 4) :
    Tendsto (fun e : scaleDomain => nativeModeForcing e.val (sourceSheet branch n unit e.val) n (emSourceColumn mu))
      scaleApproach (𝓝 (regularScaling 0 *ᵥ fun i : Fin 5 =>
        -emInfraredJet (physicalFrequencyMomentum (sourceSpeed branch) n) mu (fiveIndex i))) := by
  have entries : Tendsto (fun e : scaleDomain => fun i : Fin 5 =>
      emInfraredFrame (-(frequencyRay e.val (sourceSheet branch n unit e.val) n)) mu (fiveIndex i)/(e.val:ℂ)^2)
      scaleApproach (𝓝 (fun i : Fin 5 => -emInfraredJet (physicalFrequencyMomentum (sourceSpeed branch) n) mu (fiveIndex i))) := by
    apply tendsto_pi_nhds.mpr
    intro i
    simpa only [neg_one_smul] using em_frame_divided_limit (-1) branch n unit mu (fiveIndex i)
  have result := em_mulVec_limit (em_regular_continuous.continuousAt.tendsto.comp scaleVal_tendsto) entries
  exact result.congr' (Eventually.of_forall (fun e => (em_mode_forcing_scaled e.val _ n e.property.1.ne' mu).symm))


private theorem em_leading_pivot (branch : Fin 2) (n : PhysicalMomentum) (unit : spatialSquare n=1) :
    leadingResidue branch n (residueIndex branch) (residueIndex branch) ≠ 0 := by
  have diagonal := congrFun (congrFun (leadingResidue_normalization branch n unit) (residueIndex branch)) (residueIndex branch)
  simp only [Matrix.smul_apply,Matrix.single_apply,smul_eq_mul] at diagonal
  intro zero
  rw [zero,mul_zero] at diagonal
  exact (Complex.ofReal_ne_zero.mpr (softCoefficient_nonzero branch)) diagonal.symm

private theorem em_leading_read (branch : Fin 2) (n : PhysicalMomentum) (unit : spatialSquare n=1)
    (v : Fin 5 → ℂ) :
    (leadingResidue branch n *ᵥ v) (residueIndex branch) /
      leadingResidue branch n (residueIndex branch) (residueIndex branch) = v (residueIndex branch) := by
  have diagonal := congrFun (congrFun (leadingResidue_normalization branch n unit) (residueIndex branch)) (residueIndex branch)
  simp only [Matrix.smul_apply,Matrix.single_apply,smul_eq_mul] at diagonal
  have scale : 2*(sourceSpeed branch:ℂ) ≠ 0 := by
    intro zero
    rw [zero,zero_mul] at diagonal
    exact (Complex.ofReal_ne_zero.mpr (softCoefficient_nonzero branch)) diagonal.symm
  have column := congrFun (congrArg (fun A : Matrix (Fin 5) (Fin 5) ℂ => A*ᵥv)
    (leadingResidue_normalization branch n unit)) (residueIndex branch)
  simp only [Matrix.smul_mulVec,Matrix.single_mulVec,Pi.smul_apply,Function.update_self,smul_eq_mul] at column
  apply (div_eq_iff (em_leading_pivot branch n unit)).mpr
  apply mul_left_cancel₀ scale
  rw [column]
  calc
    _ = (2*(sourceSpeed branch:ℂ)*leadingResidue branch n (residueIndex branch) (residueIndex branch))*v (residueIndex branch) :=
      congrArg (fun z : ℂ => z*v (residueIndex branch)) diagonal.symm
    _ = _ := by ring

/-- The true EM source cofactor is finite: its limit is the reflected source first jet on the source-selected branch. -/
theorem em_left_cofactor_limit (branch : Fin 2) (n : PhysicalMomentum) (unit : spatialSquare n=1)
    (mu : Fin 4) :
    Tendsto (fun e : scaleDomain =>
      sourcePhotonLeftReader branch e.val (sourceSheet branch n unit e.val) n (emSourceColumn mu))
      scaleApproach (𝓝 (-emInfraredJet (physicalFrequencyMomentum (sourceSpeed branch) n) mu
        (fiveIndex (residueIndex branch)))) := by
  have residue := sourceResidue_soft_limit branch n unit
  have product := em_mulVec_limit residue (em_mode_forcing_limit branch n unit mu)
  have numerator := tendsto_pi_nhds.mp product (residueIndex branch)
  have denominator := tendsto_pi_nhds.mp (tendsto_pi_nhds.mp residue (residueIndex branch)) (residueIndex branch)
  have ratio := numerator.div denominator (em_leading_pivot branch n unit)
  rw [em_leading_read branch n unit] at ratio
  have scale (v : Fin 5 → ℂ) : (regularScaling 0 *ᵥ v) (residueIndex branch) = v (residueIndex branch) := by
    rw [regularScaling,Matrix.mulVec_diagonal]
    fin_cases branch <;> norm_num [residueIndex]
  rw [scale] at ratio
  exact ratio

private theorem em_five_single (j : Fin 5) (a : ℂ) :
    fiveVector (Pi.single j a) = Pi.single (fiveIndex j) a := by
  funext i
  by_cases inside : i.val<5
  · simp [fiveVector,inside,Pi.single_apply,fiveIndex,Fin.ext_iff]
  · have different : fiveIndex j≠i := by
      intro same
      have equal := congrArg Fin.val same
      simp only [fiveIndex] at equal
      omega
    simp [fiveVector,inside,different]

private theorem em_normalized_coordinates (branch : Fin 2) (n : PhysicalMomentum) (unit : spatialSquare n=1) :
    Tendsto (fun e : scaleDomain => (2*(sourceSheet branch n unit e.val:ℂ)) •
      sourcePoleCoordinates branch e.val (sourceSheet branch n unit e.val) n)
      scaleApproach (𝓝 (Pi.single (fiveIndex (residueIndex branch)) (softCoefficient branch:ℂ))) := by
  have result := sourcePoleCoordinates_sheet branch n unit
  have scaling : regularScaling 0 *ᵥ Pi.single (residueIndex branch) (softCoefficient branch:ℂ) =
      Pi.single (residueIndex branch) (softCoefficient branch:ℂ) := by
    funext i
    rw [regularScaling,Matrix.mulVec_diagonal]
    by_cases same : i=residueIndex branch
    · subst i
      fin_cases branch <;> simp [residueIndex]
    · simp [same]
  rw [Matrix.single_mulVec] at result
  simp only [Pi.single_eq_same,mul_one] at result
  change Tendsto _ _ (𝓝 (fiveVector (regularScaling 0 *ᵥ Pi.single (residueIndex branch) (softCoefficient branch:ℂ)))) at result
  rw [scaling,em_five_single] at result
  exact result

/-- The whole frequency polarization's actual EM output is epsilon-squared, with fast and full residual paid through its original Frechet law. -/
theorem em_right_projection_limit (branch : Fin 2) (n : PhysicalMomentum) (unit : spatialSquare n=1)
    (mu : Fin 4) :
    Tendsto (fun e : scaleDomain => (2*(sourceSheet branch n unit e.val:ℂ)) *
      (emInsertion.transpose *ᵥ sourceNativeFrequencyPolarization branch e.val (sourceSheet branch n unit e.val) n) mu /
        (e.val:ℂ)^2)
      scaleApproach (𝓝 (emInfraredJet (physicalFrequencyMomentum (sourceSpeed branch) n) mu
        (fiveIndex (residueIndex branch)) * (softCoefficient branch:ℂ))) := by
  have coords := em_normalized_coordinates branch n unit
  have entry (j : Fin 289) := (em_frame_divided_limit 1 branch n unit mu j).mul
    (tendsto_pi_nhds.mp coords j)
  have result := tendsto_finsetSum Finset.univ (fun j _ => entry j)
  simp only [one_smul] at result
  have value : (∑j : Fin 289,emInfraredJet (physicalFrequencyMomentum (sourceSpeed branch) n) mu j *
      ((Pi.single (fiveIndex (residueIndex branch)) (softCoefficient branch:ℂ) : Fin 289 → ℂ) j)) =
      emInfraredJet (physicalFrequencyMomentum (sourceSpeed branch) n) mu (fiveIndex (residueIndex branch)) *
        (softCoefficient branch:ℂ) := by
    exact dotProduct_single (v:=fun j : Fin 289 => emInfraredJet (physicalFrequencyMomentum (sourceSpeed branch) n) mu j)
      (softCoefficient branch:ℂ) (fiveIndex (residueIndex branch))
  rw [value] at result
  apply result.congr'
  filter_upwards [] with e
  rw [sourceNativeFrequencyPolarization_frame branch e.val _ n e.property.1.ne',Matrix.mulVec_mulVec]
  change (∑j : Fin 289,emInfraredFrame (frequencyRay e.val (sourceSheet branch n unit e.val) n) mu j /
      (e.val:ℂ)^2 * ((2*(sourceSheet branch n unit e.val:ℂ)) •
        sourcePoleCoordinates branch e.val (sourceSheet branch n unit e.val) n) j) = _
  simp only [Matrix.mulVec, dotProduct,Pi.smul_apply,smul_eq_mul,Finset.mul_sum,Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j _
  change _ = (2*(sourceSheet branch n unit e.val:ℂ)) *
    (emInfraredFrame _ mu j * sourcePoleCoordinates branch e.val _ n j) / (e.val:ℂ)^2
  ring


private theorem em_jet_slow (v : Fin 4 → ℂ) (mu : Fin 4) (k : Fin 3) :
    emInfraredJet v mu ⟨k.val,by omega⟩ =
      emLiteralA v mu * (Pi.single 0 (1:ℂ) : Fin 289 → ℂ) ⟨k.val,by omega⟩ +
      emLiteralB v mu * (Pi.single 1 (1:ℂ) : Fin 289 → ℂ) ⟨k.val,by omega⟩ := by
  have col : (fun row => sourceChargedNativeFrameJet v row ⟨k.val,by omega⟩) =
      sourceMatrix sourceEnergyChannelTerms v *ᵥ Pi.single ⟨k.val,by omega⟩ (1:ℂ) := by
    funext row
    rw [Matrix.mulVec_single_one]
    exact (sourceEnergyChannelMatrix_entry v row k).symm
  have projected := congrArg (fun V : Fin 289 → ℂ => (emInsertion.transpose *ᵥ V) mu) col
  rw [em_literal_projection] at projected
  change emInfraredJet v mu ⟨k.val,by omega⟩ = _ at projected
  simpa only [Pi.single_apply,eq_comm] using projected

/-- The original branch pivot chooses column one or two; the computed EM jet is B or zero. -/
theorem em_branch_jet (v : Fin 4 → ℂ) (mu : Fin 4) (branch : Fin 2) :
    emInfraredJet v mu (fiveIndex (residueIndex branch)) =
      if branch=0 then emLiteralB v mu else 0 := by
  fin_cases branch
  · have result := em_jet_slow v mu 1
    norm_num [residueIndex,fiveIndex,Pi.single_apply,Fin.ext_iff] at result ⊢
    exact result
  · have result := em_jet_slow v mu 2
    norm_num [residueIndex,fiveIndex,Pi.single_apply,Fin.ext_iff] at result ⊢
    exact result

/-- Both genuine EM ends consume their original full residue before taking the infrared limit. -/
theorem em_pole_tensor_normalized_limit (branch : Fin 2) (n : PhysicalMomentum) (unit : spatialSquare n=1)
    (mu nu : Fin 4) :
    Tendsto (fun e : scaleDomain => (2*(sourceSheet branch n unit e.val:ℂ))*
      emPoleTensor e.val (sourceSheet branch n unit e.val) n mu nu)
      scaleApproach (𝓝 (-(softCoefficient branch:ℂ)*
        emInfraredJet (physicalFrequencyMomentum (sourceSpeed branch) n) mu (fiveIndex (residueIndex branch))*
        emInfraredJet (physicalFrequencyMomentum (sourceSpeed branch) n) nu (fiveIndex (residueIndex branch)))) := by
  have left := em_left_cofactor_limit branch n unit nu
  have right := em_right_projection_limit branch n unit mu
  have result := left.mul right
  have scalar (a b c : ℂ) : (-a)*(b*c)= -c*b*a := by ring
  rw [scalar] at result
  apply result.congr'
  filter_upwards [sourceWholePhotonResidue_factor branch n unit] with e factor
  have entry : emPoleTensor e.val (sourceSheet branch n unit e.val) n mu nu =
      sourcePhotonLeftReader branch e.val (sourceSheet branch n unit e.val) n (emSourceColumn nu) *
        (emInsertion.transpose *ᵥ sourceNativePolarization branch e.val (sourceSheet branch n unit e.val) n) mu := by
    have applied := congrArg (fun V : Fin 289 → ℂ => (emInsertion.transpose *ᵥ V) mu)
      (factor (emSourceColumn nu))
    rw [Matrix.mulVec_smul] at applied
    change (emInsertion.transpose *ᵥ
      (sourceWholePhotonResidue e.val (sourceSheet branch n unit e.val) n *ᵥ emSourceColumn nu)) mu = _ at applied
    rw [Matrix.mulVec_mulVec] at applied
    exact applied
  rw [entry,sourceNativeFrequencyPolarization,Matrix.mulVec_smul]
  simp only [Pi.smul_apply,Complex.real_smul,Complex.ofReal_pow]
  have ne : (e.val:ℂ)≠0 := Complex.ofReal_ne_zero.mpr e.property.1.ne'
  field_simp [ne]

/-- Complete four-by-four source IR coefficient of the genuine EM sheet residue. -/
def emInfraredTensor (branch : Fin 2) (n : PhysicalMomentum) : Matrix (Fin 4) (Fin 4) ℂ :=
  fun mu nu => if branch=0 then
    -(softCoefficient branch:ℂ)/(2*(sourceSpeed branch:ℂ)) *
      emLiteralB (physicalFrequencyMomentum (sourceSpeed branch) n) mu *
      emLiteralB (physicalFrequencyMomentum (sourceSpeed branch) n) nu else 0

theorem em_pole_tensor_limit (branch : Fin 2) (n : PhysicalMomentum) (unit : spatialSquare n=1)
    (mu nu : Fin 4) :
    Tendsto (fun e : scaleDomain => emPoleTensor e.val (sourceSheet branch n unit e.val) n mu nu)
      scaleApproach (𝓝 (emInfraredTensor branch n mu nu)) := by
  have slope : Tendsto (fun e : scaleDomain => 2*(sourceSheet branch n unit e.val:ℂ))
      scaleApproach (𝓝 (2*(sourceSpeed branch:ℂ))) :=
    tendsto_const_nhds.mul (Complex.continuous_ofReal.continuousAt.tendsto.comp
      ((sourceSheet_tendsto branch n unit).comp scaleVal_tendsto))
  have ne : 2*(sourceSpeed branch:ℂ)≠0 := mul_ne_zero (by norm_num)
    (Complex.ofReal_ne_zero.mpr (sourceSpeed_positive branch).ne')
  have result := (em_pole_tensor_normalized_limit branch n unit mu nu).div slope ne
  have limit : (-(softCoefficient branch:ℂ)*
      emInfraredJet (physicalFrequencyMomentum (sourceSpeed branch) n) mu (fiveIndex (residueIndex branch))*
      emInfraredJet (physicalFrequencyMomentum (sourceSpeed branch) n) nu (fiveIndex (residueIndex branch))) /
      (2*(sourceSpeed branch:ℂ)) = emInfraredTensor branch n mu nu := by
    rw [em_branch_jet,em_branch_jet]
    unfold emInfraredTensor
    split_ifs <;> ring
  rw [limit] at result
  apply result.congr'
  filter_upwards [slope.eventually_ne ne] with e nonzero
  exact mul_div_cancel_left₀ _ nonzero

/-- The physical-frequency tensor uses the actual epsilon-squared conversion once. -/
def emFrequencyPoleTensor (epsilon s : ℝ) (n : PhysicalMomentum) : Matrix (Fin 4) (Fin 4) ℂ :=
  emInsertion.transpose * sourceWholePhotonFrequencyResidue epsilon s n * emInsertion

theorem em_frequency_pole_scaled (epsilon s : ℝ) (n : PhysicalMomentum) :
    emFrequencyPoleTensor epsilon s n = (epsilon:ℂ)^2 • emPoleTensor epsilon s n := by
  unfold emFrequencyPoleTensor sourceWholePhotonFrequencyResidue emPoleTensor
  rw [Matrix.mul_smul,Matrix.smul_mul]
  ext i j
  simp only [Matrix.smul_apply,Complex.real_smul,Complex.ofReal_pow,smul_eq_mul]

/-- Every physical EM frequency residue entry has its source-generated epsilon-squared coefficient, with both branches retained separately. -/
theorem em_frequency_pole_leading (branch : Fin 2) (n : PhysicalMomentum) (unit : spatialSquare n=1)
    (mu nu : Fin 4) :
    Tendsto (fun e : scaleDomain =>
      emFrequencyPoleTensor e.val (sourceSheet branch n unit e.val) n mu nu/(e.val:ℂ)^2)
      scaleApproach (𝓝 (emInfraredTensor branch n mu nu)) := by
  apply (em_pole_tensor_limit branch n unit mu nu).congr'
  filter_upwards [] with e
  rw [em_frequency_pole_scaled]
  simp only [Matrix.smul_apply,smul_eq_mul]
  exact (mul_div_cancel_left₀ _ (pow_ne_zero _ (Complex.ofReal_ne_zero.mpr e.property.1.ne'))).symm


/-- The first actual branch has a nonzero EM IR residue coefficient without choosing a spatial direction. -/
theorem em_ir_first_branch_nonzero (n : PhysicalMomentum) : emInfraredTensor 0 n 0 0 ≠ 0 := by
  have speed : (sourceSpeed 0:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (sourceSpeed_positive 0).ne'
  have soft : (softCoefficient 0:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (softCoefficient_nonzero 0)
  have B : emLiteralB (physicalFrequencyMomentum (sourceSpeed 0) n) 0≠0 := by
    change -(8/11:ℂ)*(-Complex.I*(sourceSpeed 0:ℂ))≠0
    exact mul_ne_zero (by norm_num) (mul_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero) speed)
  change (-(softCoefficient 0:ℂ)/(2*(sourceSpeed 0:ℂ)))*
    emLiteralB (physicalFrequencyMomentum (sourceSpeed 0) n) 0*
    emLiteralB (physicalFrequencyMomentum (sourceSpeed 0) n) 0≠0
  exact mul_ne_zero (mul_ne_zero (div_ne_zero (neg_ne_zero.mpr soft) (mul_ne_zero (by norm_num) speed)) B) B

/-- Only the epsilon-squared coefficient of branch one is zero; the complete branch and its higher terms remain. -/
theorem em_ir_second_branch_zero (n : PhysicalMomentum) : emInfraredTensor 1 n = 0 := by
  ext mu nu
  simp [emInfraredTensor]

/-- The genuine two-ended first-branch EM pole is nonzero on its generated small-scale sheet. -/
theorem em_first_frequency_pole_nonzero (n : PhysicalMomentum) (unit : spatialSquare n=1) :
    ∀ᶠ e in scaleApproach, emFrequencyPoleTensor e.val (sourceSheet 0 n unit e.val) n 0 0 ≠ 0 := by
  filter_upwards [(em_frequency_pole_leading 0 n unit 0 0).eventually_ne (em_ir_first_branch_nonzero n)] with e h
  intro zero
  rw [zero,zero_div] at h
  exact h rfl

/-- Fixed actual full currents may have the genuine epsilon-minus-two left order; it is paired with the paid right order before the limit. -/
theorem em_full_current_response_ir (branch : Fin 2) (n : PhysicalMomentum) (unit : spatialSquare n=1)
    (forcing : Fin 289 → ℂ) (mu : Fin 4) :
    Tendsto (fun e : scaleDomain => (2*(sourceSheet branch n unit e.val:ℂ))*
      (emInsertion.transpose *ᵥ (sourceWholePhotonFrequencyResidue e.val (sourceSheet branch n unit e.val) n *ᵥ forcing)) mu)
      scaleApproach (𝓝 (sourceCurvatureEmitterInput forcing (residueIndex branch)*
        emInfraredJet (physicalFrequencyMomentum (sourceSpeed branch) n) mu (fiveIndex (residueIndex branch))*
        (softCoefficient branch:ℂ))) := by
  have left := sourcePhotonLeftReader_sheet branch n unit forcing
  have right := em_right_projection_limit branch n unit mu
  have result := left.mul right
  have scalar (a b c : ℂ) : a*(b*c)=a*b*c := by ring
  rw [scalar] at result
  apply result.congr'
  filter_upwards [sourceWholePhotonResidue_factor branch n unit] with e factor
  rw [sourceWholePhotonFrequencyResidue,Matrix.smul_mulVec,factor,smul_comm,
    ←sourceNativeFrequencyPolarization,Matrix.mulVec_smul]
  simp only [Pi.smul_apply,smul_eq_mul]
  have ne : (e.val:ℂ)≠0 := Complex.ofReal_ne_zero.mpr e.property.1.ne'
  field_simp [ne]

end LowEnergy.GaussComposite.ActualEMCarrierOwn
