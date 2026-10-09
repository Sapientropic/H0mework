import H0mework.Versions.R9c73a630.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualEMCauchyPoleJet

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualEMCauchyDynamic
open SaturationMonoid.PhysicsCore
open PreparationVacuumOriginalGreenFeedback PreparationVacuumPhysicalFeedback
open PreparationVacuumFullOriginResponse PreparationVacuumWholeOrigin PreparationVacuumMixedPrincipal
open PreparationVacuumPhysicalCharacteristic PreparationVacuumPhysicalPoleSheet
open PreparationVacuumPhysicalChargedFieldFactor PreparationVacuumMixedFieldReturn
open PreparationPhysicalNativePoleChargeReturn PreparationPhysicalNativePhotonFluxReturn
open PreparationPhysicalNativePolarizationEmitter PreparationPhysicalNormalizedFullField
open PreparationVacuumNativeSlowCoupling PreparationVacuumSoftPoleSelection
open PreparationVacuumNativePoleTensor PreparationVacuumFullSlowFieldResponse
open PreparationPhysicalCurvatureSheetLimit CanonicalGradedSpatialSource ActualEMCarrierOwn
open Filter Set Asymptotics
open scoped Matrix BigOperators Topology ContDiff Matrix.Norms.Operator
attribute [local irreducible] sourceNativeFrame sourceChargedNativeFrameJet fullNativeOrigin

/-- Literal native Y gauge insertion, used only as a source component. -/
def voltageYColumn (mu : Fin 4) : Fin 289→ℂ := Pi.single (gaugeSlot mu 11) 1

def voltageYFrame (p : Fin 4→ℂ) (mu : Fin 4) (j : Fin 289) : ℂ :=
  sourceNativeFrame p (gaugeSlot mu 11) j

def voltageYJet (v : Fin 4→ℂ) (mu : Fin 4) (j : Fin 289) : ℂ :=
  sourceChargedNativeFrameJet v (gaugeSlot mu 11) j

private theorem frame_origin (mu : Fin 4) (j : Fin 289) : voltageYFrame 0 mu j=0 := by
  rw [voltageYFrame,sourceChargedNativeFrame_origin]
  simp only [Matrix.mul_apply,VoltageJetTable.voltage_y_origin,zero_mul,Finset.sum_const_zero]

private def frameEntry (mu : Fin 4) (j : Fin 289) :
    (Matrix (Fin 289) (Fin 289) ℂ)→L[ℝ]ℂ :=
  ({ toFun:=fun M=>M (gaugeSlot mu 11) j
     map_add':=fun _ _=>rfl
     map_smul':=fun _ _=>rfl } : (Matrix (Fin 289) (Fin 289) ℂ)→ₗ[ℝ]ℂ).toContinuousLinearMap

private theorem frame_smooth (mu : Fin 4) (j : Fin 289) :
    ContDiffAt ℝ ∞ (fun p=>voltageYFrame p mu j) 0 :=
  (frameEntry mu j).contDiff.contDiffAt.comp 0 sourceNativeFrame_smooth

private theorem frame_frechet (v : Fin 4→ℂ) (mu : Fin 4) (j : Fin 289) :
    (fderiv ℝ (fun p=>voltageYFrame p mu j) 0) v=voltageYJet v mu j := by
  have ray : HasDerivAt (fun d : ℝ=>(d:ℂ) • v) v 0 := by
    simpa using (hasDerivAt_id (0:ℝ)).ofReal_comp.smul_const v
  have left:=((frame_smooth mu j).differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt_of_eq
    (0:ℝ) ray (show (0:Fin 4→ℂ)=(0:ℂ) • v by simp)
  have right:=(frameEntry mu j).hasFDerivAt.comp_hasDerivAt (0:ℝ) (sourceChargedNativeFrame_derivative v)
  exact left.unique right

private theorem moving_divided (f : (Fin 4 → ℂ) → ℂ)
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

private theorem ray_real (e s : ℝ) (n : PhysicalMomentum) :
    frequencyRay e s n = (e^2:ℝ) • physicalFrequencyMomentum s n := by
  rw [frequencyRay_scaled]
  funext i
  simp only [Pi.smul_apply,Complex.real_smul,Complex.ofReal_pow,smul_eq_mul]

/-- The complete reflected or forward native Y frame pays its epsilon-squared first term on the actual moving sheet. -/
theorem voltage_y_frame_divided (sign : ℝ) (branch : Fin 2) (n : PhysicalMomentum)
    (unit : spatialSquare n=1) (mu : Fin 4) (j : Fin 289) :
    Tendsto (fun e : scaleDomain =>
      voltageYFrame (sign • frequencyRay e.val (sourceSheet branch n unit e.val) n) mu j/(e.val:ℂ)^2)
      scaleApproach (𝓝 (sign • voltageYJet (physicalFrequencyMomentum (sourceSpeed branch) n) mu j)) := by
  have moving := (tendsto_const_nhds (x:=sign)).smul (sourceCurvatureDirection_tendsto branch n unit)
  have result := moving_divided (fun p => voltageYFrame p mu j)
    ((frame_smooth mu j).differentiableAt (by simp)) (frame_origin mu j)
    (fun e => sign • physicalFrequencyMomentum (sourceSheet branch n unit e.val) n)
    (sign • physicalFrequencyMomentum (sourceSpeed branch) n) moving
  rw [map_smul,frame_frechet] at result
  apply result.congr'
  filter_upwards [] with e
  rw [ray_real,smul_comm]

private theorem reflected_row (p : Fin 4→ℂ) (mu : Fin 4) (i : Fin 5) :
    (slowFastFrame.transpose *ᵥ (rawEffectiveReader p *ᵥ activeForcing p (voltageYColumn mu))) (fiveIndex i)=
      voltageYFrame (-p) mu (fiveIndex i) := by
  have reflected:=congrArg (fun M : Matrix (Fin 289) (Fin 289) ℂ=>
    (M*ᵥvoltageYColumn mu) (fiveIndex i)) (em_reader_frame_reciprocity p)
  have left : slowFastFrame.transpose *ᵥ (rawEffectiveReader p *ᵥ activeForcing p (voltageYColumn mu))=
      (slowFastFrame.transpose*sourceNativeReader p)*ᵥvoltageYColumn mu := by
    simp only [sourceNativeReader,activeForcing,Matrix.mulVec_mulVec,Matrix.mul_assoc]
  rw [left,reflected,voltageYColumn,Matrix.mulVec_single_one]
  rfl

theorem voltage_y_mode_forcing_scaled (epsilon s : ℝ) (n : PhysicalMomentum) (nonzero : epsilon≠0)
    (mu : Fin 4) :
    nativeModeForcing epsilon s n (voltageYColumn mu) =
      regularScaling epsilon *ᵥ (fun i : Fin 5 =>
        voltageYFrame (-(frequencyRay epsilon s n)) mu (fiveIndex i)/(epsilon:ℂ)^2) := by
  have ne : (epsilon:ℂ)≠0 := Complex.ofReal_ne_zero.mpr nonzero
  funext i
  unfold nativeModeForcing
  simp only [wideRayScaling,Matrix.mulVec_diagonal]
  rw [reflected_row]
  simp only [regularScaling,Matrix.mulVec_diagonal,fiveIndex,i.isLt,if_true]
  split_ifs <;> field_simp [ne]

private theorem voltage_regular_continuous : Continuous regularScaling := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  unfold regularScaling
  simp only [Matrix.diagonal_apply]
  split_ifs <;> fun_prop

private theorem voltage_mulVec_limit {X : Type*} {m n : ℕ} {L : Filter X}
    {A : X → Matrix (Fin m) (Fin n) ℂ} {v : X → Fin n → ℂ}
    {B : Matrix (Fin m) (Fin n) ℂ} {w : Fin n → ℂ}
    (matrix : Tendsto A L (𝓝 B)) (vector : Tendsto v L (𝓝 w)) :
    Tendsto (fun x => A x *ᵥ v x) L (𝓝 (B *ᵥ w)) := by
  have cont : Continuous (fun p : Matrix (Fin m) (Fin n) ℂ × (Fin n → ℂ) => p.1 *ᵥ p.2) :=
    continuous_fst.matrix_mulVec continuous_snd
  exact (cont.tendsto _).comp (matrix.prodMk_nhds vector)

/-- The literal Y source left forcing has a finite generated limit after all original scale factors. -/
theorem voltage_y_mode_forcing_limit (branch : Fin 2) (n : PhysicalMomentum) (unit : spatialSquare n=1)
    (mu : Fin 4) :
    Tendsto (fun e : scaleDomain => nativeModeForcing e.val (sourceSheet branch n unit e.val) n (voltageYColumn mu))
      scaleApproach (𝓝 (regularScaling 0 *ᵥ fun i : Fin 5 =>
        -voltageYJet (physicalFrequencyMomentum (sourceSpeed branch) n) mu (fiveIndex i))) := by
  have entries : Tendsto (fun e : scaleDomain => fun i : Fin 5 =>
      voltageYFrame (-(frequencyRay e.val (sourceSheet branch n unit e.val) n)) mu (fiveIndex i)/(e.val:ℂ)^2)
      scaleApproach (𝓝 (fun i : Fin 5 => -voltageYJet (physicalFrequencyMomentum (sourceSpeed branch) n) mu (fiveIndex i))) := by
    apply tendsto_pi_nhds.mpr
    intro i
    simpa only [neg_one_smul] using voltage_y_frame_divided (-1) branch n unit mu (fiveIndex i)
  have result := voltage_mulVec_limit (voltage_regular_continuous.continuousAt.tendsto.comp scaleVal_tendsto) entries
  exact result.congr' (Eventually.of_forall (fun e => (voltage_y_mode_forcing_scaled e.val _ n e.property.1.ne' mu).symm))


private theorem voltage_leading_pivot (branch : Fin 2) (n : PhysicalMomentum) (unit : spatialSquare n=1) :
    leadingResidue branch n (residueIndex branch) (residueIndex branch) ≠ 0 := by
  have diagonal := congrFun (congrFun (leadingResidue_normalization branch n unit) (residueIndex branch)) (residueIndex branch)
  simp only [Matrix.smul_apply,Matrix.single_apply,smul_eq_mul] at diagonal
  intro zero
  rw [zero,mul_zero] at diagonal
  exact (Complex.ofReal_ne_zero.mpr (softCoefficient_nonzero branch)) diagonal.symm

private theorem voltage_leading_read (branch : Fin 2) (n : PhysicalMomentum) (unit : spatialSquare n=1)
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
  apply (div_eq_iff (voltage_leading_pivot branch n unit)).mpr
  apply mul_left_cancel₀ scale
  rw [column]
  calc
    _ = (2*(sourceSpeed branch:ℂ)*leadingResidue branch n (residueIndex branch) (residueIndex branch))*v (residueIndex branch) :=
      congrArg (fun z : ℂ => z*v (residueIndex branch)) diagonal.symm
    _ = _ := by ring

/-- The native Y source cofactor is finite: its limit is the reflected source first jet on the source-selected branch. -/
theorem voltage_y_left_cofactor_limit (branch : Fin 2) (n : PhysicalMomentum) (unit : spatialSquare n=1)
    (mu : Fin 4) :
    Tendsto (fun e : scaleDomain =>
      sourcePhotonLeftReader branch e.val (sourceSheet branch n unit e.val) n (voltageYColumn mu))
      scaleApproach (𝓝 (-voltageYJet (physicalFrequencyMomentum (sourceSpeed branch) n) mu
        (fiveIndex (residueIndex branch)))) := by
  have residue := sourceResidue_soft_limit branch n unit
  have product := voltage_mulVec_limit residue (voltage_y_mode_forcing_limit branch n unit mu)
  have numerator := tendsto_pi_nhds.mp product (residueIndex branch)
  have denominator := tendsto_pi_nhds.mp (tendsto_pi_nhds.mp residue (residueIndex branch)) (residueIndex branch)
  have ratio := numerator.div denominator (voltage_leading_pivot branch n unit)
  rw [voltage_leading_read branch n unit] at ratio
  have scale (v : Fin 5 → ℂ) : (regularScaling 0 *ᵥ v) (residueIndex branch) = v (residueIndex branch) := by
    rw [regularScaling,Matrix.mulVec_diagonal]
    fin_cases branch <;> norm_num [residueIndex]
  rw [scale] at ratio
  exact ratio



/-- The source-fixed longitudinal initial electric co-source before physical spatial scaling. -/
def voltageUnitInitialSource (n : PhysicalMomentum) : Fin 289→ℂ :=
  ∑j : Fin 3,(2*(Stage9C.Material.SpinPair.lapse:ℂ)*Complex.I*(n j:ℂ)) • voltageYColumn j.succ

/-- The actual Cauchy source has its original physical epsilon-squared momentum factor. -/
theorem voltage_initial_forcing_scaled (e omega : ℝ) (n : PhysicalMomentum) :
    voltageInitialFrequencyForcing e omega n=(e:ℂ)^2 • voltageUnitInitialSource n := by
  rw [voltageInitialFrequencyForcing,voltage_initial_boundary_native]
  ext r
  norm_num [voltageInitialNativeSource,voltageUnitInitialSource,voltageYColumn,gaugeSlot,
    Fin.sum_univ_three,Pi.single_apply,Pi.smul_apply,smul_eq_mul,Fin.ext_iff]
  split_ifs <;> try omega
  all_goals ring

/-- The initial event's left pole coefficient retains the full five-mode cofactor. -/
def voltageInitialEmitter (branch : Fin 2) (e s : ℝ) (n : PhysicalMomentum) : ℂ :=
  sourcePhotonLeftReader branch e s n (voltageInitialFrequencyForcing e (sourceFrequency e s) n)

private theorem initial_emitter_scaled (branch : Fin 2) (n : PhysicalMomentum) (unit : spatialSquare n=1) :
    ∀ᶠ e in scaleApproach,
      voltageInitialEmitter branch e.val (sourceSheet branch n unit e.val) n/(e.val:ℂ)^2=
        ∑j : Fin 3,(2*(Stage9C.Material.SpinPair.lapse:ℂ)*Complex.I*(n j:ℂ))*
          sourcePhotonLeftReader branch e.val (sourceSheet branch n unit e.val) n (voltageYColumn j.succ) := by
  filter_upwards [em_cofactor_read_generated branch n unit] with e generated
  unfold voltageInitialEmitter
  rw [generated,voltage_initial_forcing_scaled,voltageUnitInitialSource,map_smul,map_sum]
  simp only [map_smul,smul_eq_mul]
  have ne : (e.val:ℂ)^2≠0:=pow_ne_zero _ (Complex.ofReal_ne_zero.mpr e.property.1.ne')
  rw [mul_div_cancel_left₀ _ ne]
  apply Finset.sum_congr rfl
  intro j _
  rw [generated]

/-- The actual longitudinal initial source selects its leading cofactor by the generated sheets. -/
theorem voltage_initial_emitter_ir (branch : Fin 2) (n : PhysicalMomentum) (unit : spatialSquare n=1) :
    Tendsto (fun e : scaleDomain=>voltageInitialEmitter branch e.val (sourceSheet branch n unit e.val) n/(e.val:ℂ)^2)
      scaleApproach (𝓝 (if branch=0 then (50/67:ℂ)*(Stage9C.Material.SpinPair.lapse:ℂ) else 0)) := by
  have terms (j : Fin 3):=(tendsto_const_nhds (x:=2*(Stage9C.Material.SpinPair.lapse:ℂ)*Complex.I*(n j:ℂ))).mul
    (voltage_y_left_cofactor_limit branch n unit j.succ)
  have result:=tendsto_finsetSum Finset.univ (fun j _=>terms j)
  have generated : (∑j : Fin 3,(2*(Stage9C.Material.SpinPair.lapse:ℂ)*Complex.I*(n j:ℂ))*
      (-voltageYJet (physicalFrequencyMomentum (sourceSpeed branch) n) j.succ (fiveIndex (residueIndex branch))))=
      if branch=0 then (50/67:ℂ)*(Stage9C.Material.SpinPair.lapse:ℂ) else 0 := by
    have nunit : ∑j : Fin 3,(n j:ℂ)^2=1 := by
      have realUnit : ∑j : Fin 3,(n j)^2=1 := by
        simpa only [Fin.sum_univ_three,spatialSquare] using unit
      exact_mod_cast realUnit
    simp only [voltageYJet,VoltageJetTable.voltage_y_frame_jet,
      if_neg (Fin.succ_ne_zero _),physicalFrequencyMomentum,Fin.cases_succ]
    fin_cases branch
    · norm_num [residueIndex,fiveIndex,Pi.single_apply]
      calc
        _=(50/67:ℂ)*(Stage9C.Material.SpinPair.lapse:ℂ)*(∑j : Fin 3,(n j:ℂ)^2) := by
          rw [Finset.mul_sum,←Finset.sum_neg_distrib]
          apply Finset.sum_congr rfl
          intro j _
          ring_nf
          simp only [Complex.I_sq]
          ring
        _=_ := by rw [nunit,mul_one]
    · norm_num [residueIndex,fiveIndex,Pi.single_apply]
  rw [generated] at result
  apply result.congr'
  filter_upwards [initial_emitter_scaled branch n unit] with e same
  exact same.symm

/-- The actual initial co-source contracts the full frequency residue, preserving its independent left reader. -/
theorem voltage_initial_pole_factor (branch : Fin 2) (n : PhysicalMomentum) (unit : spatialSquare n=1) :
    ∀ᶠ e in scaleApproach,
      voltageInitialPole e.val (sourceSheet branch n unit e.val) n=
        voltageInitialEmitter branch e.val (sourceSheet branch n unit e.val) n •
          sourceNativeFrequencyPolarization branch e.val (sourceSheet branch n unit e.val) n := by
  filter_upwards [sourceWholePhotonResidue_factor branch n unit] with e factor
  rw [voltageInitialPole,sourceWholePhotonFrequencyResidue,Matrix.smul_mulVec,factor,
    sourceNativeFrequencyPolarization,voltageInitialEmitter]
  exact smul_comm _ _ _

end LowEnergy.GaussComposite.ActualEMCauchyDynamic
