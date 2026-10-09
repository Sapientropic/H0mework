import H0mework.Versions.R9c73a630.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceObservedFieldVertex

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumObservedBoundaryResidue
open GaussCoreHilbert CanonicalGradedSpatialSource
open PreparationVacuumObservedPoleTensor PreparationVacuumPhysicalSlowBlock
open PreparationVacuumPhysicalPinnedVelocity PreparationVacuumQuantumSlowResponse
open PreparationVacuumQuantumSlowResidue PreparationVacuumGaugeSlowFrequency
open PreparationVacuumElectromagneticIdentity PreparationVacuumPhysicalFeedback
open PreparationVacuumMixedFieldReturn PreparationVacuumMovingPoleGaussReturn
open Filter Set
open scoped Topology
attribute [local irreducible] sourceResonanceProjection sourceOffPoleReturn sourceEqualProjection
  sourceFullInitialUpper sourceFullInitialBase sourceRetainerReturn sourcePoleRead
  sourceBaseResidue sourceUpperResidue sourceGaugeResidue

/-- The complete pinned spectral numerator, including every resonance and escape channel. -/
def sourceBoundaryRegular (F : GaussUnitaryHistory.Index) (n : PhysicalMomentum) (c eta : ℝ) : SourceOp :=
  sourceResonanceProjection F n c+(eta:ℂ) • sourceOffPoleReturn F n c eta

theorem sourceBoundaryRegular_generated (F : GaussUnitaryHistory.Index) (n : PhysicalMomentum)
    (c eta : ℝ) (positive : 0<eta) :
    sourceBoundaryRegular F n c eta=(eta:ℂ) • sourcePinnedResolvent F n (sourcePoleSide c eta) := by
  rw [sourcePinnedResolvent_boundary F n c eta positive]
  apply ContinuousLinearMap.ext
  intro x
  change sourceResonanceProjection F n c x+(eta:ℂ) • sourceOffPoleReturn F n c eta x=
    (eta:ℂ) • ((eta:ℂ)⁻¹ • sourceResonanceProjection F n c x+sourceOffPoleReturn F n c eta x)
  rw [smul_add,smul_smul,mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr positive.ne'),one_smul]

theorem sourceBoundaryRegular_error (F : GaussUnitaryHistory.Index) (n : PhysicalMomentum) (c eta : ℝ) :
    ‖sourceBoundaryRegular F n c eta-sourceResonanceProjection F n c‖ ≤ abs eta*sourceOffPolePrice F n c := by
  rw [sourceBoundaryRegular,add_sub_cancel_left]
  exact (ContinuousLinearMap.opNorm_smul_le _ _).trans
    ((mul_le_mul_of_nonneg_left (sourceOffPoleReturn_price F n c eta) (norm_nonneg (eta:ℂ))).trans_eq
      (by rw [Complex.norm_real,Real.norm_eq_abs]))

theorem sourceBoundaryRegular_limit (F : GaussUnitaryHistory.Index) (n : PhysicalMomentum) (c : ℝ) :
    Tendsto (sourceBoundaryRegular F n c) (𝓝 0) (𝓝 (sourceResonanceProjection F n c)) := by
  have scalar:=Complex.continuous_ofReal.tendsto (0:ℝ)
  have limit:=(tendsto_const_nhds (x:=sourceResonanceProjection F n c)).add
    (scalar.smul (sourceOffPoleReturn_limit F n c))
  have zero : (0:ℂ) • sourceOffPoleReturn F n c 0=0 := by
    apply ContinuousLinearMap.ext
    intro x
    exact zero_smul ℂ _
  simp only [Complex.ofReal_zero,zero,add_zero] at limit
  apply limit.congr'
  exact Eventually.of_forall (fun eta=>by apply ContinuousLinearMap.ext;intro x;rfl)

def sourceUpperNumerator (q : PhysicalResponsePoint) (n : PhysicalMomentum) (c eta : ℝ) (i : Fin 289) : SourceOp :=
  sourceBoundaryRegular q.F n c eta*sourceEqualProjection q.F (sourceFullInitialUpper q 0 0 i)

def sourceBaseNumerator (q : PhysicalResponsePoint) (n : PhysicalMomentum) (c eta : ℝ) (i : Fin 289) : SourceOp :=
  -(sourceBoundaryRegular q.F n c eta*sourceEqualProjection q.F
    (sourceRetainerReturn q.F (sourceUpperNumerator q n c eta i)))

def sourceGaugeNumerator (q : PhysicalResponsePoint) (n : PhysicalMomentum) (c eta : ℝ)
    (mu : Fin 4) (a : Fin 12) : SourceOp :=
  sourceBoundaryRegular q.F n c eta*sourceEqualProjection q.F (sourceFullInitialBase q 0 0 (gaugeSlot mu a))

private theorem op_smul_mul (z : ℂ) (X Y : SourceOp) : (z • X)*Y=z • (X*Y) := by
  apply ContinuousLinearMap.ext
  intro x
  rfl

private theorem quadratic_scaled (z : ℂ) (R U : SourceOp) (P K : SourceSuperOp) :
    -((z • R)*P (K (z • U)))=z^2 • (-(R*P (K U))) := by
  rw [K.map_smul z U,P.map_smul z (K U)]
  apply ContinuousLinearMap.ext
  intro x
  change -(z • R (z • (P (K U) x)))=z^2 • (-(R (P (K U) x)))
  rw [R.map_smul,smul_smul,pow_two,smul_neg]

private theorem origin_projected (F : GaussUnitaryHistory.Index) (n : PhysicalMomentum) (zeta : ℂ) (X : SourceOp) :
    sourceOriginInverse F n zeta (sourceEqualProjection F X)=sourcePinnedResolvent F n zeta*sourceEqualProjection F X := by
  have idem:=congrArg (fun A : SourceSuperOp=>A X) (sourceEqualProjection_idempotent F)
  change sourceEqualProjection F (sourceEqualProjection F X)=sourceEqualProjection F X at idem
  simp only [sourceOriginInverse,add_apply,sourcePinnedLeadingInverse_apply,sourceOffProjection,
    sub_apply,one_apply_eq_self,idem,sub_self,add_zero]

/-- The source upper initial sector has its exact regular numerator. -/
theorem sourceUpperNumerator_generated (q : PhysicalResponsePoint) (n : PhysicalMomentum)
    (c eta : ℝ) (positive : 0<eta) (i : Fin 289) :
    (eta:ℂ) • sourceUpperResidue q n (sourcePoleSide c eta) i=sourceUpperNumerator q n c eta i := by
  rw [sourceUpperResidue,origin_projected,sourceUpperNumerator,
    sourceBoundaryRegular_generated q.F n c eta positive,op_smul_mul]

/-- The full nongauge second-order response keeps the actual retainer feedback. -/
theorem sourceBaseNumerator_generated (q : PhysicalResponsePoint) (n : PhysicalMomentum)
    (c eta : ℝ) (positive : 0<eta) (i : Fin 289) :
    ((eta:ℂ)^2) • sourceBaseResidue q n (sourcePoleSide c eta) i=sourceBaseNumerator q n c eta i := by
  let R:=sourcePinnedResolvent q.F n (sourcePoleSide c eta)
  let U:=sourceUpperResidue q n (sourcePoleSide c eta) i
  have base : sourceBaseResidue q n (sourcePoleSide c eta) i=
      -(R*sourceEqualProjection q.F (sourceRetainerReturn q.F U)) := by
    unfold sourceBaseResidue
    exact congrArg (fun X : SourceOp=> -X) (origin_projected q.F n (sourcePoleSide c eta) _)
  calc
    ((eta:ℂ)^2) • sourceBaseResidue q n (sourcePoleSide c eta) i=
      ((eta:ℂ)^2) • (-(R*sourceEqualProjection q.F (sourceRetainerReturn q.F U))) :=
      congrArg (fun X : SourceOp=>((eta:ℂ)^2) • X) base
    _= -(((eta:ℂ) • R)*sourceEqualProjection q.F (sourceRetainerReturn q.F ((eta:ℂ) • U))) :=
      (quadratic_scaled (eta:ℂ) R U (sourceEqualProjection q.F) (sourceRetainerReturn q.F)).symm
    _= -(sourceBoundaryRegular q.F n c eta*sourceEqualProjection q.F
        (sourceRetainerReturn q.F ((eta:ℂ) • U))) :=
      congrArg (fun X : SourceOp=> -(X*sourceEqualProjection q.F (sourceRetainerReturn q.F ((eta:ℂ) • U))))
        (sourceBoundaryRegular_generated q.F n c eta positive).symm
    _=sourceBaseNumerator q n c eta i :=
      congrArg (fun X : SourceOp=> -(sourceBoundaryRegular q.F n c eta*sourceEqualProjection q.F (sourceRetainerReturn q.F X)))
        (sourceUpperNumerator_generated q n c eta positive i)

/-- Each true gauge source has a first-order numerator. -/
theorem sourceGaugeNumerator_generated (q : PhysicalResponsePoint) (n : PhysicalMomentum)
    (c eta : ℝ) (positive : 0<eta) (mu : Fin 4) (a : Fin 12) :
    (eta:ℂ) • sourceGaugeResidue q n (sourcePoleSide c eta) mu a=sourceGaugeNumerator q n c eta mu a := by
  rw [sourceGaugeResidue,origin_projected,sourceGaugeNumerator,
    sourceBoundaryRegular_generated q.F n c eta positive,op_smul_mul]

def sourceWholeCurrentNumerator (q : PhysicalResponsePoint) (n : PhysicalMomentum) (c eta : ℝ)
    (l r : RestStateIndex) : Fin 289→ℂ :=
  fun i=> -sourcePoleRead q.epsilon q.precision 0 0 l r (sourceBaseNumerator q n c eta i)

def sourceGaugeCurrentNumerator (q : PhysicalResponsePoint) (n : PhysicalMomentum) (c eta : ℝ)
    (l r : RestStateIndex) (mu : Fin 4) (a : Fin 12) : ℂ :=
  -sourcePoleRead q.epsilon q.precision 0 0 l r (sourceGaugeNumerator q n c eta mu a)

theorem sourceWholeCurrentNumerator_generated (q : PhysicalResponsePoint) (n : PhysicalMomentum)
    (c eta : ℝ) (positive : 0<eta) (l r : RestStateIndex) :
    ((eta:ℂ)^2) • sourceFullCurrentResidue q n (sourcePoleSide c eta) l r=
      sourceWholeCurrentNumerator q n c eta l r := by
  funext i
  simp only [sourceFullCurrentResidue,sourceWholeCurrentNumerator,Pi.smul_apply]
  rw [←sourceBaseNumerator_generated q n c eta positive i,map_smul,smul_neg]

theorem sourceGaugeCurrentNumerator_generated (q : PhysicalResponsePoint) (n : PhysicalMomentum)
    (c eta : ℝ) (positive : 0<eta) (l r : RestStateIndex) (mu : Fin 4) (a : Fin 12) :
    (eta:ℂ)*sourceGaugeCurrentResidue q n (sourcePoleSide c eta) l r mu a=
      sourceGaugeCurrentNumerator q n c eta l r mu a := by
  simp only [sourceGaugeCurrentResidue,sourceGaugeCurrentNumerator]
  rw [←sourceGaugeNumerator_generated q n c eta positive mu a,map_smul,smul_eq_mul,mul_neg]

theorem sourceBoundaryRegular_zero (F : GaussUnitaryHistory.Index) (n : PhysicalMomentum) (c : ℝ) :
    sourceBoundaryRegular F n c 0=sourceResonanceProjection F n c := by
  apply ContinuousLinearMap.ext
  intro x
  change sourceResonanceProjection F n c x+(0:ℂ) • sourceOffPoleReturn F n c 0 x=_
  rw [zero_smul,add_zero]

theorem sourceUpperNumerator_limit (q : PhysicalResponsePoint) (n : PhysicalMomentum) (c : ℝ) (i : Fin 289) :
    Tendsto (fun eta=>sourceUpperNumerator q n c eta i) (𝓝 0) (𝓝 (sourceUpperNumerator q n c 0 i)) := by
  have limit:=(sourceBoundaryRegular_limit q.F n c).mul
    (tendsto_const_nhds (x:=sourceEqualProjection q.F (sourceFullInitialUpper q 0 0 i)))
  simpa only [sourceUpperNumerator,sourceBoundaryRegular_zero] using limit

theorem sourceBaseNumerator_limit (q : PhysicalResponsePoint) (n : PhysicalMomentum) (c : ℝ) (i : Fin 289) :
    Tendsto (fun eta=>sourceBaseNumerator q n c eta i) (𝓝 0) (𝓝 (sourceBaseNumerator q n c 0 i)) := by
  have upper:=sourceUpperNumerator_limit q n c i
  have retained:=(sourceRetainerReturn q.F).continuous.continuousAt.tendsto.comp upper
  have projected:=(sourceEqualProjection q.F).continuous.continuousAt.tendsto.comp retained
  have limit:=((sourceBoundaryRegular_limit q.F n c).mul projected).neg
  simpa only [Function.comp_def,sourceBaseNumerator,sourceBoundaryRegular_zero] using limit

theorem sourceGaugeNumerator_limit (q : PhysicalResponsePoint) (n : PhysicalMomentum) (c : ℝ)
    (mu : Fin 4) (a : Fin 12) :
    Tendsto (fun eta=>sourceGaugeNumerator q n c eta mu a) (𝓝 0) (𝓝 (sourceGaugeNumerator q n c 0 mu a)) := by
  have limit:=(sourceBoundaryRegular_limit q.F n c).mul
    (tendsto_const_nhds (x:=sourceEqualProjection q.F (sourceFullInitialBase q 0 0 (gaugeSlot mu a))))
  simpa only [sourceGaugeNumerator,sourceBoundaryRegular_zero] using limit

theorem sourceWholeCurrentNumerator_limit (q : PhysicalResponsePoint) (n : PhysicalMomentum) (c : ℝ)
    (l r : RestStateIndex) :
    Tendsto (fun eta=>sourceWholeCurrentNumerator q n c eta l r) (𝓝 0)
      (𝓝 (sourceWholeCurrentNumerator q n c 0 l r)) := by
  apply tendsto_pi_nhds.mpr
  intro i
  have limit:=((sourcePoleRead q.epsilon q.precision 0 0 l r).continuous.continuousAt.tendsto.comp
    (sourceBaseNumerator_limit q n c i)).neg
  simpa only [Function.comp_def,sourceWholeCurrentNumerator] using limit

theorem sourceGaugeCurrentNumerator_limit (q : PhysicalResponsePoint) (n : PhysicalMomentum) (c : ℝ)
    (l r : RestStateIndex) (mu : Fin 4) (a : Fin 12) :
    Tendsto (fun eta=>sourceGaugeCurrentNumerator q n c eta l r mu a) (𝓝 0)
      (𝓝 (sourceGaugeCurrentNumerator q n c 0 l r mu a)) := by
  have limit:=((sourcePoleRead q.epsilon q.precision 0 0 l r).continuous.continuousAt.tendsto.comp
    (sourceGaugeNumerator_limit q n c mu a)).neg
  simpa only [Function.comp_def,sourceGaugeCurrentNumerator] using limit

/-- The actual whole-current boundary coefficient is produced by the source resonant initial sectors. -/
theorem sourceWholeCurrent_boundary_residue (q : PhysicalResponsePoint) (n : PhysicalMomentum) (c : ℝ)
    (l r : RestStateIndex) :
    Tendsto (fun eta : ℝ=>((eta:ℂ)^2) • sourceFullCurrentResidue q n (sourcePoleSide c eta) l r)
      (𝓝[>] 0) (𝓝 (sourceWholeCurrentNumerator q n c 0 l r)) := by
  apply ((sourceWholeCurrentNumerator_limit q n c l r).mono_left nhdsWithin_le_nhds).congr'
  have positive : ∀ᶠ eta : ℝ in 𝓝[>] 0,0<eta := self_mem_nhdsWithin
  filter_upwards [positive] with eta pos
  exact (sourceWholeCurrentNumerator_generated q n c eta pos l r).symm

theorem sourceGaugeCurrent_boundary_residue (q : PhysicalResponsePoint) (n : PhysicalMomentum) (c : ℝ)
    (l r : RestStateIndex) (mu : Fin 4) (a : Fin 12) :
    Tendsto (fun eta : ℝ=>(eta:ℂ)*sourceGaugeCurrentResidue q n (sourcePoleSide c eta) l r mu a)
      (𝓝[>] 0) (𝓝 (sourceGaugeCurrentNumerator q n c 0 l r mu a)) := by
  apply ((sourceGaugeCurrentNumerator_limit q n c l r mu a).mono_left nhdsWithin_le_nhds).congr'
  have positive : ∀ᶠ eta : ℝ in 𝓝[>] 0,0<eta := self_mem_nhdsWithin
  filter_upwards [positive] with eta pos
  exact (sourceGaugeCurrentNumerator_generated q n c eta pos l r mu a).symm

end LowEnergy.PreparationVacuumObservedBoundaryResidue
