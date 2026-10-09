import H0mework.Versions.Rc015842c.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationSourceActualSlowResidues

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumQuantumSlowResidue
open GaussCoreHilbert CanonicalGradedSpatialSource PreparationVacuumPhysicalHalfAxis
open PreparationVacuumPhysicalSlowBlock PreparationVacuumPhysicalPinnedVelocity
open PreparationVacuumQuantumSlowResponse PreparationVacuumGaugeSlowFrequency
open PreparationVacuumPhysicalFeedback PreparationVacuumMixedFieldReturn
open PreparationVacuumElectromagneticIdentity PreparationVacuumSharedPoleCarrier PreparationVacuumMovingPoleGaussReturn
open PreparationVacuumPhysicalPoleHalfResponse PreparationVacuumCausalPoleResponse
open PreparationVacuumOriginalGreenFeedback PreparationVacuumSourceFieldFamily PreparationVacuumFieldConstraintResponse Filter Set
open scoped Topology Matrix
attribute [local irreducible] sourceEqualProjection sourceOffProjection sourceSlowTransport sourceSlowReturn
  sourceSlowEffective sourceSlowForcing sourceSlowLeading sourceOffgapInverse sourcePinnedLeadingInverse
  sourceFullHalfBase sourceFullHalfUpper sourceFullInitialBase sourceFullInitialUpper sourceRetainerReturn
  sourcePoleRead

private theorem apply_limit {l : Filter ℝ} {A : ℝ→SourceSuperOp} {x : ℝ→SourceOp}
    {a : SourceSuperOp} {y : SourceOp} (operator : Tendsto A l (𝓝 a)) (vector : Tendsto x l (𝓝 y)) :
    Tendsto (fun d=>A d (x d)) l (𝓝 (a y)) := by
  have continuous : Continuous (fun p : SourceSuperOp×SourceOp=>p.1 p.2) := continuous_fst.clm_apply continuous_snd
  exact (continuous.tendsto (a,y)).comp (operator.prodMk_nhds vector)

private theorem op_zero_smul (X : SourceOp) : (0 : ℂ) • X=0 := by
  apply ContinuousLinearMap.ext
  intro x
  exact zero_smul ℂ (X x)

/-- The full original N1 response has its source-generated second-order residue. -/
theorem sourceFullHalfBase_residue (q : PhysicalResponsePoint) (n : PhysicalMomentum) (zeta : ℂ)
    (positive : 0<zeta.re) (i : Fin 289) (nonrealL : q.z.im≠0) (nonrealR : q.w.im≠0) :
    Tendsto (fun d : ℝ=>((d:ℂ)^2) • sourceFullHalfBase q (-(d • n)) 0 i ((d:ℂ)*zeta))
      (𝓝[>] 0) (𝓝 (sourceBaseResidue q n zeta i)) := by
  have scalar : Tendsto (fun d : ℝ=>(d:ℂ)) (𝓝[>] 0) (𝓝 0) :=
    (Complex.continuous_ofReal.tendsto 0).mono_left nhdsWithin_le_nhds
  have squared:=scalar.pow 2
  have returned:=(sourceSlowReturn_limit q.F n zeta).mono_left
    (nhdsWithin_le_nhds : 𝓝[>] (0:ℝ)≤𝓝 0)
  have initial:=sourceActualInitial_slow_limit q n i nonrealL nonrealR
  have baseInitial:=initial.1.mono_left (nhdsWithin_le_nhds : 𝓝[>] (0:ℝ)≤𝓝 0)
  have upperInitial:=initial.2.mono_left (nhdsWithin_le_nhds : 𝓝[>] (0:ℝ)≤𝓝 0)
  have gap : Tendsto (fun _ : ℝ=>sourceOffgapInverse q.F) (𝓝[>] 0) (𝓝 (sourceOffgapInverse q.F)) := tendsto_const_nhds
  have retainer : Tendsto (fun _ : ℝ=>sourceRetainerReturn q.F) (𝓝[>] 0) (𝓝 (sourceRetainerReturn q.F)) := tendsto_const_nhds
  have upper:=sourceScaledUpper_limit q n zeta positive i nonrealL nonrealR
  have base:=sourceScaledBase_limit q n zeta positive i nonrealL nonrealR
  have upperReturn:=apply_limit returned (upper.add (scalar.smul (apply_limit gap upperInitial)))
  have correction:=scalar.smul (apply_limit gap (apply_limit retainer upperReturn))
  have limit:=apply_limit returned ((base.add (squared.smul (apply_limit gap baseInitial))).sub correction)
  have normalized : Tendsto (fun d : ℝ=>sourceSlowReturn q.F n zeta d
      (sourceScaledBase q n zeta i d+((d:ℂ)^2) • sourceOffgapInverse q.F (sourceFullInitialBase q (-(d • n)) 0 i)-
        (d:ℂ) • sourceOffgapInverse q.F (sourceRetainerReturn q.F
          (sourceSlowReturn q.F n zeta d (sourceScaledUpper q n zeta i d+
            (d:ℂ) • sourceOffgapInverse q.F (sourceFullInitialUpper q (-(d • n)) 0 i))))))
      (𝓝[>] 0) (𝓝 (sourceBaseResidue q n zeta i)) := by
    simpa only [zero_pow (by decide : (2 : ℕ)≠0),op_zero_smul,add_zero,sub_zero,one_apply_eq_self] using limit
  apply normalized.congr'
  filter_upwards [sourceResidue_eventually q.F n zeta] with d legal
  exact (sourceActualSlow_normalized_return q n d legal.1 zeta positive i
    (legal.2.trans (sourceResidueRadius_slow q.F n zeta))).symm

private theorem gauge_normalized_return (q : PhysicalResponsePoint) (n : PhysicalMomentum) (zeta : ℂ)
    (positive : 0<zeta.re) (d : ℝ) (positiveDelta : 0<d) (mu : Fin 4) (a : Fin 12)
    (small : abs d ≤ sourceResidueRadius q.F n zeta) (nonrealL : q.z.im≠0) (nonrealR : q.w.im≠0) :
    (d:ℂ) • sourceFullHalfBase q (-(d • n)) 0 (gaugeSlot mu a) ((d:ℂ)*zeta)=
      sourceSlowReturn q.F n zeta d (sourceScaledGauge q n zeta mu a d+
        (d:ℂ) • sourceOffgapInverse q.F (sourceFullInitialBase q (-(d • n)) 0 (gaugeSlot mu a))) := by
  have positiveLambda : 0<((d:ℂ)*zeta).re := by
    simpa only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero] using mul_pos positiveDelta positive
  have upper:=sourceFullHalfUpper_gauge_zero q (-(d • n)) 0 mu a ((d:ℂ)*zeta) positiveLambda nonrealL nonrealR
  have base:=sourceActualBase_return q n d positiveDelta zeta positive (gaugeSlot mu a)
    (small.trans (sourceResidueRadius_slow q.F n zeta))
  simp only [upper,map_zero,sub_zero] at base
  simpa only [map_add,map_smul,smul_add,sourceScaledGauge] using congrArg (fun X : SourceOp=>(d:ℂ) • X) base

/-- Each of the original 48 gauge readers retains its first-order causal response. -/
theorem sourceGaugeHalfBase_residue (q : PhysicalResponsePoint) (n : PhysicalMomentum) (zeta : ℂ)
    (positive : 0<zeta.re) (mu : Fin 4) (a : Fin 12) (nonrealL : q.z.im≠0) (nonrealR : q.w.im≠0) :
    Tendsto (fun d : ℝ=>(d:ℂ) • sourceFullHalfBase q (-(d • n)) 0 (gaugeSlot mu a) ((d:ℂ)*zeta))
      (𝓝[>] 0) (𝓝 (sourceGaugeResidue q n zeta mu a)) := by
  have scalar : Tendsto (fun d : ℝ=>(d:ℂ)) (𝓝[>] 0) (𝓝 0) :=
    (Complex.continuous_ofReal.tendsto 0).mono_left nhdsWithin_le_nhds
  have returned:=(sourceSlowReturn_limit q.F n zeta).mono_left
    (nhdsWithin_le_nhds : 𝓝[>] (0:ℝ)≤𝓝 0)
  have initial:=(sourceActualInitial_slow_limit q n (gaugeSlot mu a) nonrealL nonrealR).1.mono_left
    (nhdsWithin_le_nhds : 𝓝[>] (0:ℝ)≤𝓝 0)
  have gap : Tendsto (fun _ : ℝ=>sourceOffgapInverse q.F) (𝓝[>] 0) (𝓝 (sourceOffgapInverse q.F)) := tendsto_const_nhds
  have response:=sourceScaledGauge_limit q n zeta positive mu a nonrealL nonrealR
  have limit:=apply_limit returned (response.add (scalar.smul (apply_limit gap initial)))
  have normalized : Tendsto (fun d : ℝ=>sourceSlowReturn q.F n zeta d (sourceScaledGauge q n zeta mu a d+
      (d:ℂ) • sourceOffgapInverse q.F (sourceFullInitialBase q (-(d • n)) 0 (gaugeSlot mu a))))
      (𝓝[>] 0) (𝓝 (sourceGaugeResidue q n zeta mu a)) := by
    simpa only [op_zero_smul,add_zero,one_apply_eq_self] using limit
  apply normalized.congr'
  filter_upwards [sourceResidue_eventually q.F n zeta] with d legal
  exact (gauge_normalized_return q n zeta positive d legal.1 mu a legal.2 nonrealL nonrealR).symm

private theorem returnedHalf_read (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum) (l r : RestStateIndex)
    (lambda : ℂ) (positive : 0<lambda.re) (i : Fin 289) :
    returnedHalfCurrent q pL pR l r lambda i=
      -sourcePoleRead q.epsilon q.precision 0 0 l r (sourceFullHalfBase q pL pR i lambda) := by
  have source:=congrArg (fun M : Matrix RestStateIndex RestStateIndex ℂ=>M l r)
    (sourceFullHalf_common_carrier q pL pR i lambda positive)
  simpa only [returnedHalfCurrent,Matrix.neg_apply,sourceTensor] using source

def sourceFullCurrentResidue (q : PhysicalResponsePoint) (n : PhysicalMomentum) (zeta : ℂ)
    (l r : RestStateIndex) : Fin 289→ℂ := fun i=>
  -sourcePoleRead q.epsilon q.precision 0 0 l r (sourceBaseResidue q n zeta i)

def sourceGaugeCurrentResidue (q : PhysicalResponsePoint) (n : PhysicalMomentum) (zeta : ℂ)
    (l r : RestStateIndex) (mu : Fin 4) (a : Fin 12) : ℂ :=
  -sourcePoleRead q.epsilon q.precision 0 0 l r (sourceGaugeResidue q n zeta mu a)

/-- The complete actual current residue is read on the same common eight-state carrier. -/
theorem sourceFullCurrent_residue (q : PhysicalResponsePoint) (n : PhysicalMomentum) (zeta : ℂ)
    (positive : 0<zeta.re) (l r : RestStateIndex) (nonrealL : q.z.im≠0) (nonrealR : q.w.im≠0) :
    Tendsto (fun d : ℝ=>((d:ℂ)^2) • returnedHalfCurrent q (-(d • n)) 0 l r ((d:ℂ)*zeta))
      (𝓝[>] 0) (𝓝 (sourceFullCurrentResidue q n zeta l r)) := by
  apply tendsto_pi_nhds.mpr
  intro i
  have limit:=((sourcePoleRead q.epsilon q.precision 0 0 l r).continuous.tendsto _ |>.comp
    (sourceFullHalfBase_residue q n zeta positive i nonrealL nonrealR)).neg
  apply limit.congr'
  filter_upwards [self_mem_nhdsWithin] with d positiveDelta
  have positiveLambda : 0<((d:ℂ)*zeta).re := by
    simpa only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero] using mul_pos positiveDelta positive
  simp only [Pi.smul_apply,Function.comp_def]
  rw [returnedHalf_read q _ _ l r _ positiveLambda i,map_smul]
  simp only [smul_neg]

/-- Source-pinned recoil remains in each gauge charge/current response. -/
theorem sourceGaugeCurrent_residue (q : PhysicalResponsePoint) (n : PhysicalMomentum) (zeta : ℂ)
    (positive : 0<zeta.re) (l r : RestStateIndex) (mu : Fin 4) (a : Fin 12)
    (nonrealL : q.z.im≠0) (nonrealR : q.w.im≠0) :
    Tendsto (fun d : ℝ=>(d:ℂ) • returnedHalfCurrent q (-(d • n)) 0 l r ((d:ℂ)*zeta) (gaugeSlot mu a))
      (𝓝[>] 0) (𝓝 (sourceGaugeCurrentResidue q n zeta l r mu a)) := by
  have limit:=((sourcePoleRead q.epsilon q.precision 0 0 l r).continuous.tendsto _ |>.comp
    (sourceGaugeHalfBase_residue q n zeta positive mu a nonrealL nonrealR)).neg
  apply limit.congr'
  filter_upwards [self_mem_nhdsWithin] with d positiveDelta
  have positiveLambda : 0<((d:ℂ)*zeta).re := by
    simpa only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero] using mul_pos positiveDelta positive
  simp only [Function.comp_def]
  rw [returnedHalf_read q _ _ l r _ positiveLambda (gaugeSlot mu a),map_smul]
  simp only [smul_neg]

private theorem sourceMatrix_continuous (terms : List SourceTerm) : Continuous (sourceMatrix terms) := by
  induction terms with
  | nil=>exact continuous_const
  | cons a rest ih=>
    have term : Continuous a.matrix := by
      apply continuous_matrix
      intro i j
      simp only [SourceTerm.matrix,Matrix.single_apply]
      split_ifs
      · unfold Powers.value;fun_prop
      · exact continuous_const
    exact term.add ih

private theorem readback_continuous : Continuous originalReadback := by
  unfold originalReadback originalChange
  exact ((sourceMatrix_continuous originalChangeTerms).comp continuous_neg).matrix_transpose

private theorem sourceRay_readback_limit (n : PhysicalMomentum) (zeta : ℂ) :
    Tendsto (fun d : ℝ=>originalReadback (fixedMomentum (d • n) ((d:ℂ)*zeta)))
      (𝓝[>] 0) (𝓝 (originalReadback 0)) := by
  have point : Continuous (fun d : ℝ=>fixedMomentum (d • n) ((d:ℂ)*zeta)) := by
    apply continuous_pi
    intro i
    refine Fin.cases ?_ (fun j=>?_) i
    · change Continuous (fun d : ℝ=>(d:ℂ)*zeta)
      fun_prop
    · change Continuous (fun d : ℝ=>Complex.I*((d*n j : ℝ):ℂ))
      fun_prop
  have origin : fixedMomentum ((0:ℝ) • n) (((0:ℝ):ℂ)*zeta)=0 := by
    ext i
    refine Fin.cases ?_ (fun j=>?_) i
    · simp [fixedMomentum,fullMomentum]
    · simp [fixedMomentum,fullMomentum,PreparationVacuumPhysicalFeedback.physicalSpatial]
  have momentum:=(point.tendsto 0).mono_left (nhdsWithin_le_nhds : 𝓝[>] (0:ℝ)≤𝓝 0)
  rw [origin] at momentum
  exact readback_continuous.continuousAt.tendsto.comp momentum

/-- All original nine compatibility rows retain their actual full-current residue. -/
theorem sourceFullNull_residue (q : PhysicalResponsePoint) (n : PhysicalMomentum) (zeta : ℂ)
    (positive : 0<zeta.re) (l r : RestStateIndex) (nonrealL : q.z.im≠0) (nonrealR : q.w.im≠0) :
    Tendsto (fun d : ℝ=>((d:ℂ)^2) • (nullProjection*ᵥ
      (originalReadback (fixedMomentum (d • n) ((d:ℂ)*zeta))*ᵥ
        returnedHalfCurrent q (-(d • n)) 0 l r ((d:ℂ)*zeta))))
      (𝓝[>] 0) (𝓝 (nullProjection*ᵥ(originalReadback 0*ᵥsourceFullCurrentResidue q n zeta l r))) := by
  have read:=sourceRay_readback_limit n zeta
  have current:=sourceFullCurrent_residue q n zeta positive l r nonrealL nonrealR
  have product:=(continuous_fst.matrix_mulVec continuous_snd).continuousAt.tendsto.comp
    (read.prodMk_nhds current)
  have projection : Continuous (fun v : Fin 289→ℂ=>nullProjection*ᵥv) := continuous_const.matrix_mulVec continuous_id
  have result:=projection.continuousAt.tendsto.comp product
  simpa only [Function.comp_def,Matrix.mulVec_smul] using result

end LowEnergy.PreparationVacuumQuantumSlowResidue
