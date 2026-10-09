import H0mework.Versions.C62.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationSourceEffectiveCausalInverse

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
open PreparationVacuumPhysicalFeedback PreparationVacuumMixedFieldReturn Filter Set
open scoped Topology
attribute [local irreducible] sourceEqualProjection sourceOffProjection sourceSlowTransport sourceSlowReturn
  sourceSlowEffective sourceSlowForcing sourceSlowLeading sourceOffgapInverse sourcePinnedLeadingInverse
  sourceFullHalfBase sourceFullHalfUpper sourceFullInitialBase sourceFullInitialUpper sourceRetainerReturn

def sourceScaledUpper (q : PhysicalResponsePoint) (n : PhysicalMomentum) (zeta : ℂ) (i : Fin 289) (delta : ℝ) : SourceOp :=
  (delta:ℂ) • sourceEqualProjection q.F (sourceFullHalfUpper q (-(delta • n)) 0 i ((delta:ℂ)*zeta))

def sourceScaledBase (q : PhysicalResponsePoint) (n : PhysicalMomentum) (zeta : ℂ) (i : Fin 289) (delta : ℝ) : SourceOp :=
  ((delta:ℂ)^2) • sourceEqualProjection q.F (sourceFullHalfBase q (-(delta • n)) 0 i ((delta:ℂ)*zeta))

def sourceUpperResidue (q : PhysicalResponsePoint) (n : PhysicalMomentum) (zeta : ℂ) (i : Fin 289) : SourceOp :=
  sourceOriginInverse q.F n zeta (sourceEqualProjection q.F (sourceFullInitialUpper q 0 0 i))

def sourceBaseResidue (q : PhysicalResponsePoint) (n : PhysicalMomentum) (zeta : ℂ) (i : Fin 289) : SourceOp :=
  -sourceOriginInverse q.F n zeta (sourceEqualProjection q.F (sourceRetainerReturn q.F (sourceUpperResidue q n zeta i)))

private theorem controlled_limit {E : Type*} [NormedAddCommGroup E] (f : ℝ→E) (a : E)
    (C radius : ℝ) (positive : 0<radius)
    (bound : ∀d,abs d≤radius→‖f d-a‖≤C*abs d) : Tendsto f (𝓝 0) (𝓝 a) := by
  have near : ∀ᶠ d : ℝ in 𝓝 0,abs d<radius :=
    continuous_abs.continuousAt.eventually_lt_const (by simpa only [abs_zero] using positive)
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall (fun d=>norm_nonneg (f d-a)))
    (near.mono (fun d h=>bound d h.le))
  simpa only [abs_zero,mul_zero] using (tendsto_const_nhds.mul (continuous_abs.tendsto (0 : ℝ)))

theorem sourceEffectiveInverse_limit (F : GaussUnitaryHistory.Index) (n : PhysicalMomentum) (zeta : ℂ)
    (positive : 0<zeta.re) :
    Tendsto (sourceEffectiveInverse F n zeta) (𝓝 0) (𝓝 (sourceOriginInverse F n zeta)) :=
  controlled_limit (E:=SourceSuperOp) (sourceEffectiveInverse F n zeta) (sourceOriginInverse F n zeta)
    (2*‖sourceOriginInverse F n zeta‖^2*sourceEffectiveErrorBudget F n zeta) (sourceResidueRadius F n zeta)
    (sourceResidueRadius_positive F n zeta) (fun d small=>sourceEffectiveInverse_error F n zeta positive d small)

theorem sourceSlowReturn_limit (F : GaussUnitaryHistory.Index) (n : PhysicalMomentum) (zeta : ℂ) :
    Tendsto (sourceSlowReturn F n zeta) (𝓝 0) (𝓝 (1 : SourceSuperOp)) := by
  apply controlled_limit (E:=SourceSuperOp) (sourceSlowReturn F n zeta) (1 : SourceSuperOp)
    (2*‖sourceOffgapInverse F‖*‖sourceSlowTransport F n zeta‖)
    (sourceSlowRadius F n zeta) (sourceSlowRadius_positive F n zeta)
  intro d small
  exact (sourceSlowReturn_error F n zeta d small).trans_eq (by ring)

theorem sourceSlowForcing_limit (F : GaussUnitaryHistory.Index) (n : PhysicalMomentum) (zeta : ℂ) :
    Tendsto (sourceSlowForcing F n zeta) (𝓝 0) (𝓝 (sourceEqualProjection F)) := by
  apply controlled_limit (E:=SourceSuperOp) (sourceSlowForcing F n zeta) (sourceEqualProjection F)
    (‖sourceEqualProjection F‖*‖sourceSlowTransport F n zeta‖*2*‖sourceOffgapInverse F‖)
    (sourceSlowRadius F n zeta) (sourceSlowRadius_positive F n zeta)
  intro d small
  exact (sourceSlowForcing_error F n zeta d small).trans_eq (by ring)

theorem sourceResidue_eventually (F : GaussUnitaryHistory.Index) (n : PhysicalMomentum) (zeta : ℂ) :
    ∀ᶠ d : ℝ in 𝓝[>] 0,0<d∧abs d ≤ sourceResidueRadius F n zeta := by
  have near : ∀ᶠ d : ℝ in 𝓝 0,d<sourceResidueRadius F n zeta :=
    continuous_id.continuousAt.eventually_lt_const (sourceResidueRadius_positive F n zeta)
  filter_upwards [self_mem_nhdsWithin,near.filter_mono nhdsWithin_le_nhds] with d positive small
  exact ⟨positive,by rw [abs_of_pos positive];exact small.le⟩

private theorem op_smul_zero (d : ℂ) : d • (0 : SourceOp)=0 := by
  apply ContinuousLinearMap.ext
  intro x
  exact smul_zero d

private theorem op_zero_smul (X : SourceOp) : (0 : ℂ) • X=0 := by
  apply ContinuousLinearMap.ext
  intro x
  exact zero_smul ℂ (X x)

private theorem solve_projected (F : GaussUnitaryHistory.Index) (n : PhysicalMomentum) (zeta : ℂ)
    (positive : 0<zeta.re) (delta : ℝ) (small : abs delta ≤ sourceResidueRadius F n zeta)
    (d : ℂ) (X B : SourceOp)
    (equation : sourceSlowEffective F n zeta delta (d • sourceEqualProjection F X)=B) :
    d • sourceEqualProjection F X=sourceEffectiveInverse F n zeta delta B := by
  have fixed:=congrArg (fun T : SourceSuperOp=>T X) (sourceEqualProjection_idempotent F)
  change sourceEqualProjection F (sourceEqualProjection F X)=sourceEqualProjection F X at fixed
  have off : sourceOffProjection F (d • sourceEqualProjection F X)=0 := by
    simp only [sourceOffProjection,sub_apply,one_apply_eq_self,map_smul,fixed,sub_self,op_smul_zero]
  have complete : sourceCompletePencil F n zeta delta (d • sourceEqualProjection F X)=B := by
    rw [sourceCompletePencil,add_apply,off,add_zero]
    exact equation
  have returned:=congrArg (sourceEffectiveInverse F n zeta delta) complete
  have cancel:=congrArg (fun T : SourceSuperOp=>T (d • sourceEqualProjection F X))
    (sourceEffectiveInverse_left F n zeta positive delta small)
  change sourceEffectiveInverse F n zeta delta
    (sourceCompletePencil F n zeta delta (d • sourceEqualProjection F X))=d • sourceEqualProjection F X at cancel
  rw [cancel] at returned
  exact returned

theorem sourceScaledUpper_solved (q : PhysicalResponsePoint) (n : PhysicalMomentum) (zeta : ℂ)
    (positive : 0<zeta.re) (delta : ℝ) (positiveDelta : 0<delta) (i : Fin 289)
    (small : abs delta ≤ sourceResidueRadius q.F n zeta) :
    sourceScaledUpper q n zeta i delta=sourceEffectiveInverse q.F n zeta delta
      (sourceSlowForcing q.F n zeta delta (sourceFullInitialUpper q (-(delta • n)) 0 i)) :=
  solve_projected q.F n zeta positive delta small _ _ _
    (sourceActualSlow_effective q n delta positiveDelta zeta positive i
      (small.trans (sourceResidueRadius_slow q.F n zeta))).1

theorem sourceScaledBase_solved (q : PhysicalResponsePoint) (n : PhysicalMomentum) (zeta : ℂ)
    (positive : 0<zeta.re) (delta : ℝ) (positiveDelta : 0<delta) (i : Fin 289)
    (small : abs delta ≤ sourceResidueRadius q.F n zeta) :
    sourceScaledBase q n zeta i delta=sourceEffectiveInverse q.F n zeta delta
      ((delta:ℂ) • sourceSlowForcing q.F n zeta delta (sourceFullInitialBase q (-(delta • n)) 0 i)-
        sourceSlowForcing q.F n zeta delta (sourceRetainerReturn q.F
          (sourceSlowReturn q.F n zeta delta (sourceScaledUpper q n zeta i delta+
            (delta:ℂ) • sourceOffgapInverse q.F (sourceFullInitialUpper q (-(delta • n)) 0 i))))) :=
  solve_projected q.F n zeta positive delta small _ _ _
    (sourceActualSlow_triangular q n delta positiveDelta zeta positive i
      (small.trans (sourceResidueRadius_slow q.F n zeta)))

private theorem apply_limit {E J : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup J] [NormedSpace ℂ J] {l : Filter ℝ}
    {A : ℝ→E→L[ℂ] J} {x : ℝ→E} {a : E→L[ℂ] J} {y : E}
    (operator : Tendsto A l (𝓝 a)) (vector : Tendsto x l (𝓝 y)) :
    Tendsto (fun d=>A d (x d)) l (𝓝 (a y)) := by
  have continuous : Continuous (fun p : (E→L[ℂ] J)×E=>p.1 p.2) := continuous_fst.clm_apply continuous_snd
  exact (continuous.tendsto (a,y)).comp (operator.prodMk_nhds vector)

theorem sourceScaledUpper_limit (q : PhysicalResponsePoint) (n : PhysicalMomentum) (zeta : ℂ)
    (positive : 0<zeta.re) (i : Fin 289) (nonrealL : q.z.im≠0) (nonrealR : q.w.im≠0) :
    Tendsto (sourceScaledUpper q n zeta i) (𝓝[>] 0) (𝓝 (sourceUpperResidue q n zeta i)) := by
  have limit:=apply_limit (sourceEffectiveInverse_limit q.F n zeta positive)
    (apply_limit (sourceSlowForcing_limit q.F n zeta)
      (sourceActualInitial_slow_limit q n i nonrealL nonrealR).2)
  apply (limit.mono_left (nhdsWithin_le_nhds : 𝓝[>] (0:ℝ)≤𝓝 0)).congr'
  filter_upwards [sourceResidue_eventually q.F n zeta] with d legal
  exact (sourceScaledUpper_solved q n zeta positive d legal.1 i legal.2).symm

theorem sourceScaledBase_limit (q : PhysicalResponsePoint) (n : PhysicalMomentum) (zeta : ℂ)
    (positive : 0<zeta.re) (i : Fin 289) (nonrealL : q.z.im≠0) (nonrealR : q.w.im≠0) :
    Tendsto (sourceScaledBase q n zeta i) (𝓝[>] 0) (𝓝 (sourceBaseResidue q n zeta i)) := by
  have scalar : Tendsto (fun d : ℝ=>(d:ℂ)) (𝓝[>] 0) (𝓝 0) :=
    (Complex.continuous_ofReal.tendsto 0).mono_left nhdsWithin_le_nhds
  have inverse:=(sourceEffectiveInverse_limit q.F n zeta positive).mono_left
    (nhdsWithin_le_nhds : 𝓝[>] (0:ℝ)≤𝓝 0)
  have forcing:=(sourceSlowForcing_limit q.F n zeta).mono_left
    (nhdsWithin_le_nhds : 𝓝[>] (0:ℝ)≤𝓝 0)
  have returned:=(sourceSlowReturn_limit q.F n zeta).mono_left
    (nhdsWithin_le_nhds : 𝓝[>] (0:ℝ)≤𝓝 0)
  have initial:=sourceActualInitial_slow_limit q n i nonrealL nonrealR
  have baseInitial:=initial.1.mono_left (nhdsWithin_le_nhds : 𝓝[>] (0:ℝ)≤𝓝 0)
  have upperInitial:=initial.2.mono_left (nhdsWithin_le_nhds : 𝓝[>] (0:ℝ)≤𝓝 0)
  have upper:=sourceScaledUpper_limit q n zeta positive i nonrealL nonrealR
  have gap : Tendsto (fun _ : ℝ=>sourceOffgapInverse q.F) (𝓝[>] 0) (𝓝 (sourceOffgapInverse q.F)) := tendsto_const_nhds
  have retainer : Tendsto (fun _ : ℝ=>sourceRetainerReturn q.F) (𝓝[>] 0) (𝓝 (sourceRetainerReturn q.F)) := tendsto_const_nhds
  have upperCorrection:=scalar.smul (apply_limit gap upperInitial)
  have nativeReturn:=apply_limit returned (upper.add upperCorrection)
  have coupling:=apply_limit forcing (apply_limit retainer nativeReturn)
  have baseTerm:=scalar.smul (apply_limit forcing baseInitial)
  have limit:=apply_limit inverse (baseTerm.sub coupling)
  have normalized : Tendsto (fun d : ℝ=>sourceEffectiveInverse q.F n zeta d
      ((d:ℂ) • sourceSlowForcing q.F n zeta d (sourceFullInitialBase q (-(d • n)) 0 i)-
        sourceSlowForcing q.F n zeta d (sourceRetainerReturn q.F
          (sourceSlowReturn q.F n zeta d (sourceScaledUpper q n zeta i d+
            (d:ℂ) • sourceOffgapInverse q.F (sourceFullInitialUpper q (-(d • n)) 0 i))))))
      (𝓝[>] 0) (𝓝 (sourceBaseResidue q n zeta i)) := by
    simpa only [op_zero_smul,add_zero,one_apply_eq_self,zero_sub,map_neg,sourceBaseResidue] using limit
  apply normalized.congr'
  filter_upwards [sourceResidue_eventually q.F n zeta] with d legal
  exact (sourceScaledBase_solved q n zeta positive d legal.1 i legal.2).symm

def sourceScaledGauge (q : PhysicalResponsePoint) (n : PhysicalMomentum) (zeta : ℂ)
    (mu : Fin 4) (a : Fin 12) (delta : ℝ) : SourceOp :=
  (delta:ℂ) • sourceEqualProjection q.F
    (sourceFullHalfBase q (-(delta • n)) 0 (gaugeSlot mu a) ((delta:ℂ)*zeta))

def sourceGaugeResidue (q : PhysicalResponsePoint) (n : PhysicalMomentum) (zeta : ℂ)
    (mu : Fin 4) (a : Fin 12) : SourceOp :=
  sourceOriginInverse q.F n zeta (sourceEqualProjection q.F (sourceFullInitialBase q 0 0 (gaugeSlot mu a)))

/-- The first-order gauge response is generated by the actual zero upper sector. -/
theorem sourceScaledGauge_solved (q : PhysicalResponsePoint) (n : PhysicalMomentum) (zeta : ℂ)
    (positive : 0<zeta.re) (delta : ℝ) (positiveDelta : 0<delta) (mu : Fin 4) (a : Fin 12)
    (small : abs delta ≤ sourceResidueRadius q.F n zeta) (nonrealL : q.z.im≠0) (nonrealR : q.w.im≠0) :
    sourceScaledGauge q n zeta mu a delta=sourceEffectiveInverse q.F n zeta delta
      (sourceSlowForcing q.F n zeta delta (sourceFullInitialBase q (-(delta • n)) 0 (gaugeSlot mu a))) := by
  have positiveLambda : 0<((delta:ℂ)*zeta).re := by
    simpa only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero] using mul_pos positiveDelta positive
  have upper:=sourceFullHalfUpper_gauge_zero q (-(delta • n)) 0 mu a ((delta:ℂ)*zeta) positiveLambda nonrealL nonrealR
  have equation:=(sourceActualSlow_effective q n delta positiveDelta zeta positive (gaugeSlot mu a)
    (small.trans (sourceResidueRadius_slow q.F n zeta))).2
  rw [upper,map_zero,sub_zero] at equation
  exact solve_projected q.F n zeta positive delta small _ _ _ equation

theorem sourceScaledGauge_limit (q : PhysicalResponsePoint) (n : PhysicalMomentum) (zeta : ℂ)
    (positive : 0<zeta.re) (mu : Fin 4) (a : Fin 12) (nonrealL : q.z.im≠0) (nonrealR : q.w.im≠0) :
    Tendsto (sourceScaledGauge q n zeta mu a) (𝓝[>] 0) (𝓝 (sourceGaugeResidue q n zeta mu a)) := by
  have limit:=apply_limit (sourceEffectiveInverse_limit q.F n zeta positive)
    (apply_limit (sourceSlowForcing_limit q.F n zeta)
      (sourceActualInitial_slow_limit q n (gaugeSlot mu a) nonrealL nonrealR).1)
  apply (limit.mono_left (nhdsWithin_le_nhds : 𝓝[>] (0:ℝ)≤𝓝 0)).congr'
  filter_upwards [sourceResidue_eventually q.F n zeta] with d legal
  exact (sourceScaledGauge_solved q n zeta positive d legal.1 mu a legal.2 nonrealL nonrealR).symm

end LowEnergy.PreparationVacuumQuantumSlowResidue
