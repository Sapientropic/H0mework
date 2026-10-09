import H0mework.Versions.R9c73a630.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationSourceActualSlowSchur

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumQuantumSlowResponse
open PreparationVacuumElectromagneticIdentity
open GaussCoreHilbert PreparationVacuumPhysicalSlowBlock PreparationVacuumSharedPoleCarrier
open PreparationVacuumGaugeSlowFrequency PreparationVacuumPhysicalFeedback
open PreparationVacuumPhysicalPoleHalfResponse CanonicalGradedSpatialSource CanonicalGradedCurrent
open PreparationVacuumPhysicalHalfAxis PreparationVacuumMovingPoleGaussReturn PreparationVacuumCausalPoleResponse
open PreparationVacuumOriginalGreenFeedback SourcePropagationNativeActionHessian
open PreparationVacuumFullPoleContinuation PreparationVacuumPhysicalPoleLegDynamics
open PreparationVacuumPropagationPencil PreparationVacuumActionFieldLift
open PreparationVacuumJointFieldResponse PreparationVacuumRawJointFeedback
open PreparationVacuumPhysicalNumberOneRead Filter
open PreparationVacuumPhysicalHalfAxis
open scoped Topology Matrix
attribute [local irreducible] actualC actualA sourceVelocityLinear sourceOffgapInverse
  sourceEqualProjection sourceOffProjection sourceStaticLiouvillian sourceSlowReturn sourceSlowTransport
  sourceFullHalfBase sourceFullHalfUpper sourceFullInitialBase sourceFullInitialUpper sourceProjection
  sourcePoleRead sourceSlowEffective sourceSlowForcing sourceRetainerReturn

def sourceSlowLeading (F : GaussUnitaryHistory.Index) (n : PhysicalMomentum) (zeta : ℂ) : SourceSuperOp :=
  sourceEqualProjection F*sourceSlowTransport F n zeta*sourceEqualProjection F

private theorem effective_factor {R : Type*} [Ring R] (P T W : R) :
    P*T*W*P-P*T*P=(P*T)*(W-1)*P := by noncomm_ring

/-- The complete effective operator has a source-controlled leading tensor. -/
theorem sourceSlowEffective_error (F : GaussUnitaryHistory.Index) (n : PhysicalMomentum) (zeta : ℂ) (delta : ℝ)
    (small : (abs delta) ≤ sourceSlowRadius F n zeta) :
    ‖sourceSlowEffective F n zeta delta-sourceSlowLeading F n zeta‖≤
      ‖sourceEqualProjection F‖*‖sourceSlowTransport F n zeta‖*
      (2*(abs delta)*‖sourceOffgapInverse F‖*‖sourceSlowTransport F n zeta‖)*‖sourceEqualProjection F‖ := by
  have identity : sourceSlowEffective F n zeta delta-sourceSlowLeading F n zeta=
      (sourceEqualProjection F*sourceSlowTransport F n zeta)*
        (sourceSlowReturn F n zeta delta-1)*sourceEqualProjection F := by
    unfold sourceSlowEffective sourceSlowLeading
    exact effective_factor (sourceEqualProjection F) (sourceSlowTransport F n zeta) (sourceSlowReturn F n zeta delta)
  rw [identity]
  calc
    _≤(‖sourceEqualProjection F*sourceSlowTransport F n zeta‖*
        ‖sourceSlowReturn F n zeta delta-1‖)*‖sourceEqualProjection F‖ :=
      (ContinuousLinearMap.opNorm_comp_le _ _).trans (mul_le_mul_of_nonneg_right (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _))
    _≤_ := by
      gcongr
      · exact ContinuousLinearMap.opNorm_comp_le _ _
      · exact sourceSlowReturn_error F n zeta delta small

private theorem forcing_price {R : Type*} [NormedRing R] [NormedAlgebra ℂ R]
    (P T W G : R) (d : ℂ) (bound : ‖W‖≤2) :
    ‖P-d • (P*T*W*G)-P‖≤‖d‖*(‖P‖*‖T‖*2*‖G‖) := by
  have identity : P-d • (P*T*W*G)-P= -(d • (P*T*W*G)) := by abel
  rw [identity,norm_neg,norm_smul]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg d)
  calc
    _≤(‖P*T‖*‖W‖)*‖G‖ := (norm_mul_le _ _).trans
      (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg G))
    _≤_ := by
      gcongr
      exact norm_mul_le P T

theorem sourceSlowForcing_error (F : GaussUnitaryHistory.Index) (n : PhysicalMomentum) (zeta : ℂ) (delta : ℝ)
    (small : (abs delta) ≤ sourceSlowRadius F n zeta) :
    ‖sourceSlowForcing F n zeta delta-sourceEqualProjection F‖≤
      (abs delta)*(‖sourceEqualProjection F‖*‖sourceSlowTransport F n zeta‖*2*‖sourceOffgapInverse F‖) := by
  have price:=forcing_price (R:=SourceSuperOp) (sourceEqualProjection F) (sourceSlowTransport F n zeta)
    (sourceSlowReturn F n zeta delta) (sourceOffgapInverse F) (delta:ℂ) (sourceSlowReturn_price F n zeta delta small)
  simpa only [sourceSlowForcing,Complex.norm_real,Real.norm_eq_abs] using price

/-- Both original material-leg initial operators vary on the same actual momentum carrier. -/
theorem sourceActualInitial_continuous (q : PhysicalResponsePoint) (i : Fin 289)
    (nonrealL : q.z.im≠0) (nonrealR : q.w.im≠0) :
    Continuous (fun p : PhysicalMomentum×PhysicalMomentum=>sourceFullInitialBase q p.1 p.2 i) ∧
    Continuous (fun p : PhysicalMomentum×PhysicalMomentum=>sourceFullInitialUpper q p.1 p.2 i) := by
  have leftR:=(actualJointResolvent_continuous q.F q.z nonrealL).comp
    (continuous_fst : Continuous (fun p : PhysicalMomentum×PhysicalMomentum=>p.1))
  have rightR:=(actualJointResolvent_continuous q.F q.w nonrealR).comp
    (continuous_snd : Continuous (fun p : PhysicalMomentum×PhysicalMomentum=>p.2))
  have reader:=(rawReader_momentum_continuous (fieldUnit i) q.F).comp
    (continuous_snd : Continuous (fun p : PhysicalMomentum×PhysicalMomentum=>p.2))
  have original : (fun p : PhysicalMomentum×PhysicalMomentum=>
      rawInitial (sourcePhysicalMaterialPoint q p.1 p.2) (fieldUnit i))=
      (fun p=>jointResolvent p.1 q.F q.z 0*rawReader (fieldUnit i) p.2 q.F 0*jointResolvent p.2 q.F q.w 0) := by
    funext p
    rw [rawInitial,sourcePhysicalMaterialPoint_left,sourcePhysicalMaterialPoint_right]
    rfl
  have initial : Continuous (fun p : PhysicalMomentum×PhysicalMomentum=>
      rawInitial (sourcePhysicalMaterialPoint q p.1 p.2) (fieldUnit i)) := by
    rw [original]
    exact (leftR.mul reader).mul rightR
  have base : Continuous (fun p : PhysicalMomentum×PhysicalMomentum=>
      sourceProjection*rawInitial (sourcePhysicalMaterialPoint q p.1 p.2) (fieldUnit i)*sourceProjection) :=
    (continuous_const.mul initial).mul continuous_const
  have upper : Continuous (fun p : PhysicalMomentum×PhysicalMomentum=>
      sourceProjection*rawInitial (sourcePhysicalMaterialPoint q p.1 p.2) (fieldUnit i)*sourceExcitedProjection) :=
    (continuous_const.mul initial).mul continuous_const
  exact ⟨by simpa only [sourceFullInitialBase] using base,
    by simpa only [sourceFullInitialUpper] using upper⟩

theorem sourceActualInitial_slow_limit (q : PhysicalResponsePoint) (n : PhysicalMomentum) (i : Fin 289)
    (nonrealL : q.z.im≠0) (nonrealR : q.w.im≠0) :
    Tendsto (fun delta : ℝ=>sourceFullInitialBase q (-(delta • n)) 0 i) (𝓝 0)
      (𝓝 (sourceFullInitialBase q 0 0 i)) ∧
    Tendsto (fun delta : ℝ=>sourceFullInitialUpper q (-(delta • n)) 0 i) (𝓝 0)
      (𝓝 (sourceFullInitialUpper q 0 0 i)) := by
  have momentum : Continuous (fun delta : ℝ=>(-(delta • n),(0 : PhysicalMomentum))) :=
    (continuous_id.smul continuous_const).neg.prodMk continuous_const
  have source:=sourceActualInitial_continuous q i nonrealL nonrealR
  constructor
  · simpa only [Function.comp_def,zero_smul,neg_zero] using (source.1.comp momentum).tendsto 0
  · simpa only [Function.comp_def,zero_smul,neg_zero] using (source.2.comp momentum).tendsto 0

/-- Exact normalized reconstruction of all original N1 slots. -/
theorem sourceActualSlow_normalized_return (q : PhysicalResponsePoint) (n : PhysicalMomentum) (delta : ℝ)
    (positiveDelta : 0<delta) (zeta : ℂ) (positiveZeta : 0<zeta.re) (i : Fin 289)
    (small : (abs delta) ≤ sourceSlowRadius q.F n zeta) :
    let X0:=sourceFullHalfBase q (-(delta • n)) 0 i ((delta:ℂ)*zeta)
    let X1:=sourceFullHalfUpper q (-(delta • n)) 0 i ((delta:ℂ)*zeta)
    let B0:=sourceFullInitialBase q (-(delta • n)) 0 i
    let B1:=sourceFullInitialUpper q (-(delta • n)) 0 i
    let U0:=((delta:ℂ)^2) • sourceEqualProjection q.F X0
    let U1:=(delta:ℂ) • sourceEqualProjection q.F X1
    ((delta:ℂ)^2) • X0=sourceSlowReturn q.F n zeta delta
      (U0+((delta:ℂ)^2) • sourceOffgapInverse q.F B0-
        (delta:ℂ) • sourceOffgapInverse q.F (sourceRetainerReturn q.F
          (sourceSlowReturn q.F n zeta delta (U1+(delta:ℂ) • sourceOffgapInverse q.F B1)))) := by
  dsimp only
  have base:=sourceActualBase_return q n delta positiveDelta zeta positiveZeta i small
  have upperScaled:=sourceActualUpper_normalized_return q n delta positiveDelta zeta positiveZeta i small
  have scaled : ((delta:ℂ)^2) • sourceFullHalfBase q (-(delta • n)) 0 i ((delta:ℂ)*zeta)=
      sourceSlowReturn q.F n zeta delta
        (((delta:ℂ)^2) • sourceEqualProjection q.F (sourceFullHalfBase q (-(delta • n)) 0 i ((delta:ℂ)*zeta))+
          ((delta:ℂ)^2) • sourceOffgapInverse q.F (sourceFullInitialBase q (-(delta • n)) 0 i)-
          (delta:ℂ) • sourceOffgapInverse q.F (sourceRetainerReturn q.F
            ((delta:ℂ) • sourceFullHalfUpper q (-(delta • n)) 0 i ((delta:ℂ)*zeta)))) := by
    have scaledBase:=congrArg (fun X : SourceOp=>((delta:ℂ)^2) • X) base
    simp only [map_add,map_sub,map_smul,smul_add,smul_sub,smul_smul] at scaledBase ⊢
    convert! scaledBase using 1
    module
  rw [upperScaled] at scaled
  exact scaled

/-- The effective response is the same actual current read by the original preparation. -/
theorem sourceActualSlow_current (q : PhysicalResponsePoint) (n : PhysicalMomentum) (delta : ℝ)
    (positiveDelta : 0<delta) (zeta : ℂ) (positiveZeta : 0<zeta.re) (l r : RestStateIndex) (i : Fin 289)
    (small : (abs delta) ≤ sourceSlowRadius q.F n zeta) :
    sourcePoleCurrentHalf q (-(delta • n)) 0 l r ((delta:ℂ)*zeta) i=
      -sourcePoleRead q.epsilon q.precision (-(delta • n)) 0 l r
        (sourceSlowReturn q.F n zeta delta
          (sourceEqualProjection q.F (sourceFullHalfBase q (-(delta • n)) 0 i ((delta:ℂ)*zeta))+
            sourceOffgapInverse q.F (sourceFullInitialBase q (-(delta • n)) 0 i-
              sourceRetainerReturn q.F (sourceFullHalfUpper q (-(delta • n)) 0 i ((delta:ℂ)*zeta))))) := by
  have positive : 0<((delta:ℂ)*zeta).re := by
    simpa only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero] using mul_pos positiveDelta positiveZeta
  exact (sourceFullHalf_actualCurrent q _ _ l r i _ positive).trans
    (congrArg (fun X : SourceOp=> -sourcePoleRead q.epsilon q.precision (-(delta • n)) 0 l r X)
      (sourceActualBase_return q n delta positiveDelta zeta positiveZeta i small))

/-- The same eight actual external states read the complete Schur response on their common carrier. -/
theorem sourceActualSlow_common_carrier (q : PhysicalResponsePoint) (n : PhysicalMomentum) (delta : ℝ)
    (positiveDelta : 0<delta) (zeta : ℂ) (positiveZeta : 0<zeta.re) (i : Fin 289)
    (small : (abs delta) ≤ sourceSlowRadius q.F n zeta) :
    movingOverlap (-(delta • n))*(show Matrix RestStateIndex RestStateIndex ℂ from fun l r=>
      sourcePoleCurrentHalf q (-(delta • n)) 0 l r ((delta:ℂ)*zeta) i)*(movingOverlap 0).conjTranspose=
      -sourceTensor q.epsilon q.precision 0 0
        (sourceSlowReturn q.F n zeta delta
          (sourceEqualProjection q.F (sourceFullHalfBase q (-(delta • n)) 0 i ((delta:ℂ)*zeta))+
            sourceOffgapInverse q.F (sourceFullInitialBase q (-(delta • n)) 0 i-
              sourceRetainerReturn q.F (sourceFullHalfUpper q (-(delta • n)) 0 i ((delta:ℂ)*zeta))))) := by
  have positive : 0<((delta:ℂ)*zeta).re := by
    simpa only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero] using mul_pos positiveDelta positiveZeta
  exact (sourceFullHalf_common_carrier q _ _ i _ positive).trans
    (congrArg (fun X : SourceOp=> -sourceTensor q.epsilon q.precision 0 0 X)
      (sourceActualBase_return q n delta positiveDelta zeta positiveZeta i small))

end LowEnergy.PreparationVacuumQuantumSlowResponse
