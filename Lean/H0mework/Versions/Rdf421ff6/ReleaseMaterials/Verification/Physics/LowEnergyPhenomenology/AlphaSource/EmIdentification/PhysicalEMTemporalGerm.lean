import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedNumberFieldLeft
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedNoetherAction
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedReaderContactBasis
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceGaugeWeightedUnitReader

/-! The actual source electromagnetic temporal row: its full CAR germ keeps the weighted
momentum reader constant on the whole valid tube, so the original five-factor kernel
collapses on the grade-zero left read to the free compression legs with the same J0. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
noncomputable section
namespace LowEnergy.GaussComposite.ActualDressedEMTemporal
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open Stage10
open StageNineHolonomicField FullQuantum.StateGreen
open SourceQuantumFockGauge SourceQuantumGaugeSliceCoordinates SourceQuantumConfigurationHilbert
open GaussCoreHilbert GaussCoreDifferential GaussQuantumMultiplier GaussHistoryHilbert
open PreparationVacuumMixedFieldReturn CanonicalGradedSpatialSource
open PreparationVacuumSourceFieldFamily PreparationVacuumNonlinearFieldCurve
open PreparationVacuumGaugeSourceInjection PreparationVacuumActionFieldLift PreparationVacuumActualFieldQuantization
open PreparationVacuumOriginalDensity PreparationVacuumJointFieldResponse PreparationVacuumRawJointFeedback
open PreparationVacuumFullFieldRiesz PreparationVacuumSourceActionJets PreparationVacuumPhysicalFeedback
open PreparationVacuumNoetherChart PreparationPhysicalGaugeMomentumCoupling
open PreparationPhysicalPhaseGaugeRealization PreparationVacuumPhysicalGradeZeroRead
open Filter Set MeasureTheory
open scoped Topology ContDiff BigOperators Matrix Matrix.Norms.L2Operator InnerProductSpace
attribute [local instance] SourceRealScalarFock.branchOrder
local instance : DecidableEq Quantum.Index:=Classical.decEq _
local instance : DecidableEq Mode:=Classical.decEq _
local instance : Fintype NativeHistoryGrade.Label:=Fintype.ofFinite _

open PreparationVacuumNativeLocalWard PreparationVacuumNativeSourceRestriction PreparationVacuumHalfDensityFiber
open PreparationCoordinates
open ActualDressedFullCoulomb ActualDressedNoether ActualDressedConstraintRead
open ActualDressedNumberZero ActualDressedNumberField ActualDressedSourcePreparation
open LowEnergy.GaussComposite.SourceGraph LowEnergy.PreparationVacuumSourcePreparedResponse
attribute [local irreducible] noetherReaderContact jointResolvent
  jointCResolvent physicalTime gradeZeroProjection dressedEulerObserver

/-- Inside the valid tube the source transported symbol is independent of the ambient
candidate, so each frame-test entry of the EM row is the constant unit form. -/
private theorem em_form_flat (p : PhysicalMomentum) (a b : QuantumTest)
    (h : Field289) (small : ‖h‖<ambientRadius a) :
    noetherForm (sourcePhaseGaugeField 0) p a b h=
      (ActionNormalization.phaseMomentum:ℂ)*sourceGaugeUnitForm p a b := by
  rw [noetherForm,sourceGaugeUnitForm,←integral_const_mul]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro z
  by_cases inside : z∈tsupport a
  · have valid:=ambientRadius_valid a h z small.le inside
    change pairSample z (a z) (quantizer
        (transportedRawSymbol (sourcePhaseGaugeField 0) (sourceState z) (ambientState (h,z)) p) (b z))=
      (ActionNormalization.phaseMomentum:ℂ)*(pairSample z (a z)
        (quantizer (sourceGaugeUnitSymbol (sourceState z) p) (b z)))
    rw [sourceGaugeTransportedSymbol _ _ valid,quantizer.map_smul_of_tower]
    simp only [RCLike.real_smul_eq_coe_smul (K:=ℂ),smul_apply,pairSample_smul_right]
    rfl
  · simp only [noetherSample_zero _ _ _ _ _ _ inside,image_eq_zero_of_notMem_tsupport inside,
      pairSample_zero_left,mul_zero]

/-- The whole finite EM reader is the constant source unit reader on the same neighborhood. -/
private theorem em_reader_flat (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) :
    ∀ᶠh : Field289 in 𝓝 0,
      noetherReader (sourcePhaseGaugeField 0) p F h=
        ActionNormalization.phaseMomentum • sourceGaugeUnitReader p F := by
  have entries : ∀ᶠh : Field289 in 𝓝 0,∀i j : FrameIndex F,
      noetherForm (sourcePhaseGaugeField 0) p (frameTest F i) (frameTest F j) h=
        (ActionNormalization.phaseMomentum:ℂ)*sourceGaugeUnitForm p (frameTest F i) (frameTest F j) := by
    apply eventually_all.mpr
    intro i
    apply eventually_all.mpr
    intro j
    have near : ∀ᶠh : Field289 in 𝓝 0,‖h‖<ambientRadius (frameTest F i) :=
      (continuous_norm.tendsto 0).eventually
        (gt_mem_nhds (by simpa only [norm_zero] using ambientRadius_positive (frameTest F i)))
    exact near.mono (fun h small=>em_form_flat p (frameTest F i) (frameTest F j) h small)
  filter_upwards [entries] with h flat
  have same : (fun i j=>noetherForm (sourcePhaseGaugeField 0) p (frameTest F i) (frameTest F j) h)=
      fun i j=>(ActionNormalization.phaseMomentum:ℂ)*sourceGaugeUnitForm p (frameTest F i) (frameTest F j) :=
    funext (fun i=>funext (fun j=>flat i j))
  calc noetherReader (sourcePhaseGaugeField 0) p F h
      =finiteRiesz F (fun i j=>(ActionNormalization.phaseMomentum:ℂ)*
          sourceGaugeUnitForm p (frameTest F i) (frameTest F j)) := by
        unfold noetherReader
        exact congrArg (finiteRiesz F) same
    _ =ActionNormalization.phaseMomentum • sourceGaugeUnitReader p F := by
        simp only [sourceGaugeUnitReader,finiteRiesz,Finset.smul_sum,
          RCLike.real_smul_eq_coe_smul (K:=ℂ),smul_smul]
        rfl

/-- The source EM reader germ: the weighted momentum row is flat on the whole valid tube,
with no contact term ever assigned zero by hand. -/
theorem actual_em_temporal_reader_germ (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) :
    noetherReader (sourcePhaseGaugeField 0) p F=ᶠ[𝓝 0]
      fun _=>noetherReader (sourcePhaseGaugeField 0) p F 0 := by
  filter_upwards [em_reader_flat p F] with h flat
  rw [flat,sourceGaugeNoetherReader_momentum]

/-- The resting source EM reader retains the original phase momentum weight. -/
def emTemporalReader (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) : H→L[ℂ]H :=
  noetherReader (sourcePhaseGaugeField 0) p F 0

private theorem gaugeSlot_injective : Function.Injective (gaugeSlot 0):=by
  intro a b equal
  apply Fin.ext
  have value:=congrArg Fin.val equal
  simp only [gaugeSlot] at value
  omega

private theorem em_field_slot (a : Fin 12) : (sourcePhaseGaugeField 0) (gaugeSlot 0 a)=
    rawCoordinates sourcePhaseGaugeLie a := by
  unfold sourcePhaseGaugeField
  rw [Finset.sum_apply,Finset.sum_eq_single a]
  · simp only [Pi.smul_apply,smul_eq_mul,gaugeField,Pi.single_apply,eq_self_iff_true,if_true,mul_one]
  · intro b _ different
    simp only [Pi.smul_apply,smul_eq_mul,gaugeField,Pi.single_apply]
    rw [if_neg (fun e=>different (gaugeSlot_injective e).symm),mul_zero]
  · intro absent
    exact absurd (Finset.mem_univ a) absent

private theorem em_field_outside (k : Fin 289)
    (outside : ∀a : Fin 12,k≠gaugeSlot 0 a) : (sourcePhaseGaugeField 0) k=0 := by
  unfold sourcePhaseGaugeField
  simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
  apply Finset.sum_eq_zero
  intro a _
  rw [gaugeField,Pi.single_apply]
  simp only [outside a,if_false,mul_zero]

/-- The real-linearity of the original source reader reduces the EM row to its twelve gauge legs. -/
private theorem em_raw_reader_legs (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) :
    rawReader (sourcePhaseGaugeField 0) p F 0=
      ∑a : Fin 12,(rawCoordinates sourcePhaseGaugeLie a:ℂ)•rawReader (gaugeField 0 a) p F 0 := by
  have initial:=source_reader_initial (sourcePhaseGaugeField 0) p F
  rw [noetherReader_source] at initial
  rw [initial]
  have restricted : (∑k : Fin 289,((sourcePhaseGaugeField 0) k:ℂ)•noetherReader (fieldUnit k) p F 0)=
      ∑k ∈ Finset.image (gaugeSlot 0) Finset.univ,
        ((sourcePhaseGaugeField 0) k:ℂ)•noetherReader (fieldUnit k) p F 0 := by
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro k _ outside
    have zero : (sourcePhaseGaugeField 0) k=0 := by
      apply em_field_outside
      intro a ne
      exact outside (Finset.mem_image.mpr ⟨a,Finset.mem_univ a,ne.symm⟩)
    have coefficient : ((sourcePhaseGaugeField 0) k:ℂ)=0 := by
      rw [zero,Complex.ofReal_zero]
    rw [coefficient]
    exact zero_smul (M₀:=ℂ) (A:=PreparationVacuumJointFieldResponse.Operator) _
  rw [restricted,Finset.sum_image (fun a _ b _ e=>gaugeSlot_injective e)]
  apply Finset.sum_congr rfl
  intro a _
  rw [em_field_slot a,noetherReader_source (fieldUnit (gaugeSlot 0 a)) p F,
    show fieldUnit (gaugeSlot 0 a)=gaugeField 0 a from rfl]

/-- The EM row preserves every grade label, hence the original grade-zero projection. -/
theorem actual_em_temporal_reader_grade_zero (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) :
    Commute gradeZeroProjection (emTemporalReader p F) := by
  apply grade_zero_commutes
  intro g
  change Commute (NativeHistoryGrade.projection g) (noetherReader (sourcePhaseGaugeField 0) p F 0)
  rw [noetherReader_source,em_raw_reader_legs]
  apply Commute.sum_right
  intro a _
  exact (sourceRawGaugeReader_blocks 0 a p F g).smul_right _

/-- The same five factors with the free compression legs and the resting EM reader. -/
def emTemporalFreeKernel (event : DressedEvent) (transfer : PhysicalMomentum) (age : ℝ)
    (h : Field289) : H→L[ℂ]H :=
  SourceFiniteUnitary.time (jointCompression (event.momentum-transfer) event.frame h) (-age)*
    jointCResolvent (event.momentum-transfer) event.frame event.energy h*
    emTemporalReader event.momentum event.frame*
    jointCResolvent event.momentum event.frame event.energy h*
  SourceFiniteUnitary.time (jointCompression event.momentum event.frame h) age

/-- On the Euler pair the left grade-zero projection reads through the product. -/
theorem em_euler_left (event : DressedEvent) (A : H→L[ℂ]H) :
    dressedEulerObserver event A=
      dressedEulerObserver event (gradeZeroProjection*A) := by
  rw [dressed_euler_observer_original,dressed_euler_observer_original]
  have unit : gradeZeroProjection (sourceDressedUnit event.epsilon event.precision)=
      sourceDressedUnit event.epsilon event.precision :=
    actual_created_unit_grade_zero_fixed event.epsilon event.precision
  have background : gradeZeroProjection (prepared (sourceProfile event.epsilon event.precision))=
      prepared (sourceProfile event.epsilon event.precision) :=
    actual_background_grade_zero_fixed (sourceProfile event.epsilon event.precision)
  simp only [mul_apply_eq_comp,ContinuousLinearMap.comp_apply,
    ←grade_zero_projection_pair,unit,background]

/-- A right projection against the grade-zero Euler states is absorbed. -/
theorem em_euler_right (event : DressedEvent) (B : H→L[ℂ]H) :
    dressedEulerObserver event (B*gradeZeroProjection)=
      dressedEulerObserver event B := by
  rw [dressed_euler_observer_original,dressed_euler_observer_original]
  have unit : gradeZeroProjection (sourceDressedUnit event.epsilon event.precision)=
      sourceDressedUnit event.epsilon event.precision :=
    actual_created_unit_grade_zero_fixed event.epsilon event.precision
  have background : gradeZeroProjection (prepared (sourceProfile event.epsilon event.precision))=
      prepared (sourceProfile event.epsilon event.precision) :=
    actual_background_grade_zero_fixed (sourceProfile event.epsilon event.precision)
  simp only [mul_apply_eq_comp,ContinuousLinearMap.comp_apply,unit,background]

theorem em_projected_five {R : Type*} [Ring R] (P A B J D E a b d e : R)
    (hA : P*A=a*P) (hB : P*B=b*P) (hJ : P*J=J*P)
    (hD : P*D=d*P) (hE : P*E=e*P) :
    P*(A*B*J*D*E)=(a*b*J*d*e)*P:=by
  calc
    _=(P*A)*B*J*D*E:=by noncomm_ring
    _=a*(P*B)*J*D*E:=by rw [hA];noncomm_ring
    _=a*b*(P*J)*D*E:=by rw [hB];noncomm_ring
    _=a*b*J*(P*D)*E:=by rw [hJ];noncomm_ring
    _=a*b*J*d*(P*E):=by rw [hD];noncomm_ring
    _=_:=by rw [hE];noncomm_ring

/-- Both original legs and the resting EM row project to the same free kernel, with the
full 289-column field retained and distinct left/right momenta preserved. -/
theorem actual_em_temporal_observer_germ (event : DressedEvent) (transfer : PhysicalMomentum) :
    ∀ᶠh : Field289 in 𝓝 0,∀age : ℝ,
      dressedEulerObserver event
        (dressedNoetherKernel event transfer (sourcePhaseGaugeField 0) age h)=
        dressedEulerObserver event (emTemporalFreeKernel event transfer age h) := by
  filter_upwards [em_reader_flat event.momentum event.frame,
    actual_joint_resolvent_grade_zero_left (event.momentum-transfer) event.frame event.energy event.nonreal,
    actual_joint_resolvent_grade_zero_left event.momentum event.frame event.energy event.nonreal,
    actual_joint_free_units_near_zero (event.momentum-transfer) event.frame event.energy event.nonreal,
    actual_joint_free_units_near_zero event.momentum event.frame event.energy event.nonreal]
    with h flat rL rR uL uR
  intro age
  have commuteL : Commute gradeZeroProjection
      (jointCResolvent (event.momentum-transfer) event.frame event.energy h) := by
    unfold jointCResolvent
    exact PreparationVacuumYukawaTransport.inverse_commuting _ _ uL
      ((actual_joint_C_grade_zero _ _ h).sub_right ((Commute.one_right _).smul_right _))
  have commuteR : Commute gradeZeroProjection
      (jointCResolvent event.momentum event.frame event.energy h) := by
    unfold jointCResolvent
    exact PreparationVacuumYukawaTransport.inverse_commuting _ _ uR
      ((actual_joint_C_grade_zero _ _ h).sub_right ((Commute.one_right _).smul_right _))
  have commuteJ : Commute gradeZeroProjection (emTemporalReader event.momentum event.frame) :=
    actual_em_temporal_reader_grade_zero event.momentum event.frame
  have tL : gradeZeroProjection*physicalTime (event.momentum-transfer) event.frame (-age) h=
      SourceFiniteUnitary.time (jointCompression (event.momentum-transfer) event.frame h) (-age)*
        gradeZeroProjection :=
    (actual_joint_time_grade_zero_left _ _ _ _).trans
      (SourceFiniteUnitary.time_commutes _ _ (actual_joint_C_grade_zero _ _ h) _).eq
  have tR : gradeZeroProjection*physicalTime event.momentum event.frame age h=
      SourceFiniteUnitary.time (jointCompression event.momentum event.frame h) age*
        gradeZeroProjection :=
    (actual_joint_time_grade_zero_left _ _ _ _).trans
      (SourceFiniteUnitary.time_commutes _ _ (actual_joint_C_grade_zero _ _ h) _).eq
  have lR : gradeZeroProjection*jointResolvent (event.momentum-transfer) event.frame event.energy h=
      jointCResolvent (event.momentum-transfer) event.frame event.energy h*gradeZeroProjection :=
    rL.trans commuteL.eq
  have rR' : gradeZeroProjection*jointResolvent event.momentum event.frame event.energy h=
      jointCResolvent event.momentum event.frame event.energy h*gradeZeroProjection :=
    rR.trans commuteR.eq
  have readerSame : noetherReader (sourcePhaseGaugeField 0) event.momentum event.frame h=
      emTemporalReader event.momentum event.frame := by
    rw [flat]
    unfold emTemporalReader
    rw [sourceGaugeNoetherReader_momentum]
  have collapsed : gradeZeroProjection*dressedNoetherKernel event transfer
      (sourcePhaseGaugeField 0) age h=
      emTemporalFreeKernel event transfer age h*gradeZeroProjection := by
    unfold dressedNoetherKernel emTemporalFreeKernel
    rw [readerSame]
    exact em_projected_five _ _ _ _ _ _ _ _ _ _ tL lR commuteJ.eq rR' tR
  calc dressedEulerObserver event (dressedNoetherKernel event transfer (sourcePhaseGaugeField 0) age h)
      =dressedEulerObserver event
        (gradeZeroProjection*dressedNoetherKernel event transfer (sourcePhaseGaugeField 0) age h) :=
        em_euler_left _ _
    _ =dressedEulerObserver event (emTemporalFreeKernel event transfer age h*gradeZeroProjection) := by
        rw [collapsed]
    _ =dressedEulerObserver event (emTemporalFreeKernel event transfer age h) :=
        em_euler_right _ _

end LowEnergy.GaussComposite.ActualDressedEMTemporal
