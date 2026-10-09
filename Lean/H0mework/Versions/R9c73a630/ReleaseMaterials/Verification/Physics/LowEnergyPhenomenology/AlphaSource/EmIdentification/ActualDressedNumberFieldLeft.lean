import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedNumberFieldRange

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualDressedNumberField
open GaussCoreHilbert CanonicalGradedSpatialSource
open PreparationVacuumJointFieldResponse PreparationVacuumMixedFieldReturn
open PreparationVacuumRawJointFeedback PreparationVacuumPhysicalHalfAxis
open PreparationVacuumGradedTransport PreparationVacuumUncutYukawa
open ActualDressedNumberZero
open Filter
open scoped Topology InnerProductSpace
local instance fieldLeftRealAlgebra : NormedAlgebra ℝ ActualDressedNumberZero.Op:=NormedAlgebra.restrictScalars ℝ ℂ _
attribute [local irreducible] jointCompression jointY jointGenerator jointResolvent physicalTime gradeZeroProjection

theorem actual_joint_C_grade_zero (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) (h : Field289) :
    Commute gradeZeroProjection (jointCompression p F h) :=
  grade_zero_commutes _ (fun g=>actual_joint_compression_blocks p F h g)

theorem actual_joint_Y_grade_zero_left (h : Field289) (phi : CanonicalGradedSpatial.Localizer) :
    gradeZeroProjection*jointY phi h=0 := by
  apply ContinuousLinearMap.ext
  intro y
  apply ext_inner_left ℂ
  intro x
  change inner ℂ x (gradeZeroProjection (jointY phi h y))=inner ℂ x 0
  rw [←grade_zero_projection_pair,inner_zero_right]
  apply positive_grade_pair_zero _ 1 (by omega) _ _ y (grade_zero_projected x)
  simpa only [Nat.cast_one,one_smul] using actual_joint_Y_raises h phi

private theorem generator_zero_shift (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) (h : Field289) :
    jointGenerator p F 0 h=jointCompression p F h+jointY (PreparationVacuumYukawaTransport.finiteRetainer p F) h := by
  unfold jointGenerator
  have zero : (0:ℂ) • (1:ActualDressedNumberZero.Op)=0 := by
    apply ContinuousLinearMap.ext
    intro x
    exact zero_smul ℂ x
  rw [zero,sub_zero]

/-- The original left time return holds on the actual field family, so its field derivatives are available. -/
theorem actual_joint_time_grade_zero_left (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index)
    (t : ℝ) (h : Field289) : gradeZeroProjection*physicalTime p F t h=
      gradeZeroProjection*SourceFiniteUnitary.time (jointCompression p F h) t := by
  unfold physicalTime
  rw [generator_zero_shift]
  exact CanonicalGradedGaugeReturn.left_time_return _ _ _ (actual_joint_C_grade_zero p F h)
    (actual_joint_Y_grade_zero_left h (PreparationVacuumYukawaTransport.finiteRetainer p F)) t

/-- A read of the original free compression's inverse, on the same field family. -/
def jointCResolvent (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) (z : ℂ) (h : Field289) : ActualDressedNumberZero.Op :=
  Ring.inverse (jointCompression p F h-z • 1)

private theorem compression_zero (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) :
    jointCompression p F 0=CanonicalPhysicalSpatial.compression p F := by
  have source:=(jointCompression_ray (0:Field289) p F).self_of_nhds
  simp only [zero_smul] at source
  exact source.trans (transportedCompression_zero 0 p F)

theorem actual_joint_free_units_near_zero (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index)
    (z : ℂ) (nonreal : z.im≠0) :
    ∀ᶠh : Field289 in 𝓝 0,IsUnit (jointCompression p F h-z • (1:ActualDressedNumberZero.Op)) := by
  have unit : IsUnit (jointCompression p F 0-z • (1:ActualDressedNumberZero.Op)) := by
    rw [compression_zero]
    exact FullYSourceResolventGraphSplice.resolvent_isUnit _ (CanonicalPhysicalSpatial.compression_selfAdjoint p F) z nonreal
  have continuous:=(jointCompression_C2 p F).continuousAt.sub
    (continuousAt_const (y:=z • (1:ActualDressedNumberZero.Op)))
  exact continuous.preimage_mem_nhds (Units.isOpen.mem_nhds unit)

theorem actual_joint_full_units_near_zero (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index)
    (z : ℂ) (nonreal : z.im≠0) : ∀ᶠh : Field289 in 𝓝 0,IsUnit (jointGenerator p F z h) :=
  (jointGenerator_C2 p F z).continuousAt.preimage_mem_nhds
    (Units.isOpen.mem_nhds (jointGenerator_unit p F z nonreal))

private theorem left_inverse_return {R : Type*} [Ring R] (P D A U V : R)
    (PD : Commute P D) (PU : Commute P U) (PA : P*A=0)
    (free : U*D=1) (full : (D+A)*V=1) : P*V=P*U := by
  calc
    _=(U*D)*(P*V) := by rw [free,one_mul]
    _=U*((D*P)*V) := by noncomm_ring
    _=U*((P*D)*V) := by rw [PD.symm.eq]
    _=U*((P*D+P*A)*V) := by rw [PA,add_zero]
    _=U*(P*((D+A)*V)) := by noncomm_ring
    _=U*P := by rw [full,mul_one]
    _=P*U := PU.eq.symm

/-- Both units are generated near zero from the original source continuity and nonreal energy; no inverse witness is a public premise. -/
theorem actual_joint_resolvent_grade_zero_left (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index)
    (z : ℂ) (nonreal : z.im≠0) :
    ∀ᶠh : Field289 in 𝓝 0,gradeZeroProjection*jointResolvent p F z h=
      gradeZeroProjection*jointCResolvent p F z h := by
  filter_upwards [actual_joint_free_units_near_zero p F z nonreal,actual_joint_full_units_near_zero p F z nonreal] with h free full
  have blocks:=((actual_joint_C_grade_zero p F h).sub_right ((Commute.one_right _).smul_right z))
  have inverse_blocks : Commute gradeZeroProjection (jointCResolvent p F z h) := by
    unfold jointCResolvent
    exact PreparationVacuumYukawaTransport.inverse_commuting _ _ free blocks
  have free_inverse : jointCResolvent p F z h*(jointCompression p F h-z • (1:ActualDressedNumberZero.Op))=1 := by
    unfold jointCResolvent
    exact Ring.inverse_mul_cancel _ free
  have full_inverse : ((jointCompression p F h-z • (1:ActualDressedNumberZero.Op))+
      jointY (PreparationVacuumYukawaTransport.finiteRetainer p F) h)*jointResolvent p F z h=1 := by
    have source:=Ring.mul_inverse_cancel _ full
    simpa only [jointResolvent,jointGenerator,sub_add_eq_add_sub] using source
  exact left_inverse_return _ _ _ _ _ blocks inverse_blocks
    (actual_joint_Y_grade_zero_left h (PreparationVacuumYukawaTransport.finiteRetainer p F)) free_inverse full_inverse

end LowEnergy.GaussComposite.ActualDressedNumberField
