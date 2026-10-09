import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedGradeZeroPreparedRead
import H0mework.Versions.R9c73a630.Physics.LowEnergy.AlphaSource.CanonicalPreparationSourceMaterialPoleAmputation

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualDressedNumberZero
open GaussCoreHilbert GaussYukawaGrade CanonicalGradedSpatialSource
open PreparationVacuumPhysicalHalfAxis PreparationVacuumRawJointFeedback
open PreparationVacuumJointFieldResponse PreparationVacuumPhysicalPoleAmputation
open FullYSourceCutoffVolterra
open scoped InnerProductSpace
abbrev Op:=H→L[ℂ]H
attribute [local irreducible] actualC actualA physicalTime jointResolvent gradeZeroProjection

private theorem positive_left_zero (T : Op) (n : ℕ) (positive : 0<n)
    (homogeneous : GaussYukawaGrade.grade*T=T*GaussYukawaGrade.grade+(n:ℂ) • T) :
    gradeZeroProjection*T=0 := by
  apply ContinuousLinearMap.ext
  intro y
  apply ext_inner_left ℂ
  intro x
  change inner ℂ x (gradeZeroProjection (T y))=inner ℂ x 0
  rw [←grade_zero_projection_pair,inner_zero_right]
  exact positive_grade_pair_zero T n positive homogeneous _ y (grade_zero_projected x)

theorem actualC_grade_zero (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) :
    Commute gradeZeroProjection (actualC p F) := by
  apply grade_zero_commutes
  intro g
  simpa only [actualC] using CanonicalPhysicalSpatial.compression_blocks p F g

/-- The original positive Yukawa grade is invisible only on a grade0 left read. -/
theorem actualA_grade_zero_left (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) :
    gradeZeroProjection*actualA p F=0 := by
  apply positive_left_zero _ 1 (by omega)
  simpa only [Nat.cast_one,one_smul] using actualA_raises p F

theorem actual_prefix_grade_zero_left (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index)
    (n : ℕ) (t : ℝ) (positive : 0<n) :
    gradeZeroProjection*finitePrefix (actualC p F) (actualA p F) n t=0 :=
  positive_left_zero _ n positive
    (finitePrefix_homogeneous _ _ _ (actualC_grade p F) (actualA_raises p F) n t)

/-- All actual positive prefixes vanish on the original all-Number grade0 left projection. -/
theorem actual_time_grade_zero_left (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) (t : ℝ) :
    gradeZeroProjection*physicalTime p F t 0=
      gradeZeroProjection*SourceFiniteUnitary.time (actualC p F) t := by
  rw [actual_time_finitePrefix]
  have returns (n : ℕ) : gradeZeroProjection*partialEvolution (actualC p F) (actualA p F) n t=
      gradeZeroProjection*SourceFiniteUnitary.time (actualC p F) t := by
    induction n with
    | zero => rw [partialEvolution]
    | succ n ih =>
      rw [partialEvolution,mul_add,ih,actual_prefix_grade_zero_left p F (n+1) t (by omega),add_zero]
  exact returns 56

theorem actual_C_time_grade_zero (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) (t : ℝ) :
    Commute gradeZeroProjection (SourceFiniteUnitary.time (actualC p F) t) :=
  SourceFiniteUnitary.time_commutes _ _ (actualC_grade_zero p F) t

theorem actual_free_resolvent_grade_zero (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index)
    (z : ℂ) (nonreal : z.im≠0) :
    Commute gradeZeroProjection (CanonicalPhysicalResolvent.finiteResolvent p F z) := by
  unfold CanonicalPhysicalResolvent.finiteResolvent FullYSourceResolventGraphSplice.resolvent
  exact PreparationVacuumYukawaTransport.inverse_commuting _ _
    (FullYSourceResolventGraphSplice.resolvent_isUnit _ (CanonicalPhysicalSpatial.compression_selfAdjoint p F) z nonreal)
    ((show Commute gradeZeroProjection (CanonicalPhysicalSpatial.compression p F) from
      by simpa only [actualC] using actualC_grade_zero p F).sub_right ((Commute.one_right _).smul_right z))

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

/-- The same original joint Green returns the compressed C Green on this left read, for every nonreal material energy. -/
theorem actual_resolvent_grade_zero_left (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index)
    (z : ℂ) (nonreal : z.im≠0) :
    gradeZeroProjection*jointResolvent p F z 0=
      gradeZeroProjection*CanonicalPhysicalResolvent.finiteResolvent p F z := by
  have free:=FullYSourceResolventGraphSplice.resolvent_left (actualC p F) (actualC_symmetric p F) z nonreal
  have full:=sourceMaterialInverse_right p F z nonreal
  rw [actualGenerator_source] at full
  have full' : ((actualC p F-z • 1)+actualA p F)*jointResolvent p F z 0=1 := by
    simpa only [sub_add_eq_add_sub] using full
  have free' : CanonicalPhysicalResolvent.finiteResolvent p F z*(actualC p F-z • 1)=1 := by
    simpa only [actualC,CanonicalPhysicalResolvent.finiteResolvent] using free
  exact left_inverse_return gradeZeroProjection (actualC p F-z • 1) (actualA p F)
    (CanonicalPhysicalResolvent.finiteResolvent p F z) (jointResolvent p F z 0)
    ((actualC_grade_zero p F).sub_right ((Commute.one_right _).smul_right z))
    (actual_free_resolvent_grade_zero p F z nonreal) (actualA_grade_zero_left p F) free' full'

end LowEnergy.GaussComposite.ActualDressedNumberZero
