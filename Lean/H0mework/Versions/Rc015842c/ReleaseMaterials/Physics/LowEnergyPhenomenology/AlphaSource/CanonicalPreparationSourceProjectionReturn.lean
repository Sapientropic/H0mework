import H0mework.Versions.Rc015842c.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationPhiGrade
import H0mework.Versions.Rc015842c.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationPrincipalLaplace
import H0mework.Versions.AB.Physics.LowEnergy.AlphaSource.CanonicalGradedGaugeReturn

set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency true
noncomputable section
namespace LowEnergy.PreparationVacuumPhysicalGradeZeroRead
open GaussCoreHilbert CanonicalGradedSpatialSource PreparationVacuumElectromagneticIdentity
open PreparationVacuumMovingPoleGaussReturn PreparationVacuumPhysicalZeroRead
open PreparationVacuumJointFieldResponse PreparationVacuumPhysicalHalfAxis
open PreparationVacuumPhysicalPoleAmputation PreparationVacuumPhysicalFeedback
open PreparationVacuumMixedFieldReturn PreparationVacuumRawJointFeedback
open CanonicalGradedCurrent FullYSourceCutoffVolterra
open scoped BigOperators InnerProductSpace
attribute [local irreducible] actualC actualA physicalTime sourcePoleRead sourceProjection

theorem actualC_sourceProjection (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) :
    Commute sourceProjection (actualC p F):=
  by simpa only [sourceProjection,actualC] using
    CanonicalPhysicalSpatial.compression_blocks p F CanonicalGradedCurrent.sourceLabel

theorem actualA_sourceProjection (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) :
    sourceProjection*actualA p F=0:=
  positive_grade_left_zero _ 1 (by simpa only [Nat.cast_one,one_smul] using actualA_raises p F) (by norm_num)

theorem actual_time_sourceProjection (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) (t : ℝ) :
    sourceProjection*physicalTime p F t 0=
      sourceProjection*SourceFiniteUnitary.time (actualC p F) t:=by
  rw [physicalTime,actualGenerator_source]
  exact CanonicalGradedGaugeReturn.left_time_return _ _ _
    (actualC_sourceProjection p F) (actualA_sourceProjection p F) t

theorem actual_prefix_sourceProjection (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index)
    (n : ℕ) (t : ℝ) (positive : 0<n) :
    sourceProjection*finitePrefix (actualC p F) (actualA p F) n t=0:=
  positive_grade_left_zero _ n
    (finitePrefix_homogeneous _ _ _ (actualC_grade p F) (actualA_raises p F) n t) positive

private theorem projected_inverse {R : Type*} [Ring R] [Algebra ℂ R]
    (P C A U V : R) (z : ℂ) (PU : Commute P U) (PA : P*A=0)
    (freeInverse : U*(C-z • 1)=1) (fullInverse : (C+A-z • 1)*V=1) : P*V=P*U:=by
  have paid : (P*U)*(C+A-z • 1)=P:=by
    have zero : (P*U)*A=0:=by rw [PU.eq,mul_assoc,PA,mul_zero]
    calc
      _=(P*U)*(C-z • 1)+(P*U)*A:=by noncomm_ring
      _=P:=by rw [zero,mul_assoc,freeInverse,mul_one,add_zero]
  calc
    P*V=((P*U)*(C+A-z • 1))*V:=by rw [paid]
    _=(P*U)*((C+A-z • 1)*V):=mul_assoc _ _ _
    _=P*U:=by rw [fullInverse,mul_one]

theorem actual_resolvent_sourceProjection (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index)
    (z : ℂ) (nonreal : z.im≠0) :
    sourceProjection*jointResolvent p F z 0=
      sourceProjection*CanonicalPhysicalResolvent.finiteResolvent p F z:=by
  have freeInverse:=FullYSourceResolventGraphSplice.resolvent_left
    (actualC p F) (actualC_symmetric p F) z nonreal
  have fullInverse:=sourceMaterialInverse_right p F z nonreal
  rw [actualGenerator_source] at fullInverse
  simp only [actualC] at freeInverse
  have commutes : Commute sourceProjection (CanonicalPhysicalResolvent.finiteResolvent p F z):=by
    exact PreparationVacuumYukawaTransport.inverse_commuting _ _
      (FullYSourceResolventGraphSplice.resolvent_isUnit (CanonicalPhysicalSpatial.compression p F)
        (CanonicalPhysicalSpatial.compression_selfAdjoint p F) z nonreal)
      ((show Commute sourceProjection (CanonicalPhysicalSpatial.compression p F) from
        by simpa only [actualC] using actualC_sourceProjection p F).sub_right ((Commute.one_right _).smul_right z))
  simpa only [actualC,CanonicalPhysicalResolvent.finiteResolvent] using
    projected_inverse sourceProjection (CanonicalPhysicalSpatial.compression p F) (actualA p F)
      (FullYSourceResolventGraphSplice.resolvent (CanonicalPhysicalSpatial.compression p F) z)
      (jointResolvent p F z 0) z commutes (actualA_sourceProjection p F) freeInverse
      (by simpa only [actualC] using fullInverse)

set_option backward.isDefEq.respectTransparency false in
theorem sourcePrincipalBlock_left_positive_zero (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (left right : RestStateIndex) (reader : PreparationVacuumMixedFieldReturn.Field289)
    (j k : Fin 57) (t : ℝ) (positive : 0<j.val) :
    sourcePoleRead q.epsilon q.precision pL pR left right
      (sourcePrincipalBlock q pL pR reader j k t)=0:=by
  rw [sourcePoleRead_actual]
  have fixed:=sourcePolePrepared_sourceProjection q.epsilon q.precision pL left
  rw [←fixed]
  have symmetry:=NativeHistoryGrade.projection_symmetric CanonicalGradedCurrent.sourceLabel
    (sourcePolePrepared q.epsilon q.precision pL left)
    (sourcePrincipalBlock q pL pR reader j k t (sourcePolePrepared q.epsilon q.precision pR right))
  have read : inner ℂ (sourceProjection (sourcePolePrepared q.epsilon q.precision pL left))
      (sourcePrincipalBlock q pL pR reader j k t (sourcePolePrepared q.epsilon q.precision pR right))=
    inner ℂ (sourcePolePrepared q.epsilon q.precision pL left)
      (sourceProjection (sourcePrincipalBlock q pL pR reader j k t
        (sourcePolePrepared q.epsilon q.precision pR right))):=by
    unfold sourceProjection
    exact symmetry
  rw [read]
  have paidPrefix:=actual_prefix_sourceProjection pL q.F j.val (-t) positive
  have zero:=congrArg (fun A : H→L[ℂ] H=>A
    (jointResolvent pL q.F q.z 0 (rawReader reader pR q.F 0
      (jointResolvent pR q.F q.w 0
        (finitePrefix (actualC pR q.F) (actualA pR q.F) k.val t
          (sourcePolePrepared q.epsilon q.precision pR right)))))) paidPrefix
  simpa only [sourceProjection,sourcePrincipalBlock,mul_apply_eq_comp,zero_apply,inner_zero_right] using congrArg
    (fun v : H=>inner ℂ (sourcePolePrepared q.epsilon q.precision pL left) v) zero

theorem sourcePrincipalEuler_high_zero (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (left right : RestStateIndex) (n : Fin 113) (t : ℝ) (i : Fin 289) (high : 57≤n.val) :
    sourcePrincipalEulerSector q pL pR left right n t i=0:=by
  unfold sourcePrincipalEulerSector sourcePrincipalSector
  rw [map_sum]
  apply neg_eq_zero.mpr
  apply Finset.sum_eq_zero
  intro j _
  rw [map_sum]
  apply Finset.sum_eq_zero
  intro k _
  by_cases same : j.val+k.val=n.val
  · rw [if_pos same]
    exact sourcePrincipalBlock_left_positive_zero q pL pR left right _ j k t (by omega)
  · rw [if_neg same,map_zero]

theorem sourcePrincipalHalf_high_zero (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (left right : RestStateIndex) (lambda : ℂ) (n : Fin 113) (i : Fin 289) (high : 57≤n.val) :
    sourcePrincipalHalf q pL pR left right lambda n i=0:=by
  unfold sourcePrincipalHalf
  simp_rw [sourcePrincipalEuler_high_zero q pL pR left right n _ i high,mul_zero]
  exact MeasureTheory.integral_zero _ _

end LowEnergy.PreparationVacuumPhysicalGradeZeroRead
