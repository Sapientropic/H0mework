import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedGradeZeroLeftPropagation

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualDressedNumberZero
open GaussCoreHilbert CanonicalGradedSpatialSource
open PreparationVacuumPhysicalHalfAxis PreparationVacuumJointFieldResponse
open PreparationVacuumPhysicalPoleAmputation
open ActualDressedNumberSector
attribute [local irreducible] actualC actualA numberTwoProjection numberTwoGrade jointResolvent

private theorem inverse_preserves (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index)
    (z : ℂ) (nonreal : z.im≠0) (g : Fin 57) :
    Commute (numberTwoGrade g) (CanonicalPhysicalResolvent.finiteResolvent p F z) := by
  unfold CanonicalPhysicalResolvent.finiteResolvent FullYSourceResolventGraphSplice.resolvent
  exact PreparationVacuumYukawaTransport.inverse_commuting _ _
    (FullYSourceResolventGraphSplice.resolvent_isUnit _ (CanonicalPhysicalSpatial.compression_selfAdjoint p F) z nonreal)
    ((show Commute (numberTwoGrade g) (CanonicalPhysicalSpatial.compression p F) from
      by simpa only [actualC] using actualC_numberTwoGrade p F g).sub_right
      ((Commute.one_right _).smul_right z))

private theorem inverse_range {R : Type*} [Ring R] (P Q A U : R)
    (PU : Commute P U) (range : Q*A*P=A*P) : Q*(A*U)*P=(A*U)*P := by
  calc
    _=(Q*A)*(U*P) := by noncomm_ring
    _=(Q*A)*(P*U) := by rw [PU.symm.eq]
    _=(Q*A*P)*U := by noncomm_ring
    _=(A*P)*U := by rw [range]
    _=A*(P*U) := by rw [mul_assoc]
    _=A*(U*P) := by rw [PU.eq]
    _=_ := by rw [mul_assoc]

private theorem inverse_terminal {R : Type*} [Ring R] (P A U : R)
    (PU : Commute P U) (terminal : A*P=0) : (A*U)*P=0 := by
  rw [mul_assoc,PU.symm.eq,←mul_assoc,terminal,zero_mul]

private theorem three_step_nilpotent {R : Type*} [Ring R] (P Q T B : R)
    (first : Q*B*P=B*P) (second : T*B*Q=B*Q) (terminal : B*T=0) :
    B*B*B*(P+Q+T)=0 := by
  have one : B*B*B*P=0 := by
    calc
      _=B*B*(B*P) := by noncomm_ring
      _=B*B*(Q*B*P) := by rw [first]
      _=B*(B*Q)*B*P := by noncomm_ring
      _=B*(T*B*Q)*B*P := by rw [second]
      _=(B*T)*B*Q*B*P := by noncomm_ring
      _=0 := by rw [terminal,zero_mul,zero_mul,zero_mul,zero_mul]
  have two : B*B*B*Q=0 := by
    calc
      _=B*B*(B*Q) := by noncomm_ring
      _=B*B*(T*B*Q) := by rw [second]
      _=B*(B*T)*B*Q := by noncomm_ring
      _=0 := by rw [terminal,mul_zero,zero_mul,zero_mul]
  have three : B*B*B*T=0 := by rw [mul_assoc (B*B) B T,terminal,mul_zero]
  rw [mul_add,mul_add,one,two,three,add_zero,add_zero]

private theorem inverse_three_return {R : Type*} [Ring R] (P D A U V : R)
    (free : D*U=1) (full : V*(D+A)=1) (terminal : A*U*A*U*A*U*P=0) :
    V*P=(U-U*A*U+U*A*U*A*U)*P := by
  have generated : (D+A)*(U-U*A*U+U*A*U*A*U)*P=P := by
    calc
      _=(D*U)*P+A*U*P-((D*U)*A*U*P+A*U*A*U*P)+
        ((D*U)*A*U*A*U*P+A*U*A*U*A*U*P) := by noncomm_ring
      _=P := by rw [free,terminal]; noncomm_ring
  calc
    _=V*((D+A)*(U-U*A*U+U*A*U*A*U)*P) := by rw [generated]
    _=(V*(D+A))*((U-U*A*U+U*A*U*A*U)*P) := by noncomm_ring
    _=_ := by rw [full,one_mul]

/-- Three alternating original C-Green/Yukawa words, generated on the complete actual N2 sector. -/
theorem actual_resolvent_N2_return (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index)
    (z : ℂ) (nonreal : z.im≠0) :
    jointResolvent p F z 0*numberTwoProjection=
      (CanonicalPhysicalResolvent.finiteResolvent p F z-
        CanonicalPhysicalResolvent.finiteResolvent p F z*actualA p F*CanonicalPhysicalResolvent.finiteResolvent p F z+
        CanonicalPhysicalResolvent.finiteResolvent p F z*actualA p F*CanonicalPhysicalResolvent.finiteResolvent p F z*
          actualA p F*CanonicalPhysicalResolvent.finiteResolvent p F z)*numberTwoProjection := by
  let U:=CanonicalPhysicalResolvent.finiteResolvent p F z
  have terminal : actualA p F*U*actualA p F*U*actualA p F*U*numberTwoProjection=0 := by
    have computed:=three_step_nilpotent (numberTwoGrade 0) (numberTwoGrade 1) (numberTwoGrade 2) (actualA p F*U)
      (inverse_range _ _ _ _ (inverse_preserves p F z nonreal 0) (actualA_N2G0_range p F))
      (inverse_range _ _ _ _ (inverse_preserves p F z nonreal 1) (actualA_N2G1_range p F))
      (inverse_terminal _ _ _ (inverse_preserves p F z nonreal 2) (actualA_N2G2_zero p F))
    simpa only [numberTwoProjection,mul_assoc] using computed
  have free:=FullYSourceResolventGraphSplice.resolvent_right (actualC p F) (actualC_symmetric p F) z nonreal
  have free' : (actualC p F-z • 1)*U=1 := by
    simpa only [U,actualC,CanonicalPhysicalResolvent.finiteResolvent] using free
  have full:=sourceMaterialInverse_left p F z nonreal
  rw [actualGenerator_source] at full
  have full' : jointResolvent p F z 0*((actualC p F-z • 1)+actualA p F)=1 := by
    simpa only [sub_add_eq_add_sub] using full
  exact inverse_three_return numberTwoProjection (actualC p F-z • 1) (actualA p F) U
    (jointResolvent p F z 0) free' full' terminal

end LowEnergy.GaussComposite.ActualDressedNumberZero
