import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedNumberYukawa

set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualDressedNumberSector
open GaussCoreHilbert CanonicalGradedSpatialSource
open PreparationVacuumPhysicalHalfAxis FullYSourceCutoffVolterra
open scoped BigOperators
attribute [local irreducible] actualC actualA numberTwoGrade

private theorem interaction_range {R : Type*} [Ring R] [Algebra ℂ R]
    (P Q U V A : R) (QU : Commute Q U) (PV : Commute P V) (range : Q*A*P=A*P) :
    Q*(U*((-Complex.I) • A)*V)*P=U*((-Complex.I) • A)*V*P := by
  have paid : Q*(U*A*V)*P=U*A*V*P := by
    calc
      _=(Q*U)*A*(V*P) := by noncomm_ring
      _=(U*Q)*A*(P*V) := by rw [QU.eq,PV.symm.eq]
      _=U*(Q*A*P)*V := by noncomm_ring
      _=U*A*P*V := by rw [range];noncomm_ring
      _=U*A*V*P := by noncomm_ring [PV.eq]
  simpa only [mul_smul_comm,smul_mul_assoc] using congrArg (fun B : R=>(-Complex.I) • B) paid

private theorem interaction_zero {R : Type*} [Ring R] [Algebra ℂ R]
    (Q U V A : R) (QV : Commute Q V) (zero : A*Q=0) : (U*((-Complex.I) • A)*V)*Q=0 := by
  have paid : (U*A*V)*Q=0 := by
    calc
      _=U*(A*Q)*V := by noncomm_ring [QV.symm.eq]
      _=0 := by rw [zero,mul_zero,zero_mul]
  simpa only [mul_smul_comm,smul_mul_assoc,smul_zero] using congrArg (fun B : R=>(-Complex.I) • B) paid

theorem actual_interaction_N2G0_range (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) (t : ℝ) :
    numberTwoGrade 1*interaction (actualC p F) (actualA p F) t*numberTwoGrade 0=
      interaction (actualC p F) (actualA p F) t*numberTwoGrade 0 :=
  interaction_range _ _ _ _ _
    (SourceFiniteUnitary.time_commutes _ _ (actualC_numberTwoGrade p F 1) t)
    (SourceFiniteUnitary.time_commutes _ _ (actualC_numberTwoGrade p F 0) (-t))
    (actualA_N2G0_range p F)

theorem actual_interaction_N2G1_range (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) (t : ℝ) :
    numberTwoGrade 2*interaction (actualC p F) (actualA p F) t*numberTwoGrade 1=
      interaction (actualC p F) (actualA p F) t*numberTwoGrade 1 :=
  interaction_range _ _ _ _ _
    (SourceFiniteUnitary.time_commutes _ _ (actualC_numberTwoGrade p F 2) t)
    (SourceFiniteUnitary.time_commutes _ _ (actualC_numberTwoGrade p F 1) (-t))
    (actualA_N2G1_range p F)

theorem actual_interaction_N2G2_zero (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) (t : ℝ) :
    interaction (actualC p F) (actualA p F) t*numberTwoGrade 2=0 :=
  interaction_zero _ _ _ _
    (SourceFiniteUnitary.time_commutes _ _ (actualC_numberTwoGrade p F 2) (-t))
    (actualA_N2G2_zero p F)

end LowEnergy.GaussComposite.ActualDressedNumberSector
