import H0mework.Versions.R9c73a630.Physics.LowEnergy.Quantum.SourceClockYukawaRadialCross
import H0mework.Versions.R9c73a630.Physics.LowEnergy.Quantum.SourceClockYukawaGradedGamma

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.SourceClockYukawaRadialMixedGamma
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussNativeForm GaussNativeEnergy
open GaussDiagonalHistory GaussUnitaryHistory GaussLiveMomentum GaussRadialDomain GaussYukawaCoefficient
open SourceQuantumConfigurationHilbert SourceMixedNativeReturn SourceScalarDoubleCurrent
open SourceScalarPairedTransport SourceScalarPositiveBulkWard SourceClockYukawaTail SourceCutoffDilationWard
open SourceClockYukawaNormalizedCurrent SourceRelativePowerTail SourceHardyRetardedTail SourceRetardedForcingTail
open SourceJointResidualEnergy SourceFourPoleEnergyClosed SourceScalarSignedInverseReturn SourceEscapeSeedTail
open FullYSourceResolventGraphSplice SourceResolventBandLimit MeasureTheory Filter
open scoped InnerProductSpace Topology
abbrev End := QuantumTest →ₗ[ℂ] QuantumTest
abbrev Op := H →L[ℂ] H
attribute [local irreducible] inverseRadius fullAction state compressionCore defectAction normalizedAction
  finiteResolvent GaussGradedCompression.compression actualIncrement sourceB relativeTail

section Algebra
variable {A : Type*} [Ring A]
private def comm (x y : A) : A := x*y-y*x
private theorem inverse_mixed (L R S X : A) (hL : L*R=1) (hR : R*L=1) :
    R*comm L X*R*comm L S*R+R*comm L S*R*comm L X*R-R*comm (comm L S) X*R=
      comm (comm R S) X := by
  have hrx (a : A) : R*(L*a)=a := by rw [←mul_assoc,hR,one_mul]
  have hlx (a : A) : L*(R*a)=a := by rw [←mul_assoc,hL,one_mul]
  unfold comm
  noncomm_ring [hrx,hlx,hL]

private theorem mixed_gamma_algebra (R S X M : A) (hM : M=comm (comm R S) X) :
    R*X*R*S=R^2*(S*X)-R*S*R*X+R*(X*S)*R-R*M := by
  rw [hM]
  unfold comm
  noncomm_ring
private theorem mixed_gamma_source_algebra (R S X B M : A) (hM : M=comm (comm R S) X)
    (hSX : S*X=B) (hXS : X*S=B) :
    R*X*R*S=R^2*B-R*S*R*X+R*B*R-R*M := by
  have h := mixed_gamma_algebra R S X M hM
  rw [hSX,hXS] at h
  exact h
end Algebra
attribute [local irreducible] comm

def cutoffCurrent (sharp : Bool) (m ell : ℕ) (F : Index) : Op :=
  GaussGradedCompression.compression F*actualIncrement sharp m ell-
    actualIncrement sharp m ell*GaussGradedCompression.compression F

def radialCurrent (F : Index) : Op :=
  GaussGradedCompression.compression F*inverseRadius-inverseRadius*GaussGradedCompression.compression F

def mixedCurvature (sharp : Bool) (m ell : ℕ) (F : Index) : Op :=
  radialCurrent F*actualIncrement sharp m ell-actualIncrement sharp m ell*radialCurrent F

def mixedResponse (sharp : Bool) (m ell : ℕ) (F : Index) (z : ℂ) : Op :=
  let R := finiteResolvent F z
  R*cutoffCurrent sharp m ell F*R*radialCurrent F*R+
    R*radialCurrent F*R*cutoffCurrent sharp m ell F*R-R*mixedCurvature sharp m ell F*R

attribute [local irreducible] cutoffCurrent radialCurrent mixedCurvature mixedResponse

private theorem actual_mixed_response (sharp : Bool) (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im≠0) :
    mixedResponse sharp m ell F z=
      comm (comm (finiteResolvent F z) inverseRadius) (actualIncrement sharp m ell) := by
  have hL : (GaussGradedCompression.compression F-z • 1)*finiteResolvent F z=1 := by
    simpa only [finiteResolvent] using resolvent_right (GaussGradedCompression.compression F)
      (GaussGradedCompression.compression_selfAdjoint F) z hz
  have hR : finiteResolvent F z*(GaussGradedCompression.compression F-z • 1)=1 := by
    simpa only [finiteResolvent] using resolvent_left (GaussGradedCompression.compression F)
      (GaussGradedCompression.compression_selfAdjoint F) z hz
  have hS : comm (GaussGradedCompression.compression F-z • 1) inverseRadius=radialCurrent F := by
    simp only [comm,radialCurrent,sub_mul,mul_sub,smul_mul_assoc,mul_smul_comm,one_mul,mul_one]
    abel
  have hA : comm (GaussGradedCompression.compression F-z • 1) (actualIncrement sharp m ell)=cutoffCurrent sharp m ell F := by
    simp only [comm,cutoffCurrent,sub_mul,mul_sub,smul_mul_assoc,mul_smul_comm,one_mul,mul_one]
    abel
  have h := inverse_mixed (A := Op) (GaussGradedCompression.compression F-z • 1) (finiteResolvent F z)
    inverseRadius (actualIncrement sharp m ell) hL hR
  rw [hA,hS] at h
  simpa only [mixedResponse,mixedCurvature,comm] using h

private theorem inverse_increment (sharp : Bool) (m ell : ℕ) :
    inverseRadius*actualIncrement sharp m ell=sourceB sharp*relativeTail m ell := by
  apply GaussYukawaGrade.core_ext
  intro f
  change inverseRadius (actualIncrement sharp m ell (embed f))=
    sourceB sharp (relativeTail m ell (embed f))
  rw [literal_increment_core,literal_full_return,Module.End.mul_apply,inverse_core,
    SourceMixedNativeReturn.theta_core]
  simpa only [normalizedAction,Module.End.mul_apply] using
    (original_normalized_core sharp (thetaAction m ell f)).symm

private theorem increment_inverse (sharp : Bool) (m ell : ℕ) :
    actualIncrement sharp m ell*inverseRadius=sourceB sharp*relativeTail m ell := by
  have hc : Commute inverseRadius (actualIncrement sharp m ell) := by
    apply GaussYukawaGrade.core_ext
    intro f
    change inverseRadius (actualIncrement sharp m ell (embed f))=
      actualIncrement sharp m ell (inverseRadius (embed f))
    rw [inverse_core,literal_increment_core,literal_increment_core]
    simp only [literal_full_return,Module.End.mul_apply,inverse_core]
    congr 1
    have hy : Commute (fullAction sharp) inverseAction := by
      unfold fullAction
      cases sharp
      · exact GaussRadialHamiltonian.original_commutes
      · exact GaussRadialHamiltonian.adjoint_commutes
    have ht : Commute (thetaAction m ell) inverseAction := by
      unfold thetaAction
      exact ((Commute.one_left inverseAction).sub_left (Commute.refl inverseAction)).pow_left _ |>.sub_left
        (((Commute.one_left inverseAction).sub_left (Commute.refl inverseAction)).pow_left _)
    exact LinearMap.congr_fun (hy.mul_left ht).eq.symm f
  exact hc.eq.symm.trans (inverse_increment sharp m ell)

/-- The mixed source word is consumed at the original Gamma insertion. All
remaining endpoint insertions contain bounded B or a fixed cutoff source. -/
theorem actual_mixed_gamma_operator (sharp : Bool) (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im≠0) :
    finiteResolvent F z*actualIncrement sharp m ell*finiteResolvent F z*inverseRadius=
      (finiteResolvent F z)^2*(sourceB sharp*relativeTail m ell)-
      finiteResolvent F z*inverseRadius*finiteResolvent F z*actualIncrement sharp m ell+
      finiteResolvent F z*(sourceB sharp*relativeTail m ell)*finiteResolvent F z-
      finiteResolvent F z*mixedResponse sharp m ell F z := by
  exact mixed_gamma_source_algebra (finiteResolvent F z) inverseRadius (actualIncrement sharp m ell)
    (sourceB sharp*relativeTail m ell) (mixedResponse sharp m ell F z)
    (actual_mixed_response sharp m ell F z hz) (inverse_increment sharp m ell) (increment_inverse sharp m ell)

end LowEnergy.SourceClockYukawaRadialMixedGamma
