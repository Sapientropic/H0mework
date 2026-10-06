import H0mework.Versions.AD.Physics.LowEnergy.Quantum.SourceClockYukawaQ8WholeCurrent
import H0mework.Versions.AD.Physics.LowEnergy.Quantum.SourceClockYukawaJointDefectForce

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1500000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.SourceClockYukawaQ8CoherentDefect
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussNativeForm GaussNativeEnergy
open GaussDiagonalHistory GaussUnitaryHistory GaussRadialDomain
open SourceQuantumConfigurationHilbert SourceMixedNativeReturn SourceScalarDoubleCurrent SourceScalarPairedTransport
open SourceClockYukawaSpinClosure SourceClockYukawaSpinJointForce SourceClockYukawaJointDefectForce
open SourceClockYukawaQ8WholeCurrent SourceClockYukawaCubicCurrent
open scoped InnerProductSpace
abbrev End := QuantumTest →ₗ[ℂ] QuantumTest
attribute [local irreducible] diagonalAction compressionCore defectAction resolventCore

/-- The original Hamiltonian radial forcing and the single coherent defect share the same input and resolvent. -/
def coherentForcing (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im≠0) (g : diagonal.domain) : QuantumTest :=
  SourceInverseNeutralScalarCurrent.radialCurrent m ell (radialMap F z hz (inputCore g))+
    thetaAction m ell (GaussRadialHamiltonian.radialAction (resolventCore F z hz (inputCore g)))+
    thetaAction m ell (defectRadialMap F z hz (inputCore g))

/-- The complete moving defect is kept as one coherent radial response before any pairing or norm. -/
theorem actual_Q8_coherent_forcing (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im≠0) (g : diagonal.domain) :
    windowForcing m ell F z hz g+defectAction F (windowState m ell F z hz g)=coherentForcing m ell F z hz g := by
  have hm (J T K S D R : End) :
      (J-bracket D T)*bracket S R+T*(K-bracket D S)*R+D*T*bracket S R=
        J*bracket S R+T*K*R+T*(S*D*R-D*R*S) := by
    unfold bracket
    noncomm_ring
  have h := LinearMap.congr_fun
    (hm (SourceInverseNeutralScalarCurrent.radialCurrent m ell) (thetaAction m ell)
      GaussRadialHamiltonian.radialAction inverseAction (defectAction F) (resolventCore F z hz)) (inputCore g)
  exact h

private theorem compression_pair (F : Index) (p q : QuantumTest) :
    sourcePair p (compressionCore F q)=sourcePair (compressionCore F p) q := by
  have he (f : QuantumTest) : embed (compressionCore F f)=GaussGradedCompression.compression F (embed f) := by
    unfold compressionCore
    exact congrArg Subtype.val (coreEquiv.apply_symm_apply _)
  simp only [sourcePair,he]
  exact (GaussGradedCompression.compression_pair F _ _).symm
private theorem defect_pair (F : Index) (p q : QuantumTest) :
    sourcePair p (defectAction F q)=sourcePair (defectAction F p) q := by
  unfold defectAction
  simp only [LinearMap.sub_apply,sourcePair,map_sub,inner_sub_right,inner_sub_left]
  exact congrArg₂ (·-·) (diagonalAction_pair p q) (compression_pair F p q)

private theorem paired_symm {A B : End} (h : GaussCoframeForm.Paired A B) : GaussCoframeForm.Paired B A := by
  intro p q
  have h' := congrArg (starRingEnd ℂ) (h q p)
  simpa only [sourcePair,inner_conj_symm] using h'.symm
private theorem paired_product {A Aa B Ba : End} (hA : GaussCoframeForm.Paired A Aa)
    (hB : GaussCoframeForm.Paired B Ba) : GaussCoframeForm.Paired (A*B) (Ba*Aa) := by
  intro p q
  change sourcePair p (A (B q))=sourcePair (Ba (Aa p)) q
  rw [hA,hB]
private theorem q8_pair : GaussCoframeForm.Paired (Q8 false) (Q8 false) := by
  intro p q
  unfold Q8
  simp only [LinearMap.sum_apply,LinearMap.add_apply,Module.End.mul_apply,sourcePair,map_sum,map_add,
    inner_sum,sum_inner,inner_add_right,inner_add_left]
  apply Finset.sum_congr rfl
  intro mu _
  have h := SourceClockYukawaQ8NonScalar.original_spin_coefficient_pair false mu
  exact congrArg₂ (·+·) ((paired_product (paired_symm h) h) p q) ((paired_product h (paired_symm h)) p q)

private theorem defect_current_pair (F : Index) (u : QuantumTest) :
    (sourcePair u (bracket (defectAction F) (Q8 false) u)).im=
      -2*(sourcePair (Q8 false u) (defectAction F u)).im := by
  have h := congrArg Complex.im (pair_conjugate (Q8 false u) (defectAction F u))
  simp only [Complex.conj_im] at h
  simp only [bracket,LinearMap.sub_apply,Module.End.mul_apply,sourcePair,map_sub,inner_sub_right,Complex.sub_im]
  have hp := defect_pair F u (Q8 false u)
  have hq := q8_pair u (defectAction F u)
  simp only [sourcePair] at hp hq h
  rw [hp,hq]
  linarith only [h]

/-- No defect commutator with Q8 remains outside the single same-source radial response. -/
def coherentPrice (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im≠0) (g : diagonal.domain) : ℝ :=
  -(1/2:ℝ)*(sourcePair (windowState m ell F z hz g)
    ((scalarSquareCurrent+bracket GaussMatterCore.matterAction (Q8 false)) (windowState m ell F z hz g))).im-
    (sourcePair (Q8 false (windowState m ell F z hz g)) (coherentForcing m ell F z hz g)).im

/-- The actual whole source price consumes the self-paired defect cancellation before clipping. -/
theorem actual_Q8_coherent_price (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im≠0) (g : diagonal.domain) :
    wholePrice m ell F z hz g=coherentPrice m ell F z hz g := by
  have h := congrArg (fun f => (sourcePair (Q8 false (windowState m ell F z hz g)) f).im)
    (actual_Q8_coherent_forcing m ell F z hz g)
  simp only [sourcePair,map_add,inner_add_right,Complex.add_im] at h
  unfold wholePrice coherentPrice squareCurrent
  simp only [LinearMap.sub_apply,sourcePair,map_sub,inner_sub_right,Complex.sub_im]
  have hd := defect_current_pair F (windowState m ell F z hz g)
  simp only [sourcePair] at hd
  rw [hd]
  linarith only [h]

end LowEnergy.SourceClockYukawaQ8CoherentDefect
