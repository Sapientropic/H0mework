import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockResponse.SourceActualWeightedCovarianceTailReturn
import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockResponse.SourceActualMixedProjectionJet

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1500000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.ActualMixedCoframeTailPayment
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussDiagonalHistory GaussUnitaryHistory
open SourceScalarPairedTransport SourceClockYukawaCubicCurrent SourceScalarPositiveBulkWard
open SourceScalarVirialBulk SourceScalarGaugeScale SourceClockPhiSecondBulk SourceHamiltonianScaleJet
open SourceCoframeVolumeCurrent SourcePhysicalKineticSquare SourceScalarInverseBulk
open SourceResolventBandLimit FullYSourceResolventGraphSplice ActualMixedCovarianceTail
open ActualInverseCurrentCoframeReturn ActualWeightedCovarianceTailReturn
open Lean Meta Elab Term
open scoped InnerProductSpace
abbrev End := QuantumTest →ₗ[ℂ] QuantumTest
attribute [local irreducible] resolventCore compressionCore diagonalAction hamiltonianCurrent ownCurrent coreCovariance

private def comm {R : Type*} [Ring R] (a b : R) : R := a*b-b*a
private theorem commuting_derivations {R : Type*} [Ring R] (a b x : R) (hab : a*b=b*a) :
    comm a (comm b x)=comm b (comm a x) := by
  have h₁ := congrArg (fun y : R => y*x) hab
  have h₂ := congrArg (fun y : R => x*y) hab
  unfold comm
  linear_combination (norm := noncomm_ring) h₁-h₂
private theorem comm_product {R : Type*} [Ring R] (a b c : R) :
    comm a (b*c)=comm a b*c+b*comm a c := by unfold comm; noncomm_ring

private theorem phi_coframe_commute : Phi*SourceGaugeCoframeJets.K=SourceGaugeCoframeJets.K*Phi := by
  have h := original_dilation_phi
  rw [←SourceScalarAffineScaleTransport.generator_commutator] at h
  change Phi*SourceCoframeVolumeCurrent.dilation-SourceCoframeVolumeCurrent.dilation*Phi=0 at h
  rw [SourceGaugeCoframeJets.K,mul_smul_comm,smul_mul_assoc,sub_eq_zero.mp h]
private theorem gauge_coframe_commute : Gauge*SourceGaugeCoframeJets.K=SourceGaugeCoframeJets.K*Gauge := by
  have h := original_dilation_gauge
  rw [←SourceGaugeScaleTransport.generator_commutator] at h
  change Gauge*SourceCoframeVolumeCurrent.dilation-SourceCoframeVolumeCurrent.dilation*Gauge=0 at h
  rw [SourceGaugeCoframeJets.K,mul_smul_comm,smul_mul_assoc,sub_eq_zero.mp h]

private theorem coframe_phi (A : End) : scaleDerivative (deltaPhi A)=deltaPhi (scaleDerivative A) := by
  rw [←SourceGaugeCoframeJets.K_commutator,←SourceScalarAffineScaleTransport.generator_commutator,
    ←SourceScalarAffineScaleTransport.generator_commutator,←SourceGaugeCoframeJets.K_commutator]
  exact commuting_derivations _ _ _ phi_coframe_commute.symm
private theorem coframe_gauge (A : End) : scaleDerivative (deltaGauge A)=deltaGauge (scaleDerivative A) := by
  rw [←SourceGaugeCoframeJets.K_commutator,←SourceGaugeScaleTransport.generator_commutator,
    ←SourceGaugeScaleTransport.generator_commutator,←SourceGaugeCoframeJets.K_commutator]
  exact commuting_derivations _ _ _ gauge_coframe_commute.symm

/-- The actual coframe derivative commutes with the original mixed source word. -/
theorem actual_coframe_second_commute (A : End) :
    scaleDerivative (secondJet A)=secondJet (scaleDerivative A) := by
  change scaleDerivative ((deltaPhi A-deltaGauge A)-deltaGauge (deltaPhi A-deltaGauge A))=_
  simp only [secondJet,LinearMap.comp_apply,LinearMap.sub_apply,LinearMap.id_apply,
    map_sub,coframe_phi,coframe_gauge]
  abel

private theorem coframe_product (A B : End) :
    scaleDerivative (A*B)=scaleDerivative A*B+A*scaleDerivative B := by
  rw [←SourceGaugeCoframeJets.K_commutator,←SourceGaugeCoframeJets.K_commutator,
    ←SourceGaugeCoframeJets.K_commutator]
  exact comm_product _ _ _

/-- Source weight minus six removes the entire middle H-current coframe derivative. -/
theorem actual_hamiltonian_coframe_cancellation (A B : End) :
    scaleDerivative (A*hamiltonianCurrent*B)+(6 : ℂ) • (A*hamiltonianCurrent*B)=
      scaleDerivative A*hamiltonianCurrent*B+A*hamiltonianCurrent*scaleDerivative B := by
  have hw : scaleDerivative hamiltonianCurrent=(-6 : ℂ) • hamiltonianCurrent := by
    unfold hamiltonianCurrent
    exact original_inverse_volume_current_weight
  rw [coframe_product,coframe_product,hw]
  simp only [add_mul,mul_smul_comm,smul_mul_assoc]
  module

/-- The complete outer mixed derivative is retained after the native minus-six cancellation. -/
theorem actual_hamiltonian_mixed_coframe_cancellation (A B : End) :
    scaleDerivative (secondJet (A*hamiltonianCurrent*B))+
        (6 : ℂ) • secondJet (A*hamiltonianCurrent*B)=
      secondJet (scaleDerivative A*hamiltonianCurrent*B+A*hamiltonianCurrent*scaleDerivative B) := by
  rw [actual_coframe_second_commute]
  have h := congrArg secondJet (actual_hamiltonian_coframe_cancellation A B)
  simpa only [map_add,map_smul] using h

/-- One whole source return: both outer coframe legs and the full own-current word. -/
def outerCoframeReturn (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im≠0) : End :=
  let A := coreCovariance m ell F z hz
  let R := resolventCore F z hz
  secondJet (scaleDerivative A*hamiltonianCurrent*R+A*hamiltonianCurrent*scaleDerivative R)-
    (scaleDerivative (secondJet (A*ownCurrent F*R))+(6 : ℂ) • secondJet (A*ownCurrent F*R))

/-- Actual covariance and right resolvent share the same coframe gain; no source read or F is replaced. -/
theorem actual_whole_coframe_cancellation (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im≠0) :
    scaleDerivative (mixedCoframeCorrection m ell F z hz)+
      (6 : ℂ) • mixedCoframeCorrection m ell F z hz=outerCoframeReturn m ell F z hz := by
  have hc : compressedCurrent F=hamiltonianCurrent-ownCurrent F := by
    unfold compressedCurrent hamiltonianCurrent ownCurrent defectAction
    noncomm_ring
  unfold mixedCoframeCorrection outerCoframeReturn
  dsimp only
  simp only [hc,mul_sub,sub_mul,map_sub,smul_sub]
  have h := actual_hamiltonian_mixed_coframe_cancellation
    (coreCovariance m ell F z hz) (resolventCore F z hz)
  linear_combination (norm := module) h

elab "paid_whole_coframe_skew%" : term => do
  mkConstWithFreshMVarLevels (Name.str (Name.str (Name.str
    (Name.num `_private.H0mework.Versions.AB.Physics.LowEnergy.Quantum.SourceGaugeCoframeJets 0) "LowEnergy") "SourceGaugeCoframeJets") "K_pair")

/-- The coframe derivative returns to two fixed original inputs, not a moving-family norm claim. -/
theorem actual_whole_coframe_pair_return (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im≠0)
    (f g : QuantumTest) :
    (6 : ℂ)*sourcePair f (mixedCoframeCorrection m ell F z hz g)=
      sourcePair f (outerCoframeReturn m ell F z hz g)+
      sourcePair (SourceGaugeCoframeJets.K f) (mixedCoframeCorrection m ell F z hz g)+
      sourcePair f (mixedCoframeCorrection m ell F z hz (SourceGaugeCoframeJets.K g)) := by
  have h := congrArg (fun T : End => sourcePair f (T g)) (actual_whole_coframe_cancellation m ell F z hz)
  rw [←SourceGaugeCoframeJets.K_commutator] at h
  simp only [LinearMap.add_apply,LinearMap.sub_apply,LinearMap.smul_apply,Module.End.mul_apply,
    sourcePair,map_add,map_sub,map_smul,inner_add_right,inner_sub_right,inner_smul_right] at h
  have hs := (paid_whole_coframe_skew%) f (mixedCoframeCorrection m ell F z hz g)
  change inner ℂ (embed f) (embed (SourceGaugeCoframeJets.K (mixedCoframeCorrection m ell F z hz g)))=
    -inner ℂ (embed (SourceGaugeCoframeJets.K f)) (embed (mixedCoframeCorrection m ell F z hz g)) at hs
  rw [hs] at h
  simp only [sourcePair]
  linear_combination (norm := ring) h

elab "paid_core_coframe_inverse%" : term => do
  mkConstWithFreshMVarLevels (Name.str (Name.str (Name.str
    (Name.num `_private.H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockResponse.SourceActualMixedResolventWard 0) "LowEnergy")
    "ActualMixedResolventWard") "actual_inverse")

private theorem coframe_inverse {R : Type*} [Ring R] (a r k : R)
    (hl : r*a=1) (hr : a*r=1) : comm k r= -r*comm k a*r := by
  have h : r*comm k a*r=r*k*(a*r)-(r*a)*k*r := by unfold comm; noncomm_ring
  rw [hr,hl,mul_one,one_mul] at h
  simp only [neg_mul]
  rw [h]
  unfold comm
  noncomm_ring

private theorem actual_coframe_resolvent (F : Index) (z : ℂ) (hz : z.im≠0) :
    scaleDerivative (resolventCore F z hz)=
      -resolventCore F z hz*scaleDerivative (compressionCore F)*resolventCore F z hz := by
  have hi := (paid_core_coframe_inverse%) F z hz
  have h := coframe_inverse (compressionCore F-z • (1 : End)) (resolventCore F z hz)
    SourceGaugeCoframeJets.K hi.1 hi.2
  have he : comm SourceGaugeCoframeJets.K (compressionCore F-z • (1 : End))=
      comm SourceGaugeCoframeJets.K (compressionCore F) := by
    unfold comm
    simp only [mul_sub,sub_mul,mul_smul_comm,smul_mul_assoc,mul_one,one_mul]
    abel
  rw [he] at h
  simpa only [comm,SourceGaugeCoframeJets.K_commutator] using h

private theorem actual_coframe_theta_zero (m ell : ℕ) :
    scaleDerivative (SourceNativeCutoffContact.thetaAction m ell)=0 := by
  rw [SourceNativeCutoffContact.theta_action_polynomial]
  change scaleDerivative (SourceMixedNativeReturn.thetaAction m ell)=0
  have h := SourceMixedNativeReturn.theta_dilation m ell
  change (3*Complex.I/2) • (SourceCoframeVolumeCurrent.dilation*SourceMixedNativeReturn.thetaAction m ell-
    SourceMixedNativeReturn.thetaAction m ell*SourceCoframeVolumeCurrent.dilation)=0
  rw [h.eq,sub_self,smul_zero]

/-- Three actual inverse insertions replace every bare outer coframe derivative. -/
def inverseCoframeWord (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im≠0) : End :=
  let R := resolventCore F z hz
  let Rstar := resolventCore F (star z) (by simpa only [Complex.star_def,Complex.conj_im,neg_ne_zero] using hz)
  let T := SourceNativeCutoffContact.thetaAction m ell
  let C1 := scaleDerivative (compressionCore F);
  -(Rstar*C1*Rstar*T*T*R*hamiltonianCurrent*R)-
    Rstar*T*T*R*C1*R*hamiltonianCurrent*R-
    Rstar*T*T*R*hamiltonianCurrent*R*C1*R

/-- The complete coframe correction is now an ordered inverse word plus the full OwnDefect. -/
theorem actual_whole_coframe_inverse_normalform (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im≠0) :
    outerCoframeReturn m ell F z hz=
      secondJet (inverseCoframeWord m ell F z hz)-
        (scaleDerivative (secondJet (coreCovariance m ell F z hz*ownCurrent F*resolventCore F z hz))+
          (6 : ℂ) • secondJet (coreCovariance m ell F z hz*ownCurrent F*resolventCore F z hz)) := by
  unfold outerCoframeReturn
  dsimp only
  apply congrArg (fun Q : End => Q-(scaleDerivative
    (secondJet (coreCovariance m ell F z hz*ownCurrent F*resolventCore F z hz))+
      (6 : ℂ) • secondJet (coreCovariance m ell F z hz*ownCurrent F*resolventCore F z hz)))
  apply congrArg secondJet
  unfold coreCovariance inverseCoframeWord
  dsimp only
  simp only [coframe_product,actual_coframe_theta_zero,actual_coframe_resolvent,
    mul_zero,add_zero]
  noncomm_ring

end LowEnergy.ActualMixedCoframeTailPayment
