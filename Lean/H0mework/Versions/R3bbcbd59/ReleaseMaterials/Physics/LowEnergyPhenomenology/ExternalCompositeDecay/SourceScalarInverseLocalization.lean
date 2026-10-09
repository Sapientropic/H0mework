import H0mework.Versions.R3bbcbd59.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceScalarInverseRetardedBudget
import H0mework.Versions.R3bbcbd59.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceScalarAffineMixedJets

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
set_option synthInstance.maxHeartbeats 200000
noncomputable section
namespace LowEnergy.InverseVolumeLocalizationAlgebra
open InverseVolumeWardAlgebra
variable {R : Type*} [Ring R] [Algebra ℂ R]

def jordan (A B : R) : R := (1/2 : ℂ) • (A*B+B*A)
private theorem jordan_add_left (A B T : R) : jordan (A+B) T=jordan A T+jordan B T := by
  simp only [jordan,add_mul,mul_add,smul_add]
  abel
private theorem jordan_sub_left (A B T : R) : jordan (A-B) T=jordan A T-jordan B T := by
  simp only [jordan,sub_mul,mul_sub,smul_add,smul_sub]
  abel
private theorem jordan_smul_left (a : ℂ) (A T : R) : jordan (a • A) T=a • jordan A T := by
  simp only [jordan,smul_mul_assoc,mul_smul_comm,←smul_add]
  exact smul_comm _ _ _
private theorem jordan_delta (d : R →ₗ[ℂ] R)
    (hd : ∀ A B,d (A*B)=d A*B+A*d B) (A T : R) :
    d (jordan A T)=jordan (d A) T+jordan A (d T) := by
  simp only [jordan,map_smul,map_add,hd,smul_add]
  abel
private theorem jordan_zero_right (A : R) : jordan A 0=0 := by simp [jordan]

def gaugePolynomial (g : R →ₗ[ℂ] R) (A : R) : R :=
  g (g A)-(5 : ℂ) • g A+(4 : ℂ) • A

def firstContact (p g c : R →ₗ[ℂ] R) (γ : ℂ) (A : R) : R :=
  gaugePolynomial g A+γ • ((2 : ℂ) • p (inverseLocalPolynomial c A)-
    (3 : ℂ) • inverseLocalPolynomial c A)

def secondContact (c : R →ₗ[ℂ] R) (γ : ℂ) (A : R) : R :=
  γ • inverseLocalPolynomial c A

private theorem invariant_jordan (d : R →ₗ[ℂ] R)
    (hd : ∀ A B,d (A*B)=d A*B+A*d B) (A T : R) (hT : d T=0) :
    d (jordan A T)=jordan (d A) T := by
  rw [jordan_delta d hd,hT,jordan_zero_right,add_zero]

private theorem local_jordan (c : R →ₗ[ℂ] R)
    (hc : ∀ A B,c (A*B)=c A*B+A*c B) (A T : R) (hT : c T=0) :
    inverseLocalPolynomial c (jordan A T)=jordan (inverseLocalPolynomial c A) T := by
  simp only [inverseLocalPolynomial,invariant_jordan c hc _ T hT,jordan_add_left,jordan_smul_left]

private theorem gauge_jordan (g : R →ₗ[ℂ] R)
    (hg : ∀ A B,g (A*B)=g A*B+A*g B) (A T : R) (hT : g T=0) :
    gaugePolynomial g (jordan A T)=jordan (gaugePolynomial g A) T := by
  simp only [gaugePolynomial,invariant_jordan g hg _ T hT,
    jordan_add_left,jordan_sub_left,jordan_smul_left]

private theorem gauge_add (g : R →ₗ[ℂ] R) (A B : R) :
    gaugePolynomial g (A+B)=gaugePolynomial g A+gaugePolynomial g B := by
  simp only [gaugePolynomial,map_add,smul_add]
  abel

private theorem affine_jordan (p : R →ₗ[ℂ] R)
    (hp : ∀ A B,p (A*B)=p A*B+A*p B) (A T : R) :
    affinePolynomial p (jordan A T)=jordan (affinePolynomial p A) T+
      jordan ((2 : ℂ) • p A-(3 : ℂ) • A) (p T)+jordan A (p (p T)) := by
  simp only [affinePolynomial,jordan_delta p hp,map_add,
    jordan_add_left,jordan_sub_left,jordan_smul_left]
  module

/-- The original inverse polynomial acts on both one-sided source legs, with exactly two cutoff jets. -/
theorem inverse_ward_jordan (p g c : R →ₗ[ℂ] R) (γ : ℂ)
    (hp : ∀ A B,p (A*B)=p A*B+A*p B)
    (hg : ∀ A B,g (A*B)=g A*B+A*g B)
    (hc : ∀ A B,c (A*B)=c A*B+A*c B)
    (A T : R) (hgT : g T=0) (hcT : c T=0) (hgpT : g (p T)=0) :
    inverseWard p g c γ (jordan A T)=jordan (inverseWard p g c γ A) T+
      jordan (firstContact p g c γ A) (p T)+
      jordan (secondContact c γ A) (p (p T)) := by
  have hj : p (jordan A T)-g (jordan A T)=
      jordan (p A-g A) T+jordan A (p T) := by
    rw [jordan_delta p hp,invariant_jordan g hg A T hgT,jordan_sub_left]
    abel
  have hm : mixedPolynomial p g (jordan A T)=
      jordan (mixedPolynomial p g A) T+jordan (gaugePolynomial g A) (p T) := by
    change gaugePolynomial g (p (jordan A T)-g (jordan A T))=_
    rw [hj,gauge_add,gauge_jordan g hg _ T hgT,gauge_jordan g hg _ (p T) hgpT]
    rfl
  rw [inverseWard,hm,local_jordan c hc A T hcT,affine_jordan p hp]
  simp only [inverseWard,firstContact,secondContact,jordan_add_left,jordan_smul_left]
  module

end LowEnergy.InverseVolumeLocalizationAlgebra

namespace LowEnergy.SourceScalarInverseLocalization
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussNativeForm GaussHistoryHilbert
open GaussDiagonalHistory SourcePhysicalKineticSquare SourceScalarInverseBulk
open SourceScalarVirialBulk SourceScalarGaugeScale SourceHamiltonianScaleJet
open SourceScalarInverseRetardedBudget InverseVolumeLocalizationAlgebra
open SourceCoframeVolumeCurrent SourceQuantumConfigurationHilbert SourceQuantumScalarChart
open SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open SourceDilationRemainder GaussNativeEnergy SourceCoframeVolume
private local instance scalarTestBoundedSMul : IsBoundedSMul ℂ ℂ := NormedSpace.toIsBoundedSMul
attribute [local irreducible] GaussDiagonalHistory.diagonalAction
abbrev End := QuantumTest →ₗ[ℂ] QuantumTest

private theorem phi_product (A B : End) : deltaPhi (A*B)=deltaPhi A*B+A*deltaPhi B := by
  change phiEulerAction*(A*B)-(A*B)*phiEulerAction=
    (phiEulerAction*A-A*phiEulerAction)*B+A*(phiEulerAction*B-B*phiEulerAction)
  noncomm_ring
private theorem gauge_product (A B : End) : deltaGauge (A*B)=deltaGauge A*B+A*deltaGauge B := by
  change SourceGaugeRadialPair.gaugeEulerAction*(A*B)-(A*B)*SourceGaugeRadialPair.gaugeEulerAction=
    (SourceGaugeRadialPair.gaugeEulerAction*A-A*SourceGaugeRadialPair.gaugeEulerAction)*B+
      A*(SourceGaugeRadialPair.gaugeEulerAction*B-B*SourceGaugeRadialPair.gaugeEulerAction)
  noncomm_ring
private theorem coframe_product (A B : End) :
    scaleDerivative (A*B)=scaleDerivative A*B+A*scaleDerivative B := by
  rw [←SourceGaugeCoframeJets.K_commutator,←SourceGaugeCoframeJets.K_commutator,
    ←SourceGaugeCoframeJets.K_commutator]
  noncomm_ring

private theorem theta_pair (m ell : ℕ) (f g : QuantumTest) :
    sourcePair f (theta m ell g)=sourcePair (theta m ell f) g := multiply_pair _ _ _ _

private theorem theta_gauge_flow (m ell : ℕ) (t : ℝ) (f : QuantumTest) :
    SourceGaugeScaleTransport.coreFlow t (theta m ell f)=
      theta m ell (SourceGaugeScaleTransport.coreFlow t f) := by
  apply DFunLike.ext
  intro z
  have ht : SourceNativeCutoffContact.theta m ell
      (SourceGaugeScaleTransport.scaleEquiv t z)=SourceNativeCutoffContact.theta m ell z := rfl
  change (Real.exp (18*t) : ℂ) •
    ((SourceNativeCutoffContact.theta m ell (SourceGaugeScaleTransport.scaleEquiv t z) : ℂ) •
      f (SourceGaugeScaleTransport.scaleEquiv t z))=
    (SourceNativeCutoffContact.theta m ell z : ℂ) •
      ((Real.exp (18*t) : ℂ) • f (SourceGaugeScaleTransport.scaleEquiv t z))
  rw [ht,smul_comm]

theorem original_theta_gauge (m ell : ℕ) : deltaGauge (theta m ell)=0 := by
  rw [←SourceGaugeScaleTransport.generator_commutator]
  apply LinearMap.ext
  intro f
  apply GaussCoreLabel.pair_separates
  intro k
  have hL := SourceGaugeScaleTransport.weak_flow_derivative k (theta m ell f) 0
  have hR := SourceGaugeScaleTransport.weak_flow_derivative (theta m ell k) f 0
  have he (t : ℝ) : sourcePair k (SourceGaugeScaleTransport.coreFlow t (theta m ell f))=
      sourcePair (theta m ell k) (SourceGaugeScaleTransport.coreFlow t f) := by
    rw [theta_gauge_flow,theta_pair]
  have h := (hL.congr_of_eventuallyEq (Filter.Eventually.of_forall (fun t => (he t).symm))).unique hR
  simp only [SourceGaugeScaleTransport.coreFlow_zero] at h
  rw [←theta_pair m ell k (SourceGaugeScaleTransport.generator f)] at h
  change sourcePair k (SourceGaugeScaleTransport.generator (theta m ell f)-
    theta m ell (SourceGaugeScaleTransport.generator f))=sourcePair k 0
  simp only [sourcePair,map_sub,map_zero,inner_sub_right,inner_zero_right] at h ⊢
  exact sub_eq_zero.mpr h

theorem original_theta_coframe (m ell : ℕ) : scaleDerivative (theta m ell)=0 := by
  have h : Commute dilation (theta m ell) := by
    rw [show theta m ell=(1-GaussRadialDomain.inverseAction)^(m+1)-
        (1-GaussRadialDomain.inverseAction)^(ell+1) from
      SourceNativeCutoffContact.theta_action_polynomial m ell]
    exact (((Commute.one_right dilation).sub_right SourceCutoffDilationWard.inverse_dilation).pow_right
      (m+1)).sub_right
      (((Commute.one_right dilation).sub_right SourceCutoffDilationWard.inverse_dilation).pow_right (ell+1))
  change (3*Complex.I/2) • (dilation*theta m ell-theta m ell*dilation)=0
  rw [h.eq,sub_self,smul_zero]

attribute [local irreducible] SourceScalarVirialBulk.deltaPhi SourceScalarGaugeScale.deltaGauge
  SourceHamiltonianScaleJet.scaleDerivative SourceScalarVirialBulk.positiveBulk

private theorem gauge_phi (A : End) : deltaGauge (deltaPhi A)=deltaPhi (deltaGauge A) := by
  have hp (B : End) : deltaPhi B=SourceScalarAffineScaleTransport.generator*B-
      B*SourceScalarAffineScaleTransport.generator :=
    (SourceScalarAffineScaleTransport.generator_commutator B).symm
  have hg (B : End) : deltaGauge B=SourceGaugeScaleTransport.generator*B-
      B*SourceGaugeScaleTransport.generator :=
    (SourceGaugeScaleTransport.generator_commutator B).symm
  have hc := SourceScalarAffineMixedJets.generators_affine_gauge.eq
  change SourceScalarAffineScaleTransport.generator*SourceGaugeScaleTransport.generator=
    SourceGaugeScaleTransport.generator*SourceScalarAffineScaleTransport.generator at hc
  have hleft := congrArg (fun B : End => B*A) hc
  have hright := congrArg (fun B : End => A*B) hc
  rw [hg,hp,hp,hg]
  linear_combination (norm := noncomm_ring) -hleft+hright

theorem original_square_gauge (m ell : ℕ) : deltaGauge (square m ell)=0 := by
  rw [square,gauge_product,original_theta_gauge,zero_mul,mul_zero,add_zero]
theorem original_square_coframe (m ell : ℕ) : scaleDerivative (square m ell)=0 := by
  rw [square,coframe_product,original_theta_coframe,zero_mul,mul_zero,add_zero]
theorem original_square_mixed (m ell : ℕ) : deltaGauge (deltaPhi (square m ell))=0 := by
  rw [gauge_phi,original_square_gauge,map_zero]

def firstSourceContact : End := firstContact deltaPhi deltaGauge scaleDerivative
  (vacuumJetCoefficient : ℂ) inverseSymmetricScale
def secondSourceContact : End := secondContact scaleDerivative
  (vacuumJetCoefficient : ℂ) inverseSymmetricScale

private theorem local_add (A B : End) :
    InverseVolumeWardAlgebra.inverseLocalPolynomial scaleDerivative (A+B)=
      InverseVolumeWardAlgebra.inverseLocalPolynomial scaleDerivative A+
        InverseVolumeWardAlgebra.inverseLocalPolynomial scaleDerivative B := by
  simp only [InverseVolumeWardAlgebra.inverseLocalPolynomial,map_add,smul_add]
  abel
private theorem local_smul (a : ℂ) (A : End) :
    InverseVolumeWardAlgebra.inverseLocalPolynomial scaleDerivative (a • A)=
      a • InverseVolumeWardAlgebra.inverseLocalPolynomial scaleDerivative A := by
  simp only [InverseVolumeWardAlgebra.inverseLocalPolynomial,map_smul]
  module

/-- The second contact loses the entire nonlocal source action and both coframe inverse weights. -/
theorem original_inverse_local_polynomial :
    InverseVolumeWardAlgebra.inverseLocalPolynomial scaleDerivative inverseSymmetricScale=
      (48 : ℂ) • (inverseVolumeAction*localAction) := by
  have hs : inverseSymmetricScale=inverseVolumeAction*diagonalAction+
      (1/2 : ℂ) • (diagonalAction*inverseVolumeAction-inverseVolumeAction*diagonalAction) := by
    unfold inverseSymmetricScale
    module
  have hk : InverseVolumeWardAlgebra.inverseLocalPolynomial scaleDerivative
      (diagonalAction*inverseVolumeAction-inverseVolumeAction*diagonalAction)=0 := by
    simp only [InverseVolumeWardAlgebra.inverseLocalPolynomial,
      original_inverse_volume_current_weight,map_smul]
    module
  have hlocal : InverseVolumeWardAlgebra.localPolynomial scaleDerivative diagonalAction=
      (48 : ℂ) • localAction := by
    simpa only [InverseVolumeWardAlgebra.localPolynomial] using source_local_from_scale_jet
  rw [hs,local_add,local_smul,hk,smul_zero,add_zero,
    InverseVolumeWardAlgebra.inverse_local_mul scaleDerivative coframe_product
      inverseVolumeAction diagonalAction inverse_coframe,hlocal,mul_smul_comm]

theorem original_second_contact_source :
    secondSourceContact=(48*(vacuumJetCoefficient : ℂ)) • (inverseVolumeAction*localAction) := by
  rw [secondSourceContact,secondContact,original_inverse_local_polynomial,smul_smul]
  congr 1
  ring

private theorem inverse_current_gauge :
    deltaGauge (diagonalAction*inverseVolumeAction-inverseVolumeAction*diagonalAction)=0 := by
  rw [original_inverse_current,map_smul]
  simp only [gauge_product,inverse_gauge,SourceScalarPositiveBulkWard.original_dilation_gauge,
    zero_mul,mul_zero,add_zero,smul_zero]

private theorem inverse_gauge_polynomial :
    gaugePolynomial deltaGauge inverseSymmetricScale=
      inverseVolumeAction*gaugePolynomial deltaGauge diagonalAction+
      (2 : ℂ) • (diagonalAction*inverseVolumeAction-inverseVolumeAction*diagonalAction) := by
  have hs : inverseSymmetricScale=inverseVolumeAction*diagonalAction+
      (1/2 : ℂ) • (diagonalAction*inverseVolumeAction-inverseVolumeAction*diagonalAction) := by
    unfold inverseSymmetricScale
    module
  have hv (A : End) : deltaGauge (inverseVolumeAction*A)=inverseVolumeAction*deltaGauge A := by
    rw [gauge_product,inverse_gauge,zero_mul,zero_add]
  simp only [gaugePolynomial,hs,map_add,map_smul,hv,inverse_current_gauge,
    smul_zero,add_zero,mul_add,mul_sub,mul_smul_comm]
  module

/-- The first contact keeps the original gauge polynomial and the exact signed coframe current. -/
theorem original_first_contact_source :
    firstSourceContact=
      inverseVolumeAction*(gaugePolynomial deltaGauge diagonalAction+
        (48*(vacuumJetCoefficient : ℂ)) • ((2 : ℂ) • deltaPhi localAction-(3 : ℂ) • localAction))+
      (3*Complex.I*(sourceTime 0 : ℂ)/2) • (inverseVolumeAction*dilation*inverseVolumeAction) := by
  rw [firstSourceContact,firstContact,original_inverse_local_polynomial,
    inverse_gauge_polynomial,original_inverse_current]
  simp only [map_smul,phi_product,inverse_phi,zero_mul,zero_add,mul_add,mul_sub,
    mul_smul_comm,smul_smul]
  module

/-- The surviving second contact is the literal scalar radius, with no remaining V weight. -/
theorem original_second_contact_apply (f : QuantumTest) (z : SourceCoordinateSlice) :
    secondSourceContact f z=
      ((48*vacuumJetCoefficient*sourceTime 0*(‖(z.2.1 : Scalar)‖^2+3) : ℝ) : ℂ) • f z := by
  rw [original_second_contact_source]
  change (48*(vacuumJetCoefficient : ℂ)) •
    ((reciprocalVolume z : ℂ) • ((localPotential z : ℂ) • f z))=_
  by_cases hz : z∈physicalChart
  · have hv : reciprocalVolume z*localPotential z=
        sourceTime 0*(‖(z.2.1 : Scalar)‖^2+3) := by
      unfold reciprocalVolume localPotential GaussCoframeForm.volumePotential
      rw [real_inner_self_eq_norm_sq]
      field_simp [(volume_pos ⟨z,hz⟩).ne']
    have hvC := congrArg Complex.ofReal hv
    simp only [smul_smul]
    congr 1
    push_cast at hvC ⊢
    linear_combination (48*(vacuumJetCoefficient : ℂ))*hvC
  · rw [image_eq_zero_of_notMem_tsupport (fun h => hz (f.tsupport_subset h))]
    simp only [smul_zero]

theorem original_second_contact_ratio :
    0≤48*vacuumJetCoefficient ∧ 48*vacuumJetCoefficient<1 := by
  have hd : 0<‖vacuum‖^2+3 := by positivity
  have he : 48*vacuumJetCoefficient=‖vacuum‖^2/(‖vacuum‖^2+3) := by
    unfold vacuumJetCoefficient
    field_simp
  rw [he]
  exact ⟨div_nonneg (sq_nonneg _) hd.le,(div_lt_one hd).mpr (by linarith)⟩

/-- The actual inverse Ward of the symmetric two-sided source average has only the two original affine cutoff contacts. -/
theorem original_inverse_square_localization (m ell : ℕ) :
    inverseWeightedBulkJet (symmetricCutoff m ell)=
      jordan (inverseVolumeAction*positiveBulk) (square m ell)+
      jordan firstSourceContact (deltaPhi (square m ell))+
      jordan secondSourceContact (deltaPhi (deltaPhi (square m ell))) := by
  have h := inverse_ward_jordan (R := End) deltaPhi deltaGauge scaleDerivative (vacuumJetCoefficient : ℂ)
    phi_product gauge_product coframe_product inverseSymmetricScale (square m ell)
    (original_square_gauge m ell) (original_square_coframe m ell) (original_square_mixed m ell)
  change inverseWeightedBulkJet (symmetricCutoff m ell)=
    jordan (inverseWeightedBulkJet inverseSymmetricScale) (square m ell)+
      jordan firstSourceContact (deltaPhi (square m ell))+
      jordan secondSourceContact (deltaPhi (deltaPhi (square m ell))) at h
  rw [original_inverse_bulk_symmetric_jet] at h
  exact h

end LowEnergy.SourceScalarInverseLocalization
