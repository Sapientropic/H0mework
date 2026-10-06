import H0mework.Versions.AC.Physics.LowEnergy.Quantum.SourceScalarInverseEnergyExchange

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 300000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.SourceInverseFullResponse
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert
open GaussNativeForm GaussNativeEnergy GaussDiagonalHistory GaussUnitaryHistory
open SourceCoframeVolume SourceCoframeVolumeCurrent SourceCoframeDilation SourcePhysicalKineticSquare
open SourceScalarVirialBulk SourceScalarGaugeScale SourceHamiltonianScaleJet
open SourceScalarPositiveBulkWard SourceScalarInverseBulk SourceScalarInverseFullSource
open SourceScalarInverseRetardedBudget SourceScalarInverseLocalization SourceScalarInverseEnergyExchange
open SourceMixedNativeReturn InverseVolumeLocalizationAlgebra InverseVolumeWardAlgebra
open scoped InnerProductSpace
abbrev End := QuantumTest →ₗ[ℂ] QuantumTest
attribute [local irreducible] GaussDiagonalHistory.diagonalAction

def responseRead (f g : QuantumTest) : End →ₗ[ℂ] PairMatrix where
  toFun M A B := sourcePair (A f) (M (B g))
  map_add' M N := by
    ext A B
    simp only [LinearMap.add_apply,sourcePair,map_add,inner_add_right,Pi.add_apply]
  map_smul' c M := by
    ext A B
    simp only [LinearMap.smul_apply,sourcePair,map_smul,inner_smul_right,
      Pi.smul_apply,smul_eq_mul,RingHom.id_apply]

private theorem flow_pair_generator (flow : ℝ → End) (G : End)
    (hzero : ∀ f,flow 0 f=f)
    (hpair : ∀ t f g,sourcePair (flow t f) (flow t g)=sourcePair f g)
    (hderiv : ∀ f,HasDerivAt (fun t : ℝ => embed (flow t f)) (embed (G f)) 0)
    (f g : QuantumTest) : sourcePair f (G g)= -sourcePair (G f) g := by
  have h := (hderiv f).inner ℂ (hderiv g)
  simp only [hzero] at h
  have he : (fun t : ℝ => inner ℂ (embed (flow t f)) (embed (flow t g)))=
      fun _ => sourcePair f g := funext (fun t => hpair t f g)
  rw [he] at h
  have heq := h.unique (hasDerivAt_const (0 : ℝ) (sourcePair f g))
  change sourcePair f (G g)+sourcePair (G f) g=0 at heq
  exact eq_neg_of_add_eq_zero_left heq

private theorem phi_pair (f g : QuantumTest) : sourcePair f (Phi g)= -sourcePair (Phi f) g :=
  flow_pair_generator SourceScalarAffineScaleTransport.coreFlow Phi
    SourceScalarAffineScaleTransport.coreFlow_zero SourceScalarAffineScaleTransport.coreFlow_pair
    (fun q => by simpa only [SourceScalarAffineScaleTransport.coreFlow_zero] using!
      SourceScalarAffineScaleTransport.strong_core_derivative q 0) f g
private theorem gauge_pair (f g : QuantumTest) : sourcePair f (Gauge g)= -sourcePair (Gauge f) g :=
  flow_pair_generator SourceGaugeScaleTransport.coreFlow Gauge
    SourceGaugeScaleTransport.coreFlow_zero SourceGaugeScaleTransport.coreFlow_pair
    (fun q => by simpa only [SourceGaugeScaleTransport.coreFlow_zero] using!
      SourceGaugeScaleTransport.strong_core_derivative q 0) f g
private theorem coframe_pair (f g : QuantumTest) : sourcePair f (Coframe g)= -sourcePair (Coframe f) g := by
  have hc : star (3*Complex.I/2 : ℂ)= -(3*Complex.I/2 : ℂ) := by simp;ring
  have hd := dilation_pair f g
  change sourcePair f ((3*Complex.I/2 : ℂ) • dilation g)=
    -sourcePair ((3*Complex.I/2 : ℂ) • dilation f) g
  simp only [sourcePair,map_smul,inner_smul_left,inner_smul_right,starRingEnd_apply] at hd ⊢
  rw [hc,hd]
  ring

private theorem response_delta (G : End) (hG : ∀ f g,sourcePair f (G g)= -sourcePair (G f) g)
    (f g : QuantumTest) (M : End) : responseRead f g (G*M-M*G)=pairDelta G (responseRead f g M) := by
  ext A B
  change sourcePair (A f) (G (M (B g))-M (G (B g)))=
    -sourcePair (G (A f)) (M (B g))-sourcePair (A f) (M (G (B g)))
  simp only [sourcePair,map_sub,inner_sub_right] at hG ⊢
  rw [hG]

private theorem polynomial_map {R S : Type*} [Ring R] [Algebra ℂ R] [Ring S] [Algebra ℂ S]
    (L : R →ₗ[ℂ] S) (p g c : R →ₗ[ℂ] R) (ep eg ec : S →ₗ[ℂ] S)
    (hp : ∀ x,L (p x)=ep (L x)) (hg : ∀ x,L (g x)=eg (L x))
    (hc : ∀ x,L (c x)=ec (L x)) (γ : ℂ) (x : R) :
    L (inverseWard p g c γ x)=inverseWard ep eg ec γ (L x) := by
  simp only [inverseWard,InverseVolumeWardAlgebra.mixedPolynomial,
    InverseVolumeWardAlgebra.affinePolynomial,inverseLocalPolynomial,
    map_add,map_sub,map_smul,hp,hg,hc]

attribute [local irreducible] InverseVolumeWardAlgebra.inverseWard
  SourceScalarPositiveBulkWard.pairDelta SourceScalarInverseBulk.inverseWeightedBulkJet
  SourceScalarVirialBulk.deltaPhi SourceScalarGaugeScale.deltaGauge
  SourceHamiltonianScaleJet.scaleDerivative SourceScalarVirialBulk.vacuumJetCoefficient

/-- The original Haar half-density fixes the signs on both source legs for every inverse Ward jet. -/
theorem original_response_ward (f g : QuantumTest) (M A B : End) :
    sourcePair (A f) (inverseWeightedBulkJet M (B g))=
      inverseWard (pairDelta Phi) (pairDelta Gauge) (pairDelta Coframe)
        (vacuumJetCoefficient : ℂ) (responseRead f g M) A B := by
  have h : responseRead f g (inverseWeightedBulkJet M)=
      inverseWard (pairDelta Phi) (pairDelta Gauge) (pairDelta Coframe)
        (vacuumJetCoefficient : ℂ) (responseRead f g M) := by
    unfold inverseWeightedBulkJet
    apply polynomial_map (responseRead f g) deltaPhi deltaGauge scaleDerivative
    · intro x
      rw [←SourceScalarAffineScaleTransport.generator_commutator]
      exact response_delta Phi phi_pair f g x
    · intro x
      rw [←SourceGaugeScaleTransport.generator_commutator]
      exact response_delta Gauge gauge_pair f g x
    · intro x
      rw [←SourceGaugeCoframeJets.K_commutator]
      exact response_delta Coframe coframe_pair f g x
  exact congrFun (congrFun h A) B

private theorem inverse_pair (f g : QuantumTest) :
    sourcePair f (inverseVolumeAction g)=sourcePair (inverseVolumeAction f) g := multiply_pair _ _ _ _

private theorem full_symmetric_pair (sharp : Bool) (f g : QuantumTest) :
    sourcePair f (inverseFullSymmetricScale sharp g)=
      (1/2 : ℂ)*(sourcePair (diagonalAction f) (inverseVolumeAction g)+
        sourcePair (inverseVolumeAction f) (diagonalAction g))+
      sourcePair f (inverseVolumeAction (fullAction sharp g)) := by
  have hs : inverseFullSymmetricScale sharp=inverseSymmetricScale+inverseVolumeAction*fullAction sharp := by
    unfold inverseFullSymmetricScale inverseSymmetricScale
    rw [add_mul,mul_add,(original_full_inverse_commute sharp).eq]
    module
  rw [hs]
  change sourcePair f ((1/2 : ℂ) • (diagonalAction (inverseVolumeAction g)+
    inverseVolumeAction (diagonalAction g))+inverseVolumeAction (fullAction sharp g))=_
  simp only [sourcePair,map_add,map_smul,inner_add_right,inner_smul_right]
  change (1/2 : ℂ)*(sourcePair f (diagonalAction (inverseVolumeAction g))+
    sourcePair f (inverseVolumeAction (diagonalAction g)))+_=_
  rw [diagonalAction_pair,inverse_pair f (diagonalAction g)]
  rfl

/-- The full H0+Y polarized response uses the original states, inputs, both raised defects and full complex frequency. -/
def fullResolvedPair (sharp : Bool) (F : Index) (zl zr : ℂ) (hl : zl.im≠0) (hr : zr.im≠0)
    (g k : diagonal.domain) : PairMatrix := fun A B =>
  let p := state F zl hl k
  let q := state F zr hr g
  (1/2 : ℂ)*(sourcePair (A (coreEquiv.symm k)) (inverseVolumeAction (B q))+
    sourcePair (inverseVolumeAction (A p)) (B (coreEquiv.symm g))+
    (star zl+zr)*sourcePair (A p) (inverseVolumeAction (B q))+
    sourcePair (raisedDefect F A p) (inverseVolumeAction (B q))+
    sourcePair (inverseVolumeAction (A p)) (raisedDefect F B q))+
    sourcePair (A p) (inverseVolumeAction (fullAction sharp (B q)))

attribute [local irreducible] SourceScalarPositiveBulkWard.state
  SourceScalarPositiveBulkWard.raisedDefect SourcePhysicalKineticSquare.inverseVolumeAction
  SourceMixedNativeReturn.fullAction

theorem actual_full_symmetric_pair (sharp : Bool) (F : Index) (zl zr : ℂ)
    (hl : zl.im≠0) (hr : zr.im≠0) (g k : diagonal.domain) (A B : End) :
    sourcePair (A (state F zl hl k)) (inverseFullSymmetricScale sharp (B (state F zr hr g)))=
      fullResolvedPair sharp F zl zr hl hr g k A B := by
  rw [full_symmetric_pair,actual_raised_source,actual_raised_source]
  simp only [fullResolvedPair,sourcePair,map_add,map_smul,inner_add_left,inner_add_right,
    inner_smul_left,inner_smul_right,starRingEnd_apply]
  have hv := inverse_pair (A (state F zl hl k)) (B (state F zr hr g))
  simp only [sourcePair] at hv
  linear_combination (norm := ring) -((1/2 : ℂ)*zr)*hv

private theorem square_pair (m ell : ℕ) (f g : QuantumTest) :
    sourcePair f (square m ell g)=sourcePair (square m ell f) g := by
  change sourcePair f (theta m ell (theta m ell g))=sourcePair (theta m ell (theta m ell f)) g
  have ht (a b : QuantumTest) : sourcePair a (theta m ell b)=sourcePair (theta m ell a) b :=
    multiply_pair _ _ _ _
  rw [ht,ht]

/-- Localize the entire response before differentiating; the cutoff is not affine invariant. -/
def localizedResponse (m ell : ℕ) (P : PairMatrix) : PairMatrix := fun A B =>
  (1/2 : ℂ)*(P A (square m ell*B)+P (square m ell*A) B)

private theorem response_jordan (m ell : ℕ) (f g : QuantumTest) (M : End) :
    responseRead f g (jordan M (square m ell))=localizedResponse m ell (responseRead f g M) := by
  ext A B
  change sourcePair (A f) ((1/2 : ℂ) • (M (square m ell (B g))+square m ell (M (B g))))=_
  simp only [sourcePair,map_smul,map_add,inner_smul_right,inner_add_right]
  change (1/2 : ℂ)*(sourcePair (A f) (M (square m ell (B g)))+
    sourcePair (A f) (square m ell (M (B g))))=_
  rw [square_pair]
  rfl

attribute [local irreducible] fullResolvedPair localizedResponse
  SourceScalarInverseFullSource.inverseFullSymmetricScale
  SourceScalarPositiveBulkWard.resolvedBulk

/-- The whole localized source Ward now acts on literal dynamical responses, not supplied jet values. -/
theorem actual_whole_dynamic_response (sharp : Bool) (m ell : ℕ) (F : Index)
    (zl zr : ℂ) (hl : zl.im≠0) (hr : zr.im≠0) (g k : diagonal.domain) (A B : End) :
    sourcePair (A (state F zl hl k)) (wholeWard sharp m ell (B (state F zr hr g)))=
      inverseWard (pairDelta Phi) (pairDelta Gauge) (pairDelta Coframe) (vacuumJetCoefficient : ℂ)
        (localizedResponse m ell (fullResolvedPair sharp F zl zr hl hr g k)) A B := by
  have h := original_response_ward (state F zl hl k) (state F zr hr g)
    (jordan (inverseFullSymmetricScale sharp) (square m ell)) A B
  rw [response_jordan] at h
  have he : responseRead (state F zl hl k) (state F zr hr g) (inverseFullSymmetricScale sharp)=
      fullResolvedPair sharp F zl zr hl hr g k := by
    ext X Y
    exact actual_full_symmetric_pair sharp F zl zr hl hr g k X Y
  rw [he] at h
  simpa only [wholeWard] using! h

/-- Both branches retain Yukawa, affine contacts and all seventy inverse IMS rows in the same-F response identity. -/
theorem actual_signed_dynamic_response (sharp : Bool) (m ell : ℕ) (F : Index)
    (zl zr : ℂ) (hl : zl.im≠0) (hr : zr.im≠0) (g k : diagonal.domain) :
    inverseWard (pairDelta Phi) (pairDelta Gauge) (pairDelta Coframe) (vacuumJetCoefficient : ℂ)
        (localizedResponse m ell (fullResolvedPair sharp F zl zr hl hr g k)) 1 1-
      sourcePair (state F zl hl k) (yukawaCorrection sharp m ell (state F zr hr g))-
      sourcePair (state F zl hl k)
        (jordan firstSourceContact (deltaPhi (square m ell)) (state F zr hr g))-
      sourcePair (state F zl hl k)
        (jordan secondSourceContact (deltaPhi (deltaPhi (square m ell))) (state F zr hr g))+
      inverseContact m ell (state F zl hl k) (state F zr hr g)=
    resolvedBulk F zl zr hl hr g k (inverseVolumeAction*theta m ell) (inverseVolumeAction*theta m ell) := by
  have h := actual_two_leg_exchange sharp m ell F zl zr hl hr g k
  rw [signedPair] at h
  have hw := actual_whole_dynamic_response sharp m ell F zl zr hl hr g k 1 1
  simp only [Module.End.one_apply] at hw
  rw [hw] at h
  exact h

end LowEnergy.SourceInverseFullResponse
