import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiJointSourceDescent
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 2048
set_option maxHeartbeats 1200000
noncomputable section
namespace LowEnergy.FirstCurrentAdmissibleElectric
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussNativeForm
open GaussNativeEnergy GaussDiagonalHistory GaussUnitaryHistory
open SourceQuantumConfigurationHilbert SourceQuantumScalarChart SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open SourceScalarDoubleCurrent SourceClockPhiNormalizedScalarBudget SourceClockPhiNativeMatchedSource
open SourceLocalizedInverseFormPayment SourceResolventBandLimit
open FirstCurrentJointBudget FirstCurrentGeometricPayer FirstCurrentElectricSuccessor FirstCurrentPayerNext
open JointElectricSource ClockPhiHeatCorrectedCovarianceSource MeasureTheory
open scoped InnerProductSpace
private abbrev End:=QuantumTest→ₗ[ℂ]QuantumTest
private abbrev H0:End:=diagonalAction
private abbrev X:End:=weightedElectricCurrent
private abbrev M:End:=matchedTester
private abbrev γ:=ProbabilityTheory.gaussianReal 0 1
attribute [local irreducible] diagonalAction sourcePair embed normalizedState normalizedForcing
  correctedCompleteCore weightedElectricCurrent matchedTester updatedForcing

/-- Both restrictions carry the full original Hamiltonian commutator. -/
def clockSourcePair(s:ℝ)(hs:0<s)(x:ℝ×ℝ)(a:QuantumTest×QuantumTest):QuantumTest×QuantumTest:=
  let K:=correctedCompleteCore s hs x.1 x.2
  (K a.1,K a.2+bracket H0 K a.1)
/-- Selection uses the original magnetic word, before its electric-contact upper bound. -/
def physicalJointKernel(half advanced:Bool)(z:ℂ)(a b:QuantumTest×QuantumTest):ℂ:=
  jointSourceKernel half advanced z a b-
    (magneticPrimitiveFactor:ℂ)*sourcePair a.1 ((magneticVolumeWeight*SourceClockPhiMatchedElectricSource.wedgeAction) b.1)+
    4*sourcePair a.1 (SourcePhysicalKineticSquare.inverseVolumeAction (SourceScalarVirialBulk.magneticAction b.1))
def physicalJointPrice(half advanced:Bool)(z:ℂ)(a:QuantumTest×QuantumTest):ℝ:=
  (physicalJointKernel half advanced z a a).re
/-- Noise is integrated before the update is selected. -/
def averagedJointSlope(s:ℝ)(hs:0<s)(half advanced:Bool)(z:ℂ)(a:QuantumTest×QuantumTest):ℝ:=
  ∫x:ℝ×ℝ,
    (physicalJointKernel half advanced z (clockSourcePair s hs x a)
      (clockSourcePair s hs x (electricSourceDirection a))).re+
    (physicalJointKernel half advanced z (clockSourcePair s hs x (electricSourceDirection a))
      (clockSourcePair s hs x a)).re ∂γ.prod γ
def averagedJointCurvature(s:ℝ)(hs:0<s)(half advanced:Bool)(z:ℂ)(a:QuantumTest×QuantumTest):ℝ:=
  ∫x:ℝ×ℝ,physicalJointPrice half advanced z
    (clockSourcePair s hs x (electricSourceDirection a)) ∂γ.prod γ
private def cap(A a r:ℝ):ℝ:=a/((|A|+1)*(a+r+1))
def admissibleElectricStep(s:ℝ)(hs:0<s)(half advanced:Bool)(z:ℂ)(a:QuantumTest×QuantumTest):ℝ:=
  let A:=averagedJointSlope s hs half advanced z a
  let C:=averagedJointCurvature s hs half advanced z a
  (-A/(2*(|C|+1)))*cap A ‖embed a.1‖ ‖embed (X a.1)‖
def admissibleElectricNext(s:ℝ)(hs:0<s)(half advanced:Bool)(z:ℂ)(a:QuantumTest×QuantumTest):QuantumTest×QuantumTest:=
  a+(admissibleElectricStep s hs half advanced z a:ℂ) • electricSourceDirection a

private theorem cap_nonneg(A a r:ℝ)(ha:0≤a)(hr:0≤r):0≤cap A a r:=by unfold cap;positivity
private theorem cap_le_one(A a r:ℝ)(ha:0≤a)(hr:0≤r):cap A a r≤1:=by
  unfold cap
  apply (div_le_one (by positivity:0<(|A|+1)*(a+r+1))).mpr
  nlinarith [mul_nonneg (abs_nonneg A) (show 0≤a+r+1 by positivity)]
private theorem capped_step_norm(A C a r:ℝ)(ha:0≤a)(hr:0≤r):
    |(-A/(2*(|C|+1)))*cap A a r| *r≤a/2:=by
  let d:=|C|+1
  let e:=(|A|+1)*(a+r+1)
  have hd:0<d:=by dsimp[d];positivity
  have he:0<e:=by dsimp[e];positivity
  have hde:|A| *r≤e:=by
    dsimp[e]
    nlinarith [mul_nonneg (abs_nonneg A) ha]
  have hd1:1≤d:=by dsimp[d];linarith[abs_nonneg C]
  have heq:|(-A/(2*d))*(a/e)| *r=(|A| *r)*a/(2*d*e):=by
    rw [abs_mul,abs_div,abs_neg,abs_of_pos (by positivity:0<2*d),abs_div,
      abs_of_nonneg ha,abs_of_pos he]
    ring
  change |(-A/(2*d))*(a/e)| *r≤a/2
  rw [heq]
  calc
    _≤e*a/(2*d*e):=div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hde ha) (by positivity)
    _=a/(2*d):=by field_simp [he.ne']
    _≤a/2:=div_le_div_of_nonneg_left ha (by norm_num) (by nlinarith only[hd1])

private theorem source_direction(z:ℂ)(a:QuantumTest×QuantumTest)(ha:H0 a.1=a.2+z • a.1):
    H0 (electricSourceDirection a).1=(electricSourceDirection a).2+z • (electricSourceDirection a).1:=by
  simp only[electricSourceDirection,bracket,Module.End.mul_apply,LinearMap.sub_apply,ha,map_add,map_smul]
  module
private theorem source_clock(s:ℝ)(hs:0<s)(x:ℝ×ℝ)(z:ℂ)(a:QuantumTest×QuantumTest)
    (ha:H0 a.1=a.2+z • a.1):
    H0 (clockSourcePair s hs x a).1=(clockSourcePair s hs x a).2+z • (clockSourcePair s hs x a).1:=by
  simp only[clockSourcePair,bracket,Module.End.mul_apply,LinearMap.sub_apply,ha,map_add,map_smul]
  module
private theorem source_plane(z:ℂ)(a:QuantumTest×QuantumTest)(ha:H0 a.1=a.2+z • a.1)(α β:ℂ):
    H0 (α • a+β • electricSourceDirection a).1=
      (α • a+β • electricSourceDirection a).2+z • (α • a+β • electricSourceDirection a).1:=by
  have hd:=source_direction z a ha
  simp only[Prod.fst_add,Prod.snd_add,Prod.smul_fst,Prod.smul_snd,map_add,map_smul,ha,hd,
    smul_add,smul_smul]
  module
private theorem next_norm(s:ℝ)(hs:0<s)(half advanced:Bool)(z:ℂ)(a:QuantumTest×QuantumTest):
    ‖embed (admissibleElectricNext s hs half advanced z a).1‖≤2*‖embed a.1‖:=by
  have h:=capped_step_norm (averagedJointSlope s hs half advanced z a)
    (averagedJointCurvature s hs half advanced z a) ‖embed a.1‖ ‖embed (X a.1)‖
    (norm_nonneg _) (norm_nonneg _)
  change |admissibleElectricStep s hs half advanced z a| *‖embed (X a.1)‖≤‖embed a.1‖/2 at h
  change ‖embed (a.1+(admissibleElectricStep s hs half advanced z a:ℂ) • X a.1)‖≤_
  rw [map_add,map_smul]
  have hn:=norm_add_le (embed a.1) ((admissibleElectricStep s hs half advanced z a:ℂ) • embed (X a.1))
  rw [norm_smul,Complex.norm_real,Real.norm_eq_abs] at hn
  nlinarith [norm_nonneg (embed a.1)]

/-- The clock follows the same entire source plane; no independent forcing or endpoint is selected. -/
theorem actual_admissible_electric_source_plane(s:ℝ)(hs:0<s)(m ell:ℕ)(F:Index)(z:ℂ)(hz:z.im≠0)
    (g:diagonal.domain)(α β:ℂ)(x:ℝ×ℝ):
    let a:QuantumTest×QuantumTest:=(normalizedState m ell F z hz g,normalizedForcing m ell F z hz g)
    let b:=α • a+β • electricSourceDirection a
    H0 b.1=b.2+z • b.1 ∧
    H0 (clockSourcePair s hs x b).1=(clockSourcePair s hs x b).2+z • (clockSourcePair s hs x b).1:=by
  dsimp only
  have ha:=actual_full_normalized_source m ell F z hz g
  have hb:=source_plane z (normalizedState m ell F z hz g,normalizedForcing m ell F z hz g) ha α β
  exact ⟨hb,source_clock s hs x z _ hb⟩

/-- The selected input is independent of Gaussian noise and preserves the original shifted source price uniformly. -/
theorem actual_admissible_electric_source_update(s:ℝ)(hs:0<s)(half advanced:Bool)
    (m ell:ℕ)(F:Index)(z:ℂ)(hz:z.im≠0)(g:diagonal.domain):
    let a:QuantumTest×QuantumTest:=(normalizedState m ell F z hz g,normalizedForcing m ell F z hz g)
    let b:=admissibleElectricNext s hs half advanced z a
    H0 b.1=b.2+z • b.1 ∧
    ‖embed b.1‖≤2*‖embed a.1‖ ∧
    ‖embed (z • b.1)‖^2≤4*‖embed (z • a.1)‖^2 ∧
    M b.1=M a.1+(admissibleElectricStep s hs half advanced z a:ℂ) • matchedElectricSuccessor a.1:=by
  dsimp only
  let a:QuantumTest×QuantumTest:=(normalizedState m ell F z hz g,normalizedForcing m ell F z hz g)
  have ha:=actual_full_normalized_source m ell F z hz g
  have hp:=source_plane z a ha 1 (admissibleElectricStep s hs half advanced z a:ℂ)
  simp only[one_smul] at hp
  have hn:=next_norm s hs half advanced z a
  refine ⟨hp,hn,?_,?_⟩
  · simp only[map_smul,norm_smul]
    have ht:=mul_le_mul_of_nonneg_left hn (norm_nonneg z)
    have h2:=pow_le_pow_left₀ (by positivity) ht 2
    nlinarith only[h2]
  · change M (weightedElectricEndpoint (admissibleElectricStep s hs half advanced z a) false a.1)=_
    simpa only[Bool.false_eq_true,ite_false] using actual_matched_electric_endpoint F g
      (admissibleElectricStep s hs half advanced z a) false a.1
private theorem work_contact(F:Index)(g:diagonal.domain)(w:QuantumTest):
    magneticPrimitiveWork 1 w=magneticPrimitiveFactor*
      (sourcePair w ((magneticVolumeWeight*SourceClockPhiMatchedElectricSource.wedgeAction) w)).re:=by
  have h:=(actual_weighted_electric_midpoint F g 1 w).2
  unfold magneticPrimitiveWork
  norm_num at h ⊢
  linear_combination (-2*magneticPrimitiveFactor)*h

/-- The Gaussian selection kernel is exactly the complete original R payer, with its original magnetic field. -/
theorem actual_physical_joint_source_price(s:ℝ)(hs:0<s)(ξ η:ℝ)(half advanced:Bool)
    (m ell:ℕ)(F:Index)(q:ℝ)(g:diagonal.domain)
    (hz:(actualFrequency advanced (sourceNoetherFrequency half) q).im≠0):
    let z:=actualFrequency advanced (sourceNoetherFrequency half) q
    let a:QuantumTest×QuantumTest:=(normalizedState m ell F z hz g,normalizedForcing m ell F z hz g)
    physicalJointPrice half advanced z (clockSourcePair s hs (ξ,η) a)=
      scalarNoetherFactor half*correctedScalarNoetherPrice s hs ξ η half advanced m ell F q g+
        FirstCurrentJointBudgetNext.remainingGeometricPrice (correctedCompleteCore s hs ξ η a.1) z:=by
  dsimp only
  have h:=(actual_joint_source_variational_update s hs ξ η half advanced m ell F q g hz).1
  unfold physicalJointPrice physicalJointKernel
  simp only[Complex.add_re,Complex.sub_re,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
    Complex.re_ofNat,Complex.im_ofNat,zero_mul,sub_zero]
  change jointSourcePrice half advanced _ (clockSourcePair s hs (ξ,η) _)-_+_=_
  have he:jointSourcePrice half advanced (actualFrequency advanced (sourceNoetherFrequency half) q)
      (clockSourcePair s hs (ξ,η) (normalizedState m ell F _ hz g,normalizedForcing m ell F _ hz g))=
      scalarNoetherFactor half*correctedScalarNoetherPrice s hs ξ η half advanced m ell F q g+
        electricGeometricPrice 1 (correctedCompleteCore s hs ξ η (normalizedState m ell F _ hz g))
          (actualFrequency advanced (sourceNoetherFrequency half) q):=by
    simpa only[clockSourcePair,updatedForcing] using h
  rw [he,electricGeometricPrice,work_contact F g]
  simp only[clockSourcePair]
  ring
end LowEnergy.FirstCurrentAdmissibleElectric
