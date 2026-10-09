import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiPhysicalJointGaussian
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 2048
set_option maxHeartbeats 1200000
noncomputable section
namespace LowEnergy.FirstCurrentOriginalEcPayer
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussNativeForm
open GaussNativeEnergy GaussDiagonalHistory GaussUnitaryHistory SourcePhysicalKineticSquare
open SourceClockPhiNormalizedScalarBudget SourceLocalizedInverseFormPayment SourceResolventBandLimit
open SourceClockPhiNativeMatchedSource SourceClockPhiMatchedDiffusionSource SourceClockPhiCombinedScalePressure
open SourceClockPhiWholeSignedWorkIntegrable
open FirstCurrentJointBudget FirstCurrentGeometricPayer FirstCurrentElectricSuccessor FirstCurrentPayerNext
open FirstCurrentAdmissibleElectric FirstCurrentAdmissibleElectric.PhysicalGaussian
open JointElectricSource ClockPhiHeatCorrectedCovarianceSource
open scoped InnerProductSpace
private abbrev End:=QuantumTest→ₗ[ℂ]QuantumTest
private abbrev X:End:=weightedElectricCurrent
private abbrev U:End:=inverseVolumeAction
private abbrev D:End:=combinedGenerator
private abbrev M:End:=matchedTester
private abbrev B3:End:=driftClock
attribute [local irreducible] sourcePair embed diagonalAction normalizedState normalizedForcing
  weightedElectricCurrent matchedTester driftClock combinedGenerator inverseVolumeAction correctedCompleteCore

private theorem B3_return(F:Index)(g:diagonal.domain)(w:QuantumTest):
    B3 (X w)=matchedElectricSuccessor w+U (X w):=by
  have h:=actual_matched_electric_endpoint F g 1 false w
  simp only[weightedElectricEndpoint,LinearMap.add_apply,
    Module.End.one_apply,Bool.false_eq_true,ite_false,Complex.ofReal_one,one_smul] at h
  change M (w+X w)=M w+matchedElectricSuccessor w at h
  rw [map_add] at h
  have hM:=add_left_cancel h
  have hB:B3=M+U:=by unfold B3 M driftClock matchedTester;module
  rw [hB,LinearMap.add_apply,hM]

/-- The original M/X successor supplies the actual comparison-energy displacement. -/
def electricGraphRadius(w:QuantumTest):ℝ:=
  ‖embed (X w)‖+‖embed (matchedElectricSuccessor w+U (X w))‖+‖embed (U (D (X w)))‖
private theorem graph_nonneg(w:QuantumTest):0≤electricGraphRadius w:=by unfold electricGraphRadius;positivity
def ecFraction(s:ℝ)(hs:0<s)(half advanced:Bool)(z:ℂ)(a:QuantumTest×QuantumTest):ℝ:=
  ‖embed a.1‖/((|averagedJointSlope s hs half advanced z a|+1)*(‖embed a.1‖+electricGraphRadius a.1+1))
def originalEcStep(s:ℝ)(hs:0<s)(half advanced:Bool)(z:ℂ)(a:QuantumTest×QuantumTest):ℝ:=
  (-averagedJointSlope s hs half advanced z a/(2*(|averagedJointCurvature s hs half advanced z a|+1)))*
    ecFraction s hs half advanced z a
def originalEcNext(s:ℝ)(hs:0<s)(half advanced:Bool)(z:ℂ)(a:QuantumTest×QuantumTest):QuantumTest×QuantumTest:=
  a+(originalEcStep s hs half advanced z a:ℂ) • electricSourceDirection a

private theorem capped_step_norm(A C a r:ℝ)(ha:0≤a)(hr:0≤r):
    |(-A/(2*(|C|+1)))*(a/((|A|+1)*(a+r+1)))| *r≤a/2:=by
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


private theorem displacement_price(s:ℝ)(hs:0<s)(half advanced:Bool)(z:ℂ)(a:QuantumTest×QuantumTest):
    |originalEcStep s hs half advanced z a| *electricGraphRadius a.1≤‖embed a.1‖/2:=
  capped_step_norm _ _ _ _ (norm_nonneg _) (graph_nonneg _)
private theorem norm_add_square(a b:H):‖a+b‖^2≤2*‖a‖^2+2*‖b‖^2:=by
  have h:=pow_le_pow_left₀ (norm_nonneg (a+b)) (norm_add_le a b) 2
  nlinarith only[h,sq_nonneg (‖a‖-‖b‖)]
private theorem shifted_norm(s:ℝ)(hs:0<s)(half advanced:Bool)(z:ℂ)(a:QuantumTest×QuantumTest):
    ‖embed (originalEcNext s hs half advanced z a).1‖≤2*‖embed a.1‖:=by
  have h:=displacement_price s hs half advanced z a
  have hX:‖embed (X a.1)‖≤electricGraphRadius a.1:=by
    unfold electricGraphRadius
    linarith[norm_nonneg (embed (matchedElectricSuccessor a.1+U (X a.1))),norm_nonneg (embed (U (D (X a.1))))]
  have hd:|originalEcStep s hs half advanced z a| *‖embed (X a.1)‖≤‖embed a.1‖/2:=
    (mul_le_mul_of_nonneg_left hX (abs_nonneg _)).trans h
  change ‖embed (a.1+(originalEcStep s hs half advanced z a:ℂ) • X a.1)‖≤_
  rw [map_add,map_smul]
  have hn:=norm_add_le (embed a.1) ((originalEcStep s hs half advanced z a:ℂ) • embed (X a.1))
  rw [norm_smul,Complex.norm_real,Real.norm_eq_abs] at hn
  nlinarith[norm_nonneg (embed a.1)]

/-- No graph budget is supplied: the same source-selected step pays its displaced Ec from the original Ec and norm. -/
theorem actual_original_Ec_point_payment(s:ℝ)(hs:0<s)(half advanced:Bool)(m ell:ℕ)(F:Index)
    (z:ℂ)(hz:z.im≠0)(g:diagonal.domain):
    let w:=normalizedState m ell F z hz g
    let a:QuantumTest×QuantumTest:=(w,normalizedForcing m ell F z hz g)
    let b:=originalEcNext s hs half advanced z a
    ‖embed b.1‖≤2*‖embed w‖ ∧
    ‖embed (z • b.1)‖^2≤4*‖embed (z • w)‖^2 ∧
    comparisonEnergy b.1≤2*comparisonEnergy w+‖embed w‖^2:=by
  dsimp only
  let w:=normalizedState m ell F z hz g
  let a:QuantumTest×QuantumTest:=(w,normalizedForcing m ell F z hz g)
  let h:=originalEcStep s hs half advanced z a
  have hn:=shifted_norm s hs half advanced z a
  have hp:=displacement_price s hs half advanced z a
  have hB:‖embed (B3 (X w))‖≤electricGraphRadius w:=by
    rw [B3_return F g]
    unfold electricGraphRadius
    linarith[norm_nonneg (embed (X w)),norm_nonneg (embed (U (D (X w))))]
  have hD:‖embed (U (D (X w)))‖≤electricGraphRadius w:=by
    unfold electricGraphRadius
    linarith[norm_nonneg (embed (X w)),norm_nonneg (embed (matchedElectricSuccessor w+U (X w)))]
  have hBD:‖(h:ℂ) • embed (B3 (X w))‖≤‖embed w‖/2:=by
    rw [norm_smul,Complex.norm_real,Real.norm_eq_abs]
    exact (mul_le_mul_of_nonneg_left hB (abs_nonneg h)).trans hp
  have hDD:‖(h:ℂ) • embed (U (D (X w)))‖≤‖embed w‖/2:=by
    rw [norm_smul,Complex.norm_real,Real.norm_eq_abs]
    exact (mul_le_mul_of_nonneg_left hD (abs_nonneg h)).trans hp
  refine ⟨hn,?_,?_⟩
  · simp only[map_smul,norm_smul]
    have ht:=mul_le_mul_of_nonneg_left hn (norm_nonneg z)
    have h2:=pow_le_pow_left₀ (by positivity) ht 2
    nlinarith only[h2]
  · have hb2:=pow_le_pow_left₀ (norm_nonneg _) hBD 2
    have hd2:=pow_le_pow_left₀ (norm_nonneg _) hDD 2
    have h0:=norm_add_square (embed (B3 w)) ((h:ℂ) • embed (B3 (X w)))
    have h1:=norm_add_square (embed (U (D w))) ((h:ℂ) • embed (U (D (X w))))
    change comparisonEnergy (w+(h:ℂ) • X w)≤2*comparisonEnergy w+‖embed w‖^2
    unfold comparisonEnergy
    simp only[map_add,map_smul]
    nlinarith only[hb2,hd2,h0,h1,sq_nonneg ‖embed w‖]

/-- Both full forcing legs and every post-clock restriction belong to the original source plane. -/
theorem actual_original_Ec_full_source(s:ℝ)(hs:0<s)(half advanced:Bool)(m ell:ℕ)(F:Index)
    (z:ℂ)(hz:z.im≠0)(g:diagonal.domain)(x:ℝ×ℝ):
    let a:QuantumTest×QuantumTest:=(normalizedState m ell F z hz g,normalizedForcing m ell F z hz g)
    let b:=originalEcNext s hs half advanced z a
    diagonalAction b.1=b.2+z • b.1 ∧
    diagonalAction (clockSourcePair s hs x b).1=(clockSourcePair s hs x b).2+z • (clockSourcePair s hs x b).1:=by
  dsimp only
  have h:=actual_admissible_electric_source_plane s hs m ell F z hz g 1
    (originalEcStep s hs half advanced z (normalizedState m ell F z hz g,normalizedForcing m ell F z hz g):ℂ) x
  simpa only[one_smul,originalEcNext] using h
end LowEnergy.FirstCurrentOriginalEcPayer
