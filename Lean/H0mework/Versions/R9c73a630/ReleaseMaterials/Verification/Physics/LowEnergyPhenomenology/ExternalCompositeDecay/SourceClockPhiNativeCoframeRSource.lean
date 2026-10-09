import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiJointForcingSource
import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiNativeComplementJointSource
import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiOriginalGaussianH0CoframeRecognition
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section
namespace LowEnergy.FirstCurrentPayerNext
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussNativeForm GaussNativeEnergy
open GaussDiagonalHistory GaussUnitaryHistory SourceQuantumConfigurationHilbert
open SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge SourcePhysicalKineticSquare SourceCoframeVolume
open SourceScalarDoubleCurrent SourceCoframeCovariantAction SourceClockPhiCombinedScalePressure
open SourceClockPhiNativeMatchedSource SourceClockPhiMatchedDiffusionSource SourceClockPhiNormalizedScalarBudget
open SourceClockPhiOriginalGaussianH0CoframeRecognition SourceClockPhiOriginalGaussianH0FirstJet
open FinitePhysicalSource JointElectricSource NativePointReturn
open scoped InnerProductSpace
private abbrev n : ℝ := sourceTime 0
private abbrev A := combinedConjugate
private abbrev U := inverseVolumeAction
private abbrev D := combinedGenerator
attribute [local irreducible] sourcePair embed combinedConjugate covariantKinetic diagonalAction
private theorem n_positive : 0 < n := by
  change 0 < sourceTime 0
  rw [source_time_generated]
  exact SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair.lapse_pos
private theorem inverse_volume (f : QuantumTest) : U (volumeAction f) = f := by
  apply DFunLike.ext
  intro z
  change (reciprocalVolume z:ℂ) • ((volume z:ℂ) • f z) = f z
  by_cases hz : z ∈ physicalChart
  · have hn : (volume z:ℂ) ≠ 0 := by exact_mod_cast (volume_pos ⟨z,hz⟩).ne'
    simp only [reciprocalVolume,Complex.ofReal_inv,smul_smul,inv_mul_cancel₀ hn,one_smul]
  · rw [image_eq_zero_of_notMem_tsupport (fun h => hz (f.tsupport_subset h)),smul_zero,smul_zero]

/-- The actual coframe first current is already a generated UD square. -/
theorem actual_coframe_first_current_price (w : QuantumTest) :
    (sourcePair w ((bracket A (bracket A covariantKinetic)) w)).re =
      (3*n/8)*‖embed (U (D w))‖^2 := by
  have h := actual_stochastic_covariant_current w w
  unfold stochasticPairJet at h
  rw [inverse_volume] at h
  have hu : sourcePair (D w) (U (U (D w))) = sourcePair (U (D w)) (U (D w)) := multiply_pair _ _ _ _
  rw [hu] at h
  have he : (sourcePair (U (D w)) (U (D w))) = (‖embed (U (D w))‖^2:ℂ) := by
    simpa only [sourcePair,Complex.ofReal_pow] using!
      inner_self_eq_norm_sq_to_K (𝕜:=ℂ) (embed (U (D w)))
  rw [he] at h
  have hc : (sourceTime 0/48:ℂ)*(18*(‖embed (U (D w))‖:ℂ)^2)=
      ((3*sourceTime 0/8*‖embed (U (D w))‖^2:ℝ):ℂ) := by
    push_cast
    ring
  rw [hc] at h
  rw [←h,Complex.ofReal_re]

private theorem joint_current_balance (w f : QuantumTest) (z : ℂ)
    (hsource : diagonalAction w=f+z • w) :
    2*(sourcePair (A w) ((bracket diagonalAction A) w)).re+matchedField w+
      (432/n)*‖embed f‖^2-(n/48)*‖embed (matchedTester w)+((144/n:ℝ):ℂ) • embed f‖^2-
      (n/96)*‖embed (U (D w))‖^2 =
      (sourcePair w (completeCurrent nativeComplement w)).re+matchedField w+
      (35*n/96)*‖embed (U (D w))‖^2+(432/n)*‖embed (covariantKinetic w-z • w)‖^2-
      (n/48)*‖embed (matchedTester w)+((144/n:ℝ):ℂ) • embed (covariantKinetic w-z • w)‖^2 := by
  let fcf := covariantKinetic w-z • w
  have hf : f=fcf+nativeComplement w := by
    dsimp only [fcf]
    unfold nativeComplement
    simp only [LinearMap.sub_apply]
    linear_combination (norm:=module) -hsource
  have hsplit : bracket A (bracket A diagonalAction) =
      bracket A (bracket A covariantKinetic)+bracket A (bracket A nativeComplement) := by
    unfold nativeComplement bracket
    noncomm_ring
  have hcurrent := actual_double_current_first_source w
  rw [hsplit,LinearMap.add_apply] at hcurrent
  have hpair : sourcePair w ((bracket A (bracket A covariantKinetic)) w+
      (bracket A (bracket A nativeComplement)) w) =
      sourcePair w ((bracket A (bracket A covariantKinetic)) w)+
      sourcePair w ((bracket A (bracket A nativeComplement)) w) := by
    simp only [sourcePair,map_add,inner_add_right]
  rw [hpair,Complex.add_re] at hcurrent
  have hcf := actual_coframe_first_current_price w
  have hN := actual_native_joint_Q_source w
  have hforce := FiniteCausalSylvester.noether_clock_square n n_positive (embed (matchedTester w)) (embed f)
  have hforceCF := FiniteCausalSylvester.noether_clock_square n n_positive (embed (matchedTester w)) (embed fcf)
  have hcross : (sourcePair (matchedTester w) f).re =
      (sourcePair (matchedTester w) fcf).re+(sourcePair (matchedTester w) (nativeComplement w)).re := by
    rw [hf]
    simp only [sourcePair,map_add,inner_add_right,Complex.add_re]
  change 2*(sourcePair (A w) ((bracket diagonalAction A) w)).re+matchedField w+
    (432/n)*‖embed f‖^2-(n/48)*‖embed (matchedTester w)+((144/n:ℝ):ℂ) • embed f‖^2-
    (n/96)*‖embed (U (D w))‖^2 = _
  simp only [sourcePair] at hcurrent hcf hN hcross ⊢
  dsimp only [fcf] at *
  linear_combination (norm:=ring) -hcurrent+hcf+hN-hforce+hforceCF-6*hcross

/-- The original normalized R consumes the native Q word and the generated coframe contact jointly. -/
theorem actual_original_R_coframe_source
    (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im ≠ 0) (g : diagonal.domain) :
    let w := normalizedState m ell F z hz g
    let fcf := covariantKinetic w-z • w
    firstCurrentJointRemainder m ell F z hz g =
      (sourcePair w (completeCurrent nativeComplement w)).re+matchedField w+
      (35*n/96)*‖embed (U (D w))‖^2+(432/n)*‖embed fcf‖^2-
      (n/48)*‖embed (matchedTester w)+((144/n:ℝ):ℂ) • embed fcf‖^2 := by
  exact joint_current_balance _ _ z (actual_full_normalized_source m ell F z hz g)

/-- The same signed responsibility is returned after the actual positive-clock update,
with the full original forcing and its Hamiltonian commutator retained. -/
theorem actual_corrected_R_coframe_source (t : ℝ) (ht : 0 < t) (x : ℝ×ℝ)
    (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im ≠ 0) (g : diagonal.domain) :
    let w := normalizedState m ell F z hz g
    let u := ClockPhiHeatCorrectedCovarianceSource.correctedCompleteCore t ht x.1 x.2 w
    let f := updatedForcing t ht x m ell F z hz g
    2*(sourcePair (A u) ((bracket diagonalAction A) u)).re+matchedField u+
      (432/n)*‖embed f‖^2-(n/48)*‖embed (matchedTester u)+((144/n:ℝ):ℂ) • embed f‖^2-
      (n/96)*‖embed (U (D u))‖^2 =
      (sourcePair u (completeCurrent nativeComplement u)).re+matchedField u+
      (35*n/96)*‖embed (U (D u))‖^2+(432/n)*‖embed (coframeForcing t ht x z w)‖^2-
      (n/48)*‖embed (coframeCompleted t ht x z w)‖^2 := by
  simpa only [coframeForcing,coframeCompleted,map_add,map_smul] using!
    joint_current_balance _ _ z (actual_corrected_full_forcing t ht x m ell F z hz g)
end LowEnergy.FirstCurrentPayerNext
