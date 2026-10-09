import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiFiniteCausalSylvester
import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiCorrectedPhysicalWorkAbel
import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiComparisonNativeClosedGraph
import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiCorrectedFluctuationPhysicalWork
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
noncomputable section
namespace LowEnergy.FinitePhysicalSource
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussNativeForm
open GaussNativeEnergy GaussDiagonalHistory GaussUnitaryHistory SourceClockPhiNativeJointPayment
open SourceClockPhiCombinedScalePressure SourceClockPhiNormalizedScalarBudget
open SourceClockPhiRadiusSourceCurrent SourceClockRadiusAffineCutoff SourceClockYukawaCubicCurrent
open SourceScalarPairedTransport SourceLocalizedInverseFormPayment SourceScalarPositiveBulkWard
open SourceBulkTwoTime SourceResolventBandLimit SourceJointResidualEnergy SourceFourPoleEnergyClosed
open SourceInverseJetEnergy FullYSourceResolventGraphSplice SourceInverseNoetherChannelGap
open SourceInverseElectricMomentChannels ClockPhiCorrectedPhysicalWorkAbel
open SourceClockPhiMatchedDiffusionSource SourceClockPhiComparisonNativeClosedGraph
open FiniteCausalSylvester
open scoped InnerProductSpace
private abbrev End := QuantumTest →ₗ[ℂ] QuantumTest
attribute [local irreducible] diagonalAction compressionCore defectAction resolventCore embed

/-- These are the original two input seeds and every finite/escape channel of the same F. -/
def sourceColumn (K : End) (m ell : ℕ) (F : Index) (g : diagonal.domain)
    (j : Channel F) : QuantumTest :=
  ∑ i : Fin 2, K (phaseRow m ell i (channelTest F (inputSeed g i) j))

def sourceDrift (K : End) (m ell : ℕ) (F : Index) (g : diagonal.domain)
    (j : Channel F) : QuantumTest :=
  diagonalAction (sourceColumn K m ell F g j) -
    (channelValue F j : ℂ) • sourceColumn K m ell F g j


/-- The price is the generated full drift: original bracket and full dF, including escape. -/
theorem actual_source_drift_native (K : End) (m ell : ℕ) (F : Index) (g : diagonal.domain)
    (j : Channel F) :
    sourceDrift K m ell F g j =
      ∑ i : Fin 2,
        (SourceScalarDoubleCurrent.bracket diagonalAction (K * phaseRow m ell i)
          (channelTest F (inputSeed g i) j) +
        K (phaseRow m ell i (defectAction F (channelTest F (inputSeed g i) j)))) := by
  unfold sourceDrift sourceColumn
  rw [map_sum, Finset.smul_sum, ←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  unfold SourceScalarDoubleCurrent.bracket defectAction
  change diagonalAction (K (phaseRow m ell i (channelTest F (inputSeed g i) j))) -
      (channelValue F j : ℂ) • K (phaseRow m ell i (channelTest F (inputSeed g i) j)) =
    diagonalAction (K (phaseRow m ell i (channelTest F (inputSeed g i) j))) -
      K (phaseRow m ell i (diagonalAction (channelTest F (inputSeed g i) j))) +
      K (phaseRow m ell i ((diagonalAction - compressionCore F) (channelTest F (inputSeed g i) j)))
  rw [LinearMap.sub_apply, map_sub, map_sub, actual_channel_eigen, map_smul, map_smul]
  module

/-- The source, rather than a caller-supplied kernel condition, pays the sole Sylvester endpoint. -/
theorem actual_source_column_zero (K : End) (m ell : ℕ) (F : Index) (g : diagonal.domain) :
    (∑ j : Channel F, sourceColumn K m ell F g j) = 0 := by
  have h := (actual_linear_physical_work_source K 1 (by norm_num) false m ell F g).1
    Complex.I (by simp)
  exact h.1

private theorem B_pair (f g : QuantumTest) :
    sourcePair (driftClock f) g = -sourcePair f (driftClock g) := by
  have h := actual_B3_formal_pair (coreEquiv f) (coreEquiv g)
  change inner ℂ (embed (driftClock (coreEquiv.symm (coreEquiv f)))) (embed g) =
    inner ℂ (embed f) (embed ((-driftClock) (coreEquiv.symm (coreEquiv g)))) at h
  rw [coreEquiv.symm_apply_apply, coreEquiv.symm_apply_apply] at h
  simpa only [sourcePair, LinearMap.neg_apply, map_neg, inner_neg_right] using h

private theorem B_pair_right (f g : QuantumTest) :
    sourcePair f (driftClock g) = -sourcePair (driftClock f) g := by
  simpa only [neg_neg] using (congrArg Neg.neg (B_pair f g)).symm

private theorem clock_entry (K : End) (m ell : ℕ) (F : Index) (g : diagonal.domain)
    (i j : Channel F) :
    sourcePair (sourceColumn K m ell F g i)
      ((SourceScalarDoubleCurrent.bracket driftClock diagonalAction)
        (sourceColumn K m ell F g j)) =
      -(sourcePair (driftClock (sourceColumn K m ell F g i)) (sourceDrift K m ell F g j) +
        sourcePair (sourceDrift K m ell F g i) (driftClock (sourceColumn K m ell F g j))) -
      ((channelValue F j - channelValue F i : ℝ) : ℂ) *
        sourcePair (driftClock (sourceColumn K m ell F g i)) (sourceColumn K m ell F g j) := by
  let p := sourceColumn K m ell F g i
  let q := sourceColumn K m ell F g j
  change sourcePair p (driftClock (diagonalAction q) - diagonalAction (driftClock q)) = _
  simp only [sourcePair, map_sub, inner_sub_right]
  change sourcePair p (driftClock (diagonalAction q)) -
    sourcePair p (diagonalAction (driftClock q)) = _
  rw [B_pair_right p (diagonalAction q), diagonalAction_pair p (driftClock q)]
  unfold sourceDrift
  change -sourcePair (driftClock p) (diagonalAction q) -
      sourcePair (diagonalAction p) (driftClock q) =
    -(sourcePair (driftClock p) (diagonalAction q - (channelValue F j : ℂ) • q) +
      sourcePair (diagonalAction p - (channelValue F i : ℂ) • p) (driftClock q)) -
      ((channelValue F j - channelValue F i : ℝ) : ℂ) * sourcePair (driftClock p) q
  simp only [sourcePair, map_sub, map_smul, inner_sub_left, inner_sub_right,
    inner_smul_left, inner_smul_right, Complex.conj_ofReal, Complex.ofReal_sub]
  change _ = -((sourcePair (driftClock p) (diagonalAction q) -
    (channelValue F j : ℂ) * sourcePair (driftClock p) q) +
    (sourcePair (diagonalAction p) (driftClock q) -
      (channelValue F i : ℂ) * sourcePair p (driftClock q))) - _
  rw [B_pair_right p q]
  simp only [sourcePair]
  ring

/-- The entire finite-CF clock part cancels against its literal two-cause phase.
The surviving word consists only of the original full physical source drift cross legs. -/
theorem actual_clock_phase_finite_source (advanced : Bool) (μ : ℝ) (hμ : 0 < μ)
    (K : End) (m ell : ℕ) (F : Index) (g : diagonal.domain) :
    let c := sourceColumn K m ell F g
    let d := sourceDrift K m ell F g
    3 * (gramRead advanced μ (channelValue F) (fun i j =>
      sourcePair (c i) ((SourceScalarDoubleCurrent.bracket driftClock diagonalAction) (c j)))).re -
      6 * (causalSign advanced * μ) *
        (gramRead advanced μ (channelValue F) (fun i j => sourcePair (driftClock (c i)) (c j))).im =
      -3 * (gramRead advanced μ (channelValue F) (fun i j =>
        sourcePair (driftClock (c i)) (d j) + sourcePair (d i) (driftClock (c j)))).re := by
  dsimp only
  let c := sourceColumn K m ell F g
  let B := fun i j : Channel F => sourcePair (driftClock (c i)) (c j)
  let D := fun i j : Channel F =>
    -(sourcePair (driftClock (c i)) (sourceDrift K m ell F g j) +
      sourcePair (sourceDrift K m ell F g i) (driftClock (c j)))
  have hB : (∑ i, ∑ j, B i j) = 0 := by
    change (∑ i, ∑ j, sourcePair (driftClock (c i)) (c j)) = 0
    simp only [sourcePair, ←inner_sum, ←map_sum]
    rw [show (∑ j, c j) = 0 from actual_source_column_zero K m ell F g]
    simp only [map_zero, inner_zero_right, Finset.sum_const_zero]
  have h := clock_phase_cancellation advanced μ hμ (channelValue F) B D hB
  have he (i j : Channel F) :
      sourcePair (c i) ((SourceScalarDoubleCurrent.bracket driftClock diagonalAction) (c j)) =
        D i j - ((channelValue F j - channelValue F i : ℝ) : ℂ) * B i j :=
    clock_entry K m ell F g i j
  have hleft : (fun i j => D i j - ((channelValue F j - channelValue F i : ℝ) : ℂ) * B i j) =
      (fun i j => sourcePair (sourceColumn K m ell F g i)
        ((SourceScalarDoubleCurrent.bracket driftClock diagonalAction) (sourceColumn K m ell F g j))) := by
    funext i j
    exact (he i j).symm
  rw [hleft] at h
  simp only [B, D, c, gramRead, mul_neg, Finset.sum_neg_distrib, Complex.neg_re] at h ⊢
  linear_combination h

open SourcePhysicalKineticSquare SourceClockPhiWholeSignedWorkIntegrable
open ClockPhiCorrectedFluctuationPhysicalWork

/-- The existing Ec debit pays the complete original clock cross word and retains both losses. -/
theorem actual_clock_cross_square (w d : QuantumTest) :
    -6 * (sourcePair (driftClock w) d).re - (sourceTime 0/48) * comparisonEnergy w =
      (432/sourceTime 0) * ‖embed d‖^2 - (sourceTime 0/48) *
        ‖embed (driftClock w) + ((144/sourceTime 0 : ℝ) : ℂ) • embed d‖^2 -
      (sourceTime 0/96) * ‖embed (inverseVolumeAction (combinedGenerator w))‖^2 := by
  have hn : 0 < sourceTime 0 := by
    rw [source_time_generated]
    exact SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair.lapse_pos
  have h := noether_clock_square (sourceTime 0) hn (embed (driftClock w)) (embed d)
  unfold comparisonEnergy
  change -6 * (inner ℂ (embed (driftClock w)) (embed d)).re -
    (sourceTime 0/48) * _ = _
  linarith only [h]

/-- At every original physical CF time the literal Kcorr−1 column has an internally generated
clock payment.  The right-hand side is its actual full drift norm, including every defect. -/
theorem actual_fluctuation_clock_cross_payment (τ : ℝ) (hτ : 0 < τ) (x : ℝ × ℝ)
    (m ell : ℕ) (F : Index) (g : diagonal.domain) (t : ℝ) :
    let y := fluctuationPhysicalColumn τ hτ x m ell F g t
    let d := fluctuationPhysicalDrift τ hτ x m ell F g t
    (-6 * (sourcePair (driftClock y) d).re - (sourceTime 0/48) * comparisonEnergy y ≤
      (432/sourceTime 0) * ‖embed d‖^2) := by
  dsimp only
  rw [actual_clock_cross_square]
  have hn : 0 < sourceTime 0 := by
    rw [source_time_generated]
    exact SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair.lapse_pos
  have h1 : 0 ≤ (sourceTime 0/48) * ‖embed (driftClock
      (fluctuationPhysicalColumn τ hτ x m ell F g t)) +
      ((144/sourceTime 0 : ℝ) : ℂ) • embed (fluctuationPhysicalDrift τ hτ x m ell F g t)‖^2 := by
    positivity
  have h2 : 0 ≤ (sourceTime 0/96) * ‖embed (inverseVolumeAction (combinedGenerator
      (fluctuationPhysicalColumn τ hτ x m ell F g t)))‖^2 := by positivity
  linarith


/-- The original zero-column producer, skew clock, and existing clock debit jointly generate
an upper price on the finite full-source drift, with both causal lines and every cross channel. -/
theorem actual_clock_phase_common_gram_payment (advanced : Bool) (μ : ℝ) (hμ : 0 < μ)
    (K : End) (m ell : ℕ) (F : Index) (g : diagonal.domain) :
    let c := sourceColumn K m ell F g
    let d := sourceDrift K m ell F g
    3 * (gramRead advanced μ (channelValue F) (fun i j =>
      sourcePair (c i) ((SourceScalarDoubleCurrent.bracket driftClock diagonalAction) (c j)))).re -
      6 * (causalSign advanced * μ) *
        (gramRead advanced μ (channelValue F) (fun i j => sourcePair (driftClock (c i)) (c j))).im -
      (sourceTime 0/48) * (gramRead advanced μ (channelValue F) (fun i j =>
        sourcePair (driftClock (c i)) (driftClock (c j)))).re ≤
      (432/sourceTime 0) * (gramRead advanced μ (channelValue F) (fun i j => sourcePair (d i) (d j))).re := by
  dsimp only
  rw [actual_clock_phase_finite_source advanced μ hμ K m ell F g]
  have hn : 0 < sourceTime 0 := by
    rw [source_time_generated]
    exact SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair.lapse_pos
  simpa only [sourcePair] using causalGram_noether_payment advanced μ hμ (channelValue F)
    (fun i => embed (driftClock (sourceColumn K m ell F g i)))
    (fun i => embed (sourceDrift K m ell F g i)) (sourceTime 0) hn


open SourceClockPhiNativeMatchedSource

private theorem original_inverse_volume_gram_real (advanced : Bool) (μ : ℝ)
    (K : End) (m ell : ℕ) (F : Index) (g : diagonal.domain) :
    (gramRead advanced μ (channelValue F) (fun i j =>
      sourcePair (inverseVolumeAction (sourceColumn K m ell F g i))
        (sourceColumn K m ell F g j))).im = 0 := by
  apply paired_gram_real
  intro i j
  have hp := GaussNativeForm.pair_conjugate
    (inverseVolumeAction (sourceColumn K m ell F g i)) (sourceColumn K m ell F g j)
  rw [show star (sourcePair (inverseVolumeAction (sourceColumn K m ell F g i))
      (sourceColumn K m ell F g j)) =
      sourcePair (sourceColumn K m ell F g j) (inverseVolumeAction (sourceColumn K m ell F g i)) from hp]
  exact multiply_pair _ _ _ _

/-- The U contribution is consumed as an actual real Gram, so the phase remains the literal C3 phase. -/
theorem actual_literal_matched_phase (advanced : Bool) (μ : ℝ)
    (K : End) (m ell : ℕ) (F : Index) (g : diagonal.domain) :
    (gramRead advanced μ (channelValue F) (fun i j =>
      sourcePair (driftClock (sourceColumn K m ell F g i)) (sourceColumn K m ell F g j))).im =
    (gramRead advanced μ (channelValue F) (fun i j =>
      sourcePair (matchedColumn (sourceColumn K m ell F g i)) (sourceColumn K m ell F g j))).im := by
  have hU := original_inverse_volume_gram_real advanced μ K m ell F g
  have he : gramRead advanced μ (channelValue F) (fun i j =>
      sourcePair (driftClock (sourceColumn K m ell F g i)) (sourceColumn K m ell F g j)) =
      gramRead advanced μ (channelValue F) (fun i j =>
        sourcePair (matchedColumn (sourceColumn K m ell F g i)) (sourceColumn K m ell F g j)) +
      3 * gramRead advanced μ (channelValue F) (fun i j =>
        sourcePair (inverseVolumeAction (sourceColumn K m ell F g i)) (sourceColumn K m ell F g j)) := by
    unfold gramRead
    simp only [driftClock, LinearMap.add_apply, LinearMap.smul_apply, sourcePair,
      map_add, map_smul, inner_add_left, inner_smul_left, map_ofNat, mul_add,
      Finset.sum_add_distrib, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [he, Complex.add_im, Complex.mul_im, hU]
  simp only [Complex.re_ofNat, Complex.im_ofNat, mul_zero, zero_mul, add_zero]

/-- Direct finite payment of the literal original clock/phase block with its existing Ec clock debit. -/
theorem actual_literal_clock_phase_finite_payment (advanced : Bool) (μ : ℝ) (hμ : 0 < μ)
    (K : End) (m ell : ℕ) (F : Index) (g : diagonal.domain) :
    let c := sourceColumn K m ell F g
    let d := sourceDrift K m ell F g
    3 * (gramRead advanced μ (channelValue F) (fun i j =>
      sourcePair (c i) ((SourceScalarDoubleCurrent.bracket driftClock diagonalAction) (c j)))).re -
      6 * (causalSign advanced * μ) *
        (gramRead advanced μ (channelValue F) (fun i j => sourcePair (matchedColumn (c i)) (c j))).im -
      (sourceTime 0/48) * (gramRead advanced μ (channelValue F) (fun i j =>
        sourcePair (driftClock (c i)) (driftClock (c j)))).re ≤
      (432/sourceTime 0) * (gramRead advanced μ (channelValue F) (fun i j => sourcePair (d i) (d j))).re := by
  have h := actual_clock_phase_common_gram_payment advanced μ hμ K m ell F g
  simpa only [actual_literal_matched_phase] using h


open SourceCoframeDilation SourceCoframeVolumeCurrent SourceClockPhiHeatNativeClosedGraph
open ClockPhiMatchedGainFrequencyPayment
open MeasureTheory Filter
open scoped Topology
private abbrev U : End := inverseVolumeAction
private abbrev A : End := combinedConjugate
private abbrev D : End := combinedGenerator
private abbrev Dc : End := dilation
private abbrev n : ℝ := sourceTime 0

private theorem lapse_positive : 0 < n := by
  change 0 < sourceTime 0
  rw [source_time_generated]
  exact SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair.lapse_pos
private theorem source_pair_re (f g : QuantumTest) : (sourcePair f g).re = (sourcePair g f).re := by
  have h := congrArg Complex.re (GaussNativeForm.pair_conjugate f g)
  simpa only [Complex.conj_re] using h
private theorem source_self_re (f : QuantumTest) : (sourcePair f f).re = ‖embed f‖^2 := by
  simpa only [sourcePair, RCLike.re_eq_complex_re] using
    (norm_sq_eq_re_inner (𝕜 := ℂ) (embed f)).symm
private theorem source_A_pair (f g : QuantumTest) : sourcePair (A f) g = -sourcePair f (A g) := by
  have h := actual_A_formal_pair (coreEquiv f) (coreEquiv g)
  change inner ℂ (embed (A (coreEquiv.symm (coreEquiv f)))) (embed g) =
    inner ℂ (embed f) (embed ((-A) (coreEquiv.symm (coreEquiv g)))) at h
  rw [coreEquiv.symm_apply_apply, coreEquiv.symm_apply_apply] at h
  simpa only [sourcePair, LinearMap.neg_apply, map_neg, inner_neg_right] using h
private theorem source_A_pair_right (f g : QuantumTest) : sourcePair f (A g) = -sourcePair (A f) g := by
  simpa only [neg_neg] using (congrArg Neg.neg (source_A_pair f g)).symm

/-- The complete double current is generated by a single H0 commutator on its actual A leg. -/
theorem actual_double_current_first_source (w : QuantumTest) :
    (sourcePair w ((SourceScalarDoubleCurrent.bracket A
      (SourceScalarDoubleCurrent.bracket A diagonalAction)) w)).re =
      2 * (sourcePair (A w) ((SourceScalarDoubleCurrent.bracket diagonalAction A) w)).re := by
  have hp : sourcePair w ((SourceScalarDoubleCurrent.bracket A
      (SourceScalarDoubleCurrent.bracket A diagonalAction)) w) =
      sourcePair (A w) (diagonalAction (A w) - A (diagonalAction w)) +
      sourcePair (diagonalAction (A w) - A (diagonalAction w)) (A w) := by
    change sourcePair w (A (A (diagonalAction w) - diagonalAction (A w)) -
      (A (diagonalAction (A w)) - diagonalAction (A (A w)))) = _
    simp only [sourcePair, map_sub, inner_sub_left, inner_sub_right]
    change sourcePair w (A (A (diagonalAction w))) - sourcePair w (A (diagonalAction (A w))) -
      (sourcePair w (A (diagonalAction (A w))) - sourcePair w (diagonalAction (A (A w)))) = _
    rw [source_A_pair_right w (A (diagonalAction w)),
      source_A_pair_right w (diagonalAction (A w)),
      diagonalAction_pair w (A (A w)),
      source_A_pair_right (diagonalAction w) (A w)]
    change _ = (sourcePair (A w) (diagonalAction (A w)) - sourcePair (A w) (A (diagonalAction w))) +
      (sourcePair (diagonalAction (A w)) (A w) - sourcePair (A (diagonalAction w)) (A w))
    rw [←diagonalAction_pair (A w) (A w)]
    ring
  rw [hp, Complex.add_re, source_pair_re (diagonalAction (A w) - A (diagonalAction w)) (A w)]
  change _ = 2 * (sourcePair (A w) (diagonalAction (A w) - A (diagonalAction w))).re
  ring

private theorem inverse_dilation_source : Dc*U-U*Dc = (2*Complex.I) • U := by
  have h := congrArg (fun L : End => (-2*Complex.I/3) • L) SourceScalarInverseBulk.inverse_coframe
  change (-2*Complex.I/3) • ((3*Complex.I/2) • (Dc*U-U*Dc)) =
    (-2*Complex.I/3) • ((-3:ℂ) • U) at h
  simp only [smul_smul] at h
  have hi : (-2*Complex.I/3)*(3*Complex.I/2) = 1 := by
    calc _ = -(Complex.I*Complex.I) := by ring
         _ = _ := by rw [Complex.I_mul_I]; ring
  rw [hi, one_smul] at h
  convert! h using 1
  congr 1
  ring
private theorem inverse_combined_source : Commute U D := by
  change U*D = D*U
  apply LinearMap.ext
  intro f
  have h1 := LinearMap.congr_fun actual_root_combined_commute.eq (inverseRootAction f)
  have h2 := LinearMap.congr_fun actual_root_combined_commute.eq f
  change inverseRootAction (D (inverseRootAction f)) = D (inverseRootAction (inverseRootAction f)) at h1
  change inverseRootAction (D f) = D (inverseRootAction f) at h2
  change U (D f) = D (U f)
  rw [←inverse_root_square (D f), ←inverse_root_square f, h2, h1]
private theorem clock_inverse_source : driftClock*U-U*driftClock = (-6:ℂ) • (U*U) := by
  apply LinearMap.ext
  intro f
  have hD := LinearMap.congr_fun inverse_combined_source.eq f
  have hDc := LinearMap.congr_fun inverse_dilation_source (U f)
  simp only [Module.End.mul_apply, LinearMap.sub_apply, LinearMap.smul_apply] at hD hDc
  have hdc : Dc (U (U f)) = U (Dc (U f)) + (2*Complex.I) • U (U f) := by
    linear_combination (norm := module) hDc
  change (U (D (U f)) + (3*Complex.I) • Dc (U (U f)) + (3:ℂ) • U (U f)) -
    U (U (D f) + (3*Complex.I) • Dc (U f) + (3:ℂ) • U f) = (-6:ℂ) • U (U f)
  rw [←hD, hdc]
  simp only [map_add, map_smul, smul_add, smul_smul]
  have hc : (3*Complex.I)*(2*Complex.I) = (-6:ℂ) := by
    calc _ = 6*(Complex.I*Complex.I) := by ring
         _ = _ := by rw [Complex.I_mul_I]; ring
  rw [hc]
  module

private theorem clock_inverse_pair (w : QuantumTest) :
    (sourcePair (driftClock w) (U w)).re = 3 * ‖embed (U w)‖^2 := by
  have h := congrArg (fun q : QuantumTest => (sourcePair w q).re)
    (LinearMap.congr_fun clock_inverse_source w)
  have hu (p q : QuantumTest) : sourcePair p (U q) = sourcePair (U p) q := multiply_pair _ _ p q
  change (sourcePair w (driftClock (U w) - U (driftClock w))).re =
    (sourcePair w ((-6:ℂ) • U (U w))).re at h
  have hs : sourcePair w (driftClock (U w) - U (driftClock w)) =
      -sourcePair (driftClock w) (U w) - sourcePair (U w) (driftClock w) := by
    simp only [sourcePair, map_sub, inner_sub_right]
    change sourcePair w (driftClock (U w)) - sourcePair w (U (driftClock w)) = _
    rw [B_pair_right w (U w), hu w (driftClock w)]
    rfl
  rw [hs] at h
  have hr : (sourcePair w ((-6:ℂ) • U (U w))).re = -6 * ‖embed (U w)‖^2 := by
    simp only [sourcePair, map_smul, inner_smul_right]
    change ((-6:ℂ) * sourcePair w (U (U w))).re = _
    rw [hu]
    simp only [Complex.mul_re, Complex.neg_re, Complex.re_ofNat, Complex.neg_im,
      Complex.im_ofNat, source_self_re]
    ring
  rw [hr] at h
  simp only [Complex.sub_re, Complex.neg_re, source_pair_re (U w) (driftClock w)] at h
  linarith only [h]

private theorem matched_tester_difference : matchedTester = driftClock-U := by
  unfold matchedTester driftClock
  module

/-- Combining the clock and gain forcing produces five additional inverse-volume squares. -/
theorem actual_matched_tester_clock_contraction (w : QuantumTest) :
    ‖embed (matchedTester w)‖^2 = ‖embed (driftClock w)‖^2 - 5 * ‖embed (U w)‖^2 := by
  have h := norm_sub_sq (𝕜 := ℂ) (embed (driftClock w)) (embed (U w))
  simp only [RCLike.re_eq_complex_re] at h
  rw [matched_tester_difference]
  change ‖embed (driftClock w - U w)‖^2 = _
  rw [map_sub, h]
  change ‖embed (driftClock w)‖^2 - 2 * (sourcePair (driftClock w) (U w)).re + ‖embed (U w)‖^2 = _
  rw [clock_inverse_pair]
  ring

/-- The actual full source forcing remains inside its completed square; no drift norm is discarded. -/
theorem actual_clock_gain_joint_square (w f : QuantumTest) :
    -6 * (sourcePair (matchedTester w) f).re - (n/48) * comparisonEnergy w =
      (432/n) * ‖embed f‖^2 - (n/48) *
        ‖embed (matchedTester w) + ((144/n : ℝ) : ℂ) • embed f‖^2 -
      (5*n/48) * ‖embed (U w)‖^2 - (n/96) * ‖embed (U (D w))‖^2 := by
  have hs := noether_clock_square n lapse_positive (embed (matchedTester w)) (embed f)
  have hm := actual_matched_tester_clock_contraction w
  change -6 * (sourcePair (matchedTester w) f).re - (n/48) * ‖embed (matchedTester w)‖^2 = _ at hs
  rw [hm] at hs
  unfold comparisonEnergy
  linarith only [hs]

/-- The literal complete S keeps its full field while its double-A leg becomes the first current. -/
theorem actual_whole_signed_first_current (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im ≠ 0)
    (g : diagonal.domain) :
    let w := normalizedState m ell F z hz g
    wholeSignedWork m ell F z hz g =
      2 * (sourcePair (A w) ((SourceScalarDoubleCurrent.bracket diagonalAction A) w)).re -
      6 * (sourcePair (matchedTester w) (normalizedForcing m ell F z hz g)).re +
      gainFrequency m ell F z hz g + matchedField w - (n/48) * comparisonEnergy w := by
  dsimp only
  have hH : compressionCore F + defectAction F = diagonalAction := by
    unfold defectAction
    module
  have hb : SourceScalarDoubleCurrent.bracket A (SourceScalarDoubleCurrent.bracket A (compressionCore F)) +
      SourceScalarDoubleCurrent.bracket A (SourceScalarDoubleCurrent.bracket A (defectAction F)) =
      SourceScalarDoubleCurrent.bracket A (SourceScalarDoubleCurrent.bracket A diagonalAction) := by
    rw [←hH]
    unfold SourceScalarDoubleCurrent.bracket
    noncomm_ring
  have hd := actual_double_current_first_source (normalizedState m ell F z hz g)
  have hf := source_pair_re (normalizedForcing m ell F z hz g)
    (matchedTester (normalizedState m ell F z hz g))
  unfold wholeSignedWork matchedForcingWord matchedField gainFrequency
  rw [hb]
  simp only [LinearMap.add_apply, sourcePair, map_add, inner_add_right, Complex.add_re] at hd hf ⊢
  linarith only [hd, hf]

/-- The sole remaining signed source word after the complete clock/gain forcing is paid jointly. -/
def firstCurrentJointRemainder (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im ≠ 0)
    (g : diagonal.domain) : ℝ :=
  let w := normalizedState m ell F z hz g
  let f := normalizedForcing m ell F z hz g
  2 * (sourcePair (A w) ((SourceScalarDoubleCurrent.bracket diagonalAction A) w)).re +
    matchedField w + (432/n) * ‖embed f‖^2 - (n/48) *
      ‖embed (matchedTester w) + ((144/n : ℝ) : ℂ) • embed f‖^2 -
    (n/96) * ‖embed (U (D w))‖^2

theorem actual_whole_signed_joint_balance (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im ≠ 0)
    (g : diagonal.domain) :
    let w := normalizedState m ell F z hz g
    wholeSignedWork m ell F z hz g = firstCurrentJointRemainder m ell F z hz g +
      gainFrequency m ell F z hz g - (5*n/48) * ‖embed (U w)‖^2 := by
  have h1 := actual_whole_signed_first_current m ell F z hz g
  have h2 := actual_clock_gain_joint_square (normalizedState m ell F z hz g)
    (normalizedForcing m ell F z hz g)
  dsimp only at h1 ⊢
  unfold firstCurrentJointRemainder
  linarith only [h1, h2]

private theorem positive_cross_square (u v : H) :
    6 * (inner ℂ u v).re - (5*n/48) * ‖u‖^2 =
      (432/(5*n)) * ‖v‖^2 - (5*n/48) * ‖u - ((144/(5*n) : ℝ) : ℂ) • v‖^2 := by
  have h := noether_clock_square (5*n) (mul_pos (by norm_num) lapse_positive) u (-v)
  simp only [inner_neg_right, Complex.neg_re, norm_neg, smul_neg, ←sub_eq_add_neg] at h
  linarith only [h]

/-- The gained inverse-volume debit pays literal real-frequency gain from the already-generated shifted seed. -/
theorem actual_whole_signed_shifted_square (g : diagonal.domain) :
    ∀ᶠ F in (sourceFilter : Filter Index), ∀ m ell : ℕ, ∀ z : ℂ, ∀ hz : z.im ≠ 0,
      let w := normalizedState m ell F z hz g
      let v := shiftedState m ell F z hz g
      wholeSignedWork m ell F z hz g = firstCurrentJointRemainder m ell F z hz g +
        (432/(5*n)) * ‖embed v‖^2 - (5*n/48) *
          ‖embed (U w) - ((144/(5*n) : ℝ) : ℂ) • embed v‖^2 := by
  filter_upwards [actual_gain_frequency_source g] with F hF
  intro m ell z hz
  have h := actual_whole_signed_joint_balance m ell F z hz g
  have hs := positive_cross_square (embed (U (normalizedState m ell F z hz g)))
    (embed (shiftedState m ell F z hz g))
  have hg := (hF m ell z hz).2
  dsimp only at h ⊢
  change gainFrequency m ell F z hz g = 6 * (inner ℂ
    (embed (U (normalizedState m ell F z hz g))) (embed (shiftedState m ell F z hz g))).re at hg
  linarith only [h, hs, hg]

private theorem frequency_nonreal (advanced : Bool) (μ : ℝ) (hμ : 0 < μ) (q : ℝ) :
    (actualFrequency advanced μ q).im ≠ 0 := by
  cases advanced <;> simpa only [actualFrequency, Bool.false_eq_true, ite_false, ite_true,
    Complex.star_def, Complex.conj_im, line_im, neg_ne_zero] using hμ.ne'

/-- One N pays the full S-to-first-current difference for both original causal lines.
The first-current, full field and signed forcing square stay together in the surviving word. -/
theorem actual_joint_first_current_common_payment (μ : ℝ) (hμ : 0 < μ) (g : diagonal.domain) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ m, N ≤ m → ∀ ell, m ≤ ell →
      ∀ᶠ F in (sourceFilter : Filter Index), ∀ advanced : Bool,
        (∫⁻ q : ℝ, ENNReal.ofReal (wholeSignedWork m ell F (actualFrequency advanced μ q)
          (frequency_nonreal advanced μ hμ q) g - firstCurrentJointRemainder m ell F
          (actualFrequency advanced μ q) (frequency_nonreal advanced μ hμ q) g)) ≤ ENNReal.ofReal ε := by
  intro ε hε
  let C : ℝ := 432/(5*n)
  have hC : 0 < C := by dsimp only [C]; exact div_pos (by norm_num) (mul_pos (by norm_num) lapse_positive)
  obtain ⟨N, hN⟩ := shifted_common_tail μ hμ g (ε/C) (div_pos hε hC)
  refine ⟨N, fun m hm ell hml => ?_⟩
  filter_upwards [hN m hm ell hml, actual_whole_signed_shifted_square g] with F hF hS
  intro advanced
  calc
    _ ≤ ∫⁻ q : ℝ, ENNReal.ofReal C * ENNReal.ofReal
        (‖embed (shiftedState m ell F (actualFrequency advanced μ q)
          (frequency_nonreal advanced μ hμ q) g)‖^2) := by
      apply lintegral_mono
      intro q
      dsimp only
      rw [←ENNReal.ofReal_mul hC.le]
      apply ENNReal.ofReal_le_ofReal
      have h := hS m ell (actualFrequency advanced μ q) (frequency_nonreal advanced μ hμ q)
      dsimp only at h
      have hn : 0 ≤ (5*n/48) * ‖embed (U (normalizedState m ell F (actualFrequency advanced μ q)
          (frequency_nonreal advanced μ hμ q) g)) - ((144/(5*n) : ℝ) : ℂ) •
          embed (shiftedState m ell F (actualFrequency advanced μ q)
            (frequency_nonreal advanced μ hμ q) g)‖^2 := by
        have hp := lapse_positive
        positivity
      dsimp only [C]
      linarith only [h, hn]
    _ = ENNReal.ofReal C * (∫⁻ q : ℝ, ENNReal.ofReal
        (‖embed (shiftedState m ell F (actualFrequency advanced μ q)
          (frequency_nonreal advanced μ hμ q) g)‖^2)) :=
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal C * ENNReal.ofReal (ε/C) :=
      mul_le_mul_of_nonneg_left (hF advanced) zero_le
    _ = ENNReal.ofReal ε := by
      rw [←ENNReal.ofReal_mul hC.le]
      congr 1
      field_simp [hC.ne']

end LowEnergy.FinitePhysicalSource
