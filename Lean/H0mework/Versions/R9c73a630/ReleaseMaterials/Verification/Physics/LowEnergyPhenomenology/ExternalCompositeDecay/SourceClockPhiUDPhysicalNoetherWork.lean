import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiWholeUDClockSource
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section
namespace LowEnergy.FirstCurrentPayer
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussNativeForm GaussNativeEnergy
open GaussDiagonalHistory GaussUnitaryHistory SourceQuantumConfigurationHilbert SourceQuantumScalarChart
open SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge SourcePhysicalKineticSquare
open SourceClockPhiCoframeForwardCore SourceClockPhiForwardNativeReturn SourceClockPhiCombinedScalePressure
open SourceClockPhiCorrectedWeightTransport SourceClockPhiHeatLocalNativeGaussian
open ClockPhiHeatCorrectedCovarianceSource ClockPhiConservativeHeatSource PositiveClockGenerator
open SourceClockPhiMatchedDiffusionSource SourceClockPhiNormalizedScalarBudget FinitePhysicalSource
open ClockPhiCorrectedHamiltonianWorkGenerator MeasureTheory Filter
open scoped ContDiff Topology InnerProductSpace
private abbrev A := combinedConjugate
private abbrev U := inverseVolumeAction
private abbrev D := combinedGenerator
private abbrev n : ℝ := sourceTime 0
private abbrev γ := ProbabilityTheory.gaussianReal 0 1
private abbrev G (s : ℝ) := SourceClockPhiActualCovarianceStep.sourceGain (Real.sqrt s)
attribute [local irreducible] diagonalAction embed
private theorem root_pair (f g : QuantumTest) :
    sourcePair (inverseRootAction f) g = sourcePair f (inverseRootAction g) := (multiply_pair _ _ f g).symm
private theorem gain_pair (s : ℝ) (f g : QuantumTest) :
    sourcePair (G s f) g = sourcePair f (G s g) := (multiply_pair _ _ f g).symm
private theorem complete_pair (s : ℝ) (hs : 0 < s) (ξ η : ℝ) (f g : QuantumTest) :
    sourcePair (correctedCompleteCore s hs ξ η f) (correctedCompleteCore s hs ξ η g) =
      sourcePair (G s f) (G s g) := by
  change sourcePair (sourceForwardCore s hs.le (correctedProfileCore s hs ξ η (G s f)))
    (sourceForwardCore s hs.le (correctedProfileCore s hs ξ η (G s g))) = _
  rw [SourceClockPhiCoframeForwardPair.actual_forward_core_pair]
  exact clockProfileAction_pair _ _ _ _ _ _
private theorem gain_inverse_power (s : ℝ) (hs : 0 < s) (f : QuantumTest) :
    G s (G s (forwardUAction s hs.le f)) = U (gaussianProfileWeight s hs (-2/3) f) := by
  apply DFunLike.ext
  intro z
  by_cases hz : z ∈ physicalChart
  · have hr := forward_ratio_pos s hs.le ⟨z,hz⟩
    have hg : SourceClockPhiActualCovarianceStep.gainProfile (Real.sqrt s) z ^ 2 = (forwardRatio s z)^(1/3:ℝ) := by
      unfold SourceClockPhiActualCovarianceStep.gainProfile
      rw [Real.sq_sqrt hs.le,←Real.rpow_natCast,←Real.rpow_mul hr.le]
      norm_num
    have hp : (forwardRatio s z)^(1/3:ℝ) = (forwardRatio s z)^(-2/3:ℝ)*forwardRatio s z := by
      calc _ = (forwardRatio s z)^((-2/3:ℝ)+1) := by norm_num
           _ = _ := by rw [Real.rpow_add hr,Real.rpow_one]
    have hu : forwardU s z*forwardRatio s z = reciprocalVolume z := by
      unfold forwardU forwardRatio reciprocalVolume
      field_simp [(volume_pos ⟨z,hz⟩).ne',ne_of_gt (by linarith [volume_pos ⟨z,hz⟩] : 0 < volume z+18*s)]
    have he : SourceClockPhiActualCovarianceStep.gainProfile (Real.sqrt s) z*
        (SourceClockPhiActualCovarianceStep.gainProfile (Real.sqrt s) z*forwardU s z) =
        reciprocalVolume z*(forwardRatio s z)^(-2/3:ℝ) := by
      calc _ = SourceClockPhiActualCovarianceStep.gainProfile (Real.sqrt s) z^2*forwardU s z := by ring
           _ = _ := by rw [hg,hp];linear_combination (norm:=ring) (forwardRatio s z)^(-2/3:ℝ)*hu
    change (SourceClockPhiActualCovarianceStep.gainProfile (Real.sqrt s) z:ℂ) •
      ((SourceClockPhiActualCovarianceStep.gainProfile (Real.sqrt s) z:ℂ) • ((forwardU s z:ℂ) • f z)) =
      (reciprocalVolume z:ℂ) • ((((forwardRatio s z)^(-2/3:ℝ):ℝ):ℂ) • f z)
    simpa only [Complex.ofReal_mul,mul_smul] using congrArg (fun r:ℝ => (r:ℂ) • f z) he
  · have hzero (q : QuantumTest) : q z = 0 := image_eq_zero_of_notMem_tsupport (fun h => hz (q.tsupport_subset h))
    exact (hzero _).trans (hzero _).symm

/-- The payment potential is the original A-square on the same actual corrected source. -/
theorem actual_corrected_A_clock_potential (s : ℝ) (hs : 0 < s) (ξ η : ℝ) (f : QuantumTest) :
    clockPotential s hs f = (‖embed (A (correctedCompleteCore s hs ξ η f))‖^2 : ℂ) := by
  have hA (q : QuantumTest) : sourcePair (A q) (A q) = sourcePair (D q) (U (D q)) := by
    change sourcePair (inverseRootAction (D q)) (inverseRootAction (D q)) = _
    rw [root_pair,inverse_root_square]
  have hD := LinearMap.congr_fun (actual_corrected_complete_generator_commute s hs ξ η).eq f
  have hU := LinearMap.congr_fun (actual_corrected_complete_inverse_volume s hs ξ η) (D f)
  change D (correctedCompleteCore s hs ξ η f) = correctedCompleteCore s hs ξ η (D f) at hD
  change U (correctedCompleteCore s hs ξ η (D f)) = correctedCompleteCore s hs ξ η (forwardUAction s hs.le (D f)) at hU
  have hpair : sourcePair (A (correctedCompleteCore s hs ξ η f))
      (A (correctedCompleteCore s hs ξ η f)) = clockPotential s hs f := by
    rw [hA,hD,hU,complete_pair,gain_pair,gain_inverse_power]
    unfold clockPotential
    change _ = sourcePair (inverseRootAction (D f)) (gaussianProfileWeight s hs (-2/3) (inverseRootAction (D f)))
    have hw (q : QuantumTest) : gaussianProfileWeight s hs (-2/3) (inverseRootAction q) =
        inverseRootAction (gaussianProfileWeight s hs (-2/3) q) := by
      apply DFunLike.ext
      intro z
      exact smul_comm (((forwardRatio s z)^(-2/3:ℝ):ℝ):ℂ) (inverseRootVolume z:ℂ) (q z)
    rw [hw,root_pair,inverse_root_square]
  rw [←hpair]
  simpa only [sourcePair,Complex.ofReal_pow] using!
    inner_self_eq_norm_sq_to_K (𝕜:=ℂ) (embed (A (correctedCompleteCore s hs ξ η f)))

/-- The same normalized finite physical work inherits the existing Noether UD debit exactly. -/
theorem actual_normalized_finite_physical_noether_work
    (s h : ℝ) (hs : 0 < s) (hh : 0 < h) (ξ η : ℝ)
    (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im ≠ 0) (g : diagonal.domain) :
    let w := normalizedState m ell F z hz g
    (correctedHamiltonianPair (s+h) (add_pos hs hh) w w-correctedHamiltonianPair s hs w w).re +
      (n/1152)*((clockPotential (s+h) (add_pos hs hh) w).re-(clockPotential s hs w).re) =
      (∫ x : ℝ×ℝ, correctedHamiltonianWork h hh
        (correctedCompleteCore s hs x.1 x.2 w) (correctedCompleteCore s hs x.1 x.2 w) ∂γ.prod γ).re -
      (n/96)*(∫ t in s..(s+h), actualClockUDSquare t ξ η w) := by
  dsimp only
  let w := normalizedState m ell F z hz g
  have hw := (actual_corrected_hamiltonian_finite_work_increment h s hh hs w w).2
  simp only [add_comm h s] at hw
  rw [hw]
  have ht := actual_finite_clock_UD_payment (s+h) (add_pos hs hh) ξ η w
  have hzero := actual_finite_clock_UD_payment s hs ξ η w
  have hi := intervalIntegral.integral_interval_sub_left ht.1 hzero.1
  dsimp only [w] at *
  linear_combination (norm:=ring) (n/1152)*(ht.2-hzero.2)-(n/96)*hi

/-- The complete positive-s Q(H0) law and the original Noether debit generate one actual work jet. -/
theorem actual_normalized_positive_clock_noether_generator
    (s : ℝ) (hs : 0 < s) (ξ η : ℝ)
    (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im ≠ 0) (g : diagonal.domain) :
    let w := normalizedState m ell F z hz g
    Tendsto (fun h : ℝ => if hh : 0 < h then (h:ℂ)⁻¹ *
      (correctedHamiltonianPair (s+h) (add_pos hs hh) w w-correctedHamiltonianPair s hs w w +
        ((n/1152:ℝ):ℂ)*(clockPotential (s+h) (add_pos hs hh) w-clockPotential s hs w)) else 0)
      (𝓝[>] (0:ℝ))
      (𝓝 ((∫ x : ℝ×ℝ, sourcePair (correctedCompleteCore s hs x.1 x.2 w)
        (completeCurrent diagonalAction (correctedCompleteCore s hs x.1 x.2 w)) ∂γ.prod γ) -
        ((n/96:ℝ):ℂ)*(‖embed (U (D (correctedCompleteCore s hs ξ η w)))‖^2:ℂ))) := by
  dsimp only
  let w := normalizedState m ell F z hz g
  have hH := actual_corrected_hamiltonian_positive_time_Q_H0 s hs w w
  have hP := (actual_UD_clock_primitive_slope s hs ξ η w).const_mul ((n/1152:ℝ):ℂ)
  have he : ((n/1152:ℝ):ℂ)*(-12) = -((n/96:ℝ):ℂ) := by push_cast;ring
  have h := hH.add hP
  rw [←mul_assoc,he,neg_mul,←sub_eq_add_neg] at h
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  have ht' : 0 < t := ht
  dsimp only [w]
  simp only [dif_pos ht']
  ring
end LowEnergy.FirstCurrentPayer
