import H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKDirectRCofinalDivision.CountedVelocity
import H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.GenericFoundation.Scalar.Topological.Quadrature.FiniteCutoff

set_option autoImplicit false
set_option Elab.async false
set_option pp.deepTerms.threshold 25
set_option maxHeartbeats 130000

noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKDirectRCofinalDivision

open Filter BurnolPhysicalState Complex SourceGeneratedQuadrature
open OriginalRieszFinitePairing.CoPoisson.Ward CountedJointStrong
open scoped Topology

open private wave_source velocity_is_first_correction incidence_converges real_fourier from H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKDirectRCofinalDivision.CountedVelocity
open private endpoint_scale_fourier from H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKDirectRCofinalDivision.CountedEndpointLimit

local notation "Dilation" => burnolMultiplicativeDilation

private def doubleAction (direction : ℝ) : BurnolL2 →ₗᵢ[ℂ] BurnolL2 :=
  (Dilation (direction*Real.log 2)).toLinearIsometry

private def ratio : ℝ := (Real.sqrt 2)⁻¹

private theorem ratio_small : ‖ratio‖ < 1 := by
  unfold ratio
  rw [Real.norm_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _))]
  exact inv_lt_one_of_one_lt₀ Real.one_lt_sqrt_two

private theorem half_ratio_small : ‖ratio / 2‖ < 1 := by
  have small := ratio_small
  rw [norm_div, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  linarith

/-- Two finite counts at their original addresses, in the smaller cutoff's frame. -/
def finiteCountDifference (direction : ℝ) (count : Nat → BurnolL2) (m : Nat) : BurnolL2 :=
  countEndpointScale direction (m+1) (count (doubledCut m+1)-count (m+1))

private theorem scale_double (direction : ℝ) (m : Nat) (x : BurnolL2) :
    (countEndpointScale direction (m+1)) x =
      ratio • doubleAction direction (countEndpointScale direction (doubledCut m+1) x) := by
  let n : ℝ := (m : ℝ)+1
  have np : 0 < n := by dsimp [n]; positivity
  have index : ((doubledCut m+1 : Nat) : ℝ) = 2*n := by
    unfold doubledCut n
    push_cast
    ring
  have first : ((m+1 : Nat) : ℝ) = n := by simp [n]
  have root : (ratio : ℂ)*(Real.sqrt (2*n) : ℂ) = Real.sqrt n := by
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2), Complex.ofReal_mul,
      show (ratio : ℂ) = (Real.sqrt 2 : ℂ)⁻¹ by rw [ratio, Complex.ofReal_inv],
      ← mul_assoc, inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)).ne'), one_mul]
  have times : direction*Real.log 2 + -(direction*Real.log (2*n)) = -(direction*Real.log n) := by
    rw [Real.log_mul (by norm_num) np.ne']
    ring
  change (Real.sqrt ((m+1 : Nat) : ℝ) : ℂ) •
      Dilation (-(direction*Real.log ((m+1 : Nat) : ℝ))) x =
    ratio • Dilation (direction*Real.log 2) ((Real.sqrt ((doubledCut m+1 : Nat) : ℝ) : ℂ) •
      Dilation (-(direction*Real.log ((doubledCut m+1 : Nat) : ℝ))) x)
  rw [first, index, RCLike.real_smul_eq_coe_smul (K := ℂ), map_smul, smul_smul]
  change (Real.sqrt n : ℂ) • Dilation (-(direction*Real.log n)) x =
    ((ratio : ℂ)*(Real.sqrt (2*n) : ℂ)) •
      Dilation (direction*Real.log 2) (Dilation (-(direction*Real.log (2*n))) x)
  rw [root, burnolMultiplicativeDilation_add, times]

private theorem finite_difference_is_tail (direction : ℝ) (count : Nat → BurnolL2)
    (limit : BurnolL2) (m : Nat) :
    finiteCountDifference direction count m = countedTail direction count limit m -
      ratio • doubleAction direction (countedTail direction count limit (doubledCut m)) := by
  unfold finiteCountDifference countedTail
  rw [← scale_double, ← map_sub]
  congr 1
  abel

/-- The complete input and output are reconstructed from three finite vector counts. -/
def finiteCountIncidence (coordinate : BurnolCompletedMellinCoordinate) (direction : ℝ)
    (count : Nat → BurnolL2) (m : Nat) : BurnolL2 × BurnolL2 :=
  let leading := finiteCutoffLeading (doubleAction direction) ratio (finiteCountDifference direction count) m
  let velocity := finiteCutoffVelocity (doubleAction direction) ratio (finiteCountDifference direction count) m
  (incidenceInput coordinate leading velocity, (2 : ℝ) • leading)

private theorem count_difference_fourier (count : Nat → BurnolL2) (m : Nat) :
    fourierL2 (finiteCountDifference 1 count m) =
      finiteCountDifference (-1) (fun N => fourierL2 (count N)) m := by
  unfold finiteCountDifference
  rw [endpoint_scale_fourier, map_sub]

private theorem cutoff_inverse_fourier (r : ℝ) (small : ‖r‖ < 1) (x : BurnolL2) :
    fourierL2 (cutoffInverse (doubleAction 1) r x) =
      cutoffInverse (doubleAction (-1)) r (fourierL2 x) := by
  apply cutoff_inverse_intertwines (doubleAction 1) (doubleAction (-1))
    fourierL2.toContinuousLinearEquiv.toContinuousLinearMap _ r small x
  intro value
  change fourierL2 (Dilation (1 * Real.log 2) value) =
    Dilation (-1 * Real.log 2) (fourierL2 value)
  rw [fourierL2_burnolMultiplicativeDilation, one_mul, neg_one_mul]

private theorem cutoff_pair_fourier (count : Nat → BurnolL2) (m : Nat) :
    fourierL2 (cutoffPair (finiteCountDifference 1 count) m) =
      cutoffPair (finiteCountDifference (-1) (fun N => fourierL2 (count N))) m := by
  unfold cutoffPair
  rw [real_fourier, map_sub, count_difference_fourier, count_difference_fourier]

/-- Fourier transports the finite decoder at every cutoff. -/
theorem finite_count_incidence_fourier (coordinate : BurnolCompletedMellinCoordinate)
    (count : Nat → BurnolL2) (m : Nat) :
    Prod.map fourierL2 fourierL2 (finiteCountIncidence coordinate 1 count m) =
      finiteCountIncidence coordinate (-1) (fun N => fourierL2 (count N)) m := by
  unfold finiteCountIncidence
  simp only [Prod.map, incidenceInput, finiteCutoffLeading, finiteCutoffVelocity, map_sub, map_smul,
    real_fourier, cutoff_inverse_fourier ratio ratio_small, cutoff_inverse_fourier (ratio/2) half_ratio_small,
    count_difference_fourier]
  erw [cutoff_pair_fourier count m]
  rfl

private theorem finite_incidence_tendsto (coordinate : BurnolCompletedMellinCoordinate)
    (direction : ℝ) (count : Nat → BurnolL2) (limit x y : BurnolL2)
    (leading : Tendsto (countedTail direction count limit) atTop (𝓝 ((1/2 : ℝ) • y)))
    (velocity : Tendsto (fun m : Nat => velocityRead direction m limit (count (m+1)) y)
      atTop (𝓝 ((1/12 : ℂ) • (coordinate.value • y+(2 : ℂ) • x)))) :
    Tendsto (finiteCountIncidence coordinate direction count) atTop (𝓝 (x,y)) := by
  have correction := velocity.congr'
    (Eventually.of_forall (velocity_is_first_correction direction count limit y))
  have actual := finite_cutoff_coordinates (doubleAction direction) ratio ratio_small
    (finite_difference_is_tail direction count limit) leading correction
  have old := incidence_converges coordinate actual.fst_nhds actual.snd_nhds
  have born := actual.fst_nhds.const_smul (2 : ℝ)
  rw [smul_smul, show (2 : ℝ)*(1/2)=1 by norm_num, one_smul] at born
  exact old.prodMk_nhds born

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n : Nat, observation.coordinate = -2*(n+1))
variable (half : OriginalKCombCalculation.Half observation) (depth ordinal : Nat)
local notation "coord" => burnolDivisionZeroCompletedMellinCoordinate observation half.down
local notation "before" => D.raw observation nontrivial half depth (ordinal+1)
local notation "after" => D.raw observation nontrivial half depth (ordinal+1+1)
local notation "wave" => actualDivisionCompactWave observation nontrivial half depth (ordinal+1)

private theorem source_limits (coordinate : BurnolCompletedMellinCoordinate)
    {x y w : BurnolL2} (readWave : fourierL2 y = w)
    (slopes : ∃ l : BurnolL2, Tendsto (fun N : Nat => (DualSource.source N y, FiniteForcing.source N w))
        atTop (𝓝 (l, fourierL2 l)) ∧
      Tendsto (fun m : Nat => (velocityRead 1 m l (DualSource.source (m+1) y) y,
        velocityRead (-1) m (fourierL2 l) (FiniteForcing.source (m+1) w) w)) atTop
          (𝓝 ((1/12 : ℂ) • (coordinate.value • y+(2 : ℂ) • x),
            fourierL2 ((1/12 : ℂ) • (coordinate.value • y+(2 : ℂ) • x)))))
    (ends : ∃ l : BurnolL2, Tendsto (fun N : Nat => DualSource.source N y) atTop (𝓝 l) ∧
      Tendsto (countedTail 1 (fun N => DualSource.source N y) l) atTop (𝓝 ((1/2 : ℝ) • y)) ∧
      Tendsto (countedTail (-1) (fun N => FiniteForcing.source N w) (fourierL2 l))
        atTop (𝓝 ((1/2 : ℝ) • w))) :
    Tendsto (finiteCountIncidence coordinate 1 (fun N => DualSource.source N y)) atTop (𝓝 (x,y)) ∧
    Tendsto (finiteCountIncidence coordinate (-1) (fun N => FiniteForcing.source N w)) atTop
      (𝓝 (fourierL2 x,w)) := by
  obtain ⟨limit, counts, vel⟩ := slopes
  obtain ⟨old, c, lead, waveLead⟩ := ends
  have same := tendsto_nhds_unique c counts.fst_nhds
  subst old
  have waveVel := vel.snd_nhds
  have frequency : fourierL2 ((1/12 : ℂ) • (coordinate.value • y+(2 : ℂ) • x)) =
      (1/12 : ℂ) • (coordinate.value • w+(2 : ℂ) • fourierL2 x) := by
    rw [map_smul, map_add, map_smul, map_smul, readWave]
  rw [frequency] at waveVel
  exact ⟨finite_incidence_tendsto coordinate 1 _ limit x y lead vel.fst_nhds,
    finite_incidence_tendsto coordinate (-1) _ (fourierL2 limit) (fourierL2 x) w waveLead waveVel⟩

/-- Three literal cutoffs of each actual count feed the original before/after recovery. -/
theorem actual_finite_counted_incidence :
    Tendsto (finiteCountIncidence coord 1 (fun N => DualSource.source N after))
      atTop (𝓝 (before,after)) ∧
    Tendsto (finiteCountIncidence coord (-1) (fun N => FiniteForcing.source N wave))
      atTop (𝓝 (fourierL2 before,wave)) := by
  have readWave : @Eq BurnolL2 (fourierL2 after) wave := wave_source observation nontrivial half depth ordinal
  have identity : @Eq BurnolL2 (fourierL2.symm wave) after :=
    (congrArg fourierL2.symm readWave.symm).trans (fourierL2.symm_apply_apply after)
  have old := actual_division_counted_endpoint_limit observation nontrivial half depth (ordinal+1)
  let limit := old.choose
  have counted : Tendsto (fun N : Nat => DualSource.source N (fourierL2.symm wave)) atTop (𝓝 limit) :=
    old.choose_spec.2.1.fst_nhds
  have head : Tendsto (countedTail 1 (fun N => DualSource.source N (fourierL2.symm wave)) limit)
      atTop (𝓝 ((1/2 : ℝ) • fourierL2.symm wave)) := old.choose_spec.2.2.fst_nhds
  have waveHead : Tendsto (countedTail (-1) (fun N => FiniteForcing.source N wave) (fourierL2 limit))
      atTop (𝓝 ((1/2 : ℝ) • wave)) := old.choose_spec.2.2.snd_nhds
  rw [identity] at counted head
  exact source_limits coord readWave
    (actual_counted_velocity observation nontrivial half depth ordinal) ⟨limit,counted,head,waveHead⟩

/-- Both branches read the same three actual counts in their own coordinates. -/
theorem actual_finite_counted_incidence_fourier (m : Nat) :
    Prod.map fourierL2 fourierL2 (finiteCountIncidence coord 1
      (fun N => DualSource.source N after) m) =
      finiteCountIncidence coord (-1) (fun N => FiniteForcing.source N wave) m := by
  have readWave : @Eq BurnolL2 (fourierL2 after) wave :=
    wave_source observation nontrivial half depth ordinal
  have counts : (fun N => fourierL2 (DualSource.source N after)) =
      (fun N => FiniteForcing.source N wave) := by
    funext N
    exact (OriginalGamma.Source.CountingQuadraticLimit.source_fourier N after).symm.trans
      (congrArg (FiniteForcing.source N) readWave)
  exact (finite_count_incidence_fourier coord (fun N => DualSource.source N after) m).trans
    (congrArg (fun count => finiteCountIncidence coord (-1) count m) counts)

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKDirectRCofinalDivision
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
