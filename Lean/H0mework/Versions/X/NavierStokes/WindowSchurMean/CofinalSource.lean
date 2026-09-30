import H0mework.Versions.X.NavierStokes.WindowSchurMean.StrongBilinear
import H0mework.Versions.X.NavierStokes.WindowSourceGreen.Coefficients.Tail

set_option autoImplicit false
open scoped BigOperators Topology ENNReal
namespace SaturationMonoid.NavierStokes.NativeWindowHistoryMeanCofinalSource
open Set Filter
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityWeakEndpoint
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellStrongContinuationEnergyLedger
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingTangentCoercivity
open ThreeDimensionalVorticityCoefficientGeneratedShellSerrinGeometry
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointGalerkinInitialConvergence
open NativeWholeResolvent (wholePhysical)
open NativeWholeH1Mixed (modes modes_zero)
open NativeEndpointVelocityCarrier (wholeVelocity)
open NativeWindowHistoryMeanStrongBilinear
open NativeUnheatedSexticLatticePower (radical)
open NativeWindowSobolevVelocity (state state_row)
noncomputable section
variable {nu : Viscosity}

def value (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) : wholePhysical :=
  NativeWindowHistoryMeanProjection.mean (NativeWindowTraceWholeHistory.history seed time)

theorem value_original (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) :
    (value seed time).1=NativeForwardWindowEvolution.velocityJet seed 0 time := by
  rw [value,NativeWindowHistoryMeanProjection.source_mean]
  simp only [NativeForwardWindowEvolution.velocityJet,NativeForwardWindowJets.jet_zero]

theorem density_original (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (k : IntegerWavevector) :
    density 3 (value seed time) k=NativeWindowSobolevVelocity.wholeDensity seed 0 time k := by
  rw [density,value_original,euclideanCoordinateRow_norm_sq]
  have power : radical k^(2*3)=(1+integerWaveNormSq k)*Real.sqrt (1+integerWaveNormSq k) := by
    rw [show radical k^(2*3)=radical k^4*radical k^2 by ring,
      NativeUnheatedSexticLatticePower.radical_fourth,NativeUnheatedSexticLatticePower.radical_square]
    rfl
  rw [power]
  rfl

theorem regular (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (valid : -1<time) :
    Regular 3 (value seed time) := by
  exact (NativeWindowSobolevVelocity.whole_summable seed 0 time valid).congr
    (fun k => (density_original seed time k).symm)

theorem mass_bound (seed : GeneratedWholeRestartCurrent nu) (time horizon : ℝ) (valid : -1<time)
    (before : time ≤ horizon) : mass 3 (value seed time) ≤  NativeWindowSobolevVelocity.budget seed 0 horizon := by
  simpa only [mass,density_original] using NativeWindowSobolevVelocity.whole_bound_on_interval seed 0 time horizon valid before

theorem read_row (M : ℕ) (v : WholeRestartVelocityEndpointState) (k : NonzeroIntegerWavevector) :
    NativeWindowHistoryMeanTime.read M v k=if k.1∈modes M then v k else 0 := by
  rw [NativeWindowHistoryMeanTime.read_original,wholeRestartVelocityEndpointGalerkinInitialVelocity_apply]
  rfl

theorem difference_mass (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (valid : -1<time) :
    mass 3 (value seed time-NativeWholeH1Approximation.project M (value seed time))=
      ‖state seed 0 time valid-NativeWindowHistoryMeanTime.read M (state seed 0 time valid)‖^2 := by
  have support : Function.support (density 3 (value seed time-NativeWholeH1Approximation.project M (value seed time)))⊆{k | k≠0} := by
    intro k included
    by_contra zero
    have eq:k=0:=not_ne_iff.mp zero
    subst k
    apply included
    simp only [density,NativeEndpointVelocityCarrier.wholeVelocity_zero,
      show euclideanCoordinateRow (0 : ComplexCoordinateVector)=0 from rfl,norm_zero,
      zero_pow (by norm_num : (2:ℕ)≠0),mul_zero]
  have source:=NativeWindowMotherCoefficientForm.square_sum
    (state seed 0 time valid-NativeWindowHistoryMeanTime.read M (state seed 0 time valid))
  have actual (k : NonzeroIntegerWavevector) :
      density 3 (value seed time-NativeWholeH1Approximation.project M (value seed time)) k.1=
        ‖(state seed 0 time valid-NativeWindowHistoryMeanTime.read M (state seed 0 time valid)) k‖^2 := by
    rw [density_difference]
    change _=‖state seed 0 time valid k-NativeWindowHistoryMeanTime.read M (state seed 0 time valid) k‖^2
    rw [read_row]
    split_ifs
    · simp only [sub_self,norm_zero,zero_pow (by norm_num : (2:ℕ)≠0)]
    · rw [sub_zero,density_original,state_row,norm_smul,mul_pow,Real.norm_eq_abs,sq_abs,NativeWindowSobolevVelocity.multiplier_sq]
      simp only [NativeWindowSobolevVelocity.wholeDensity,NativeUnheatedWindowGradient.whole_row_mass]
  have punctured : HasSum (fun k : NonzeroIntegerWavevector =>
      density 3 (value seed time-NativeWholeH1Approximation.project M (value seed time)) k.1)
      (‖state seed 0 time valid-NativeWindowHistoryMeanTime.read M (state seed 0 time valid)‖^2) := by
    simpa only [actual] using source
  exact ((hasSum_subtype_iff_of_support_subset support).mp punctured).tsum_eq

theorem uniform_tail (seed : GeneratedWholeRestartCurrent nu) (horizon epsilon : ℝ) (positive : 0<epsilon) :
    ∃low : ℕ,∀M ≥ low,∀time∈Icc (0:ℝ) horizon,
      mass 3 (value seed time-NativeWholeH1Approximation.project M (value seed time))<epsilon := by
  obtain ⟨F,paid⟩:=NativeWindowMotherCoefficientForm.exists_uniform_high seed 0 horizon (Real.sqrt epsilon) (by positivity)
  obtain ⟨low,covered⟩:=(Filter.eventually_atTop.1 (NativeWindowStressOseenSource.cover_eventually (F.image Subtype.val)))
  refine ⟨low,fun M above time inside => ?_⟩
  have valid:-1<time:=by linarith [inside.1]
  have point (k : NonzeroIntegerWavevector) :
      ‖(state seed 0 time valid-NativeWindowHistoryMeanTime.read M (state seed 0 time valid)) k‖ ≤
        ‖NativeWindowMotherCoefficientForm.high F (state seed 0 time valid) k‖ := by
    change ‖state seed 0 time valid k-NativeWindowHistoryMeanTime.read M (state seed 0 time valid) k‖ ≤ _
    rw [read_row]
    change _ ≤ ‖if k∈F then 0 else state seed 0 time valid k‖
    by_cases kept : k.1∈modes M
    · rw [if_pos kept,sub_self,norm_zero]
      exact norm_nonneg _
    · have outside:k∉F:=fun member => kept (covered M above k.1 (Finset.mem_image.mpr ⟨k,member,rfl⟩) k.2)
      rw [if_neg kept,if_neg outside,sub_zero]
  have bound:=(lp.norm_mono (p := (2:ℝ≥0∞)) (by norm_num) point).trans_lt (paid ⟨time,inside⟩)
  rw [difference_mass seed M time valid]
  have square:=(sq_lt_sq₀ (norm_nonneg _) (Real.sqrt_nonneg epsilon)).mpr bound
  rwa [Real.sq_sqrt positive.le] at square


theorem source_strong_error (seed : GeneratedWholeRestartCurrent nu) (horizon epsilon : ℝ) (positive : 0<epsilon) :
    ∃low : ℕ,∀M ≥ low,∀time∈Icc (0:ℝ) horizon,∀F : Finset IntegerWavevector,
      (∑k∈F,‖euclideanCoordinateRow (NativeWholeH1Mixed.row (value seed time) (value seed time) k-
        NativeWholeH1Mixed.finiteRow M (value seed time) (value seed time) k)‖^2) ≤ epsilon := by
  let B:=max 0 (NativeWindowSobolevVelocity.budget seed 0 horizon)
  let K:=4*NativeWindowHistoryAdjointSpatialFeedback.transportCap*B
  have K0:0 ≤ K:=by dsimp only [K,B]; positivity [NativeWindowHistoryAdjointSpatialFeedback.transportCap_nonnegative]
  obtain ⟨low,tail⟩:=uniform_tail seed horizon (epsilon/(K+1)) (by positivity)
  refine ⟨low,fun M above time inside F => ?_⟩
  have valid:-1<time:=by linarith [inside.1]
  have original:=NativeWindowHistoryMeanStrongBilinear.observed_difference nu M (value seed time) (regular seed time valid) F
  have mass:mass 3 (value seed time) ≤ B:=(mass_bound seed time horizon valid inside.2).trans (le_max_right _ _)
  have coefficient:=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left mass
    (show 0 ≤ 4*NativeWindowHistoryAdjointSpatialFeedback.transportCap by positivity [NativeWindowHistoryAdjointSpatialFeedback.transportCap_nonnegative]))
      (mass_nonnegative 3 (value seed time-NativeWholeH1Approximation.project M (value seed time)))
  have high:=mul_le_mul_of_nonneg_left (tail M above time inside).le K0
  have last:K*(epsilon/(K+1)) ≤ epsilon := by
    rw [← mul_div_assoc,div_le_iff₀ (by linarith : 0<K+1)]
    nlinarith
  exact original.trans (coefficient.trans (high.trans last))

end
end SaturationMonoid.NavierStokes.NativeWindowHistoryMeanCofinalSource
