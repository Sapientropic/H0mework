import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiCoframeGaussianVariance
import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiCorrectedQuadraticCarrier
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section
namespace LowEnergy.FirstCurrentPayerNext
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussNativeForm GaussNativeEnergy
open GaussDiagonalHistory GaussUnitaryHistory SourceQuantumConfigurationHilbert
open SourceClockPhiCombinedScalePressure SourceClockPhiCorrectedWeightTransport
open ClockPhiHeatCorrectedCovarianceSource SourceClockPhiNativeMatchedSource
open SourceClockPhiMatchedDiffusionSource SourceClockPhiNormalizedScalarBudget SourceCoframeCovariantAction
open FinitePhysicalSource JointElectricSource MeasureTheory Filter
open scoped InnerProductSpace
private abbrev End := QuantumTest →ₗ[ℂ] QuantumTest
private abbrev n : ℝ := sourceTime 0
private abbrev α : ℝ := 144/n
private abbrev γ := ProbabilityTheory.gaussianReal 0 1
private abbrev A := combinedConjugate
private abbrev U := SourcePhysicalKineticSquare.inverseVolumeAction
private abbrev C := SourceScalarDoubleCurrent.bracket diagonalAction A
private theorem n_positive : 0 < n := by
  change 0 < sourceTime 0
  rw [source_time_generated]
  exact SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair.lapse_pos

def originalComplement : End := diagonalAction-covariantKinetic
def updatedForcing (t : ℝ) (ht : 0 < t) (x : ℝ×ℝ)
    (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im ≠ 0) (g : diagonal.domain) : QuantumTest :=
  correctedCompleteCore t ht x.1 x.2 (normalizedForcing m ell F z hz g)+
    SourceScalarDoubleCurrent.bracket diagonalAction (correctedCompleteCore t ht x.1 x.2)
      (normalizedState m ell F z hz g)
def coframeForcing (t : ℝ) (ht : 0 < t) (x : ℝ×ℝ) (z : ℂ) (w : QuantumTest) : QuantumTest :=
  covariantKinetic (correctedCompleteCore t ht x.1 x.2 w)-z • correctedCompleteCore t ht x.1 x.2 w
def coframeCompleted (t : ℝ) (ht : 0 < t) (x : ℝ×ℝ) (z : ℂ) (w : QuantumTest) : QuantumTest :=
  matchedTester (correctedCompleteCore t ht x.1 x.2 w)+(α:ℂ) • coframeForcing t ht x z w

theorem actual_corrected_full_forcing (t : ℝ) (ht : 0 < t) (x : ℝ×ℝ)
    (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im ≠ 0) (g : diagonal.domain) :
    let w := normalizedState m ell F z hz g
    diagonalAction (correctedCompleteCore t ht x.1 x.2 w) =
      updatedForcing t ht x m ell F z hz g+z • correctedCompleteCore t ht x.1 x.2 w := by
  dsimp only
  have h := actual_full_normalized_source m ell F z hz g
  unfold updatedForcing SourceScalarDoubleCurrent.bracket
  simp only [Module.End.mul_apply,LinearMap.sub_apply,h,map_add,map_smul]
  module
private theorem forcing_split (t : ℝ) (ht : 0 < t) (x : ℝ×ℝ)
    (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im ≠ 0) (g : diagonal.domain) :
    updatedForcing t ht x m ell F z hz g =
      coframeForcing t ht x z (normalizedState m ell F z hz g)+
      originalComplement (correctedCompleteCore t ht x.1 x.2 (normalizedState m ell F z hz g)) := by
  have h := actual_corrected_full_forcing t ht x m ell F z hz g
  dsimp only at h
  unfold coframeForcing originalComplement
  simp only [LinearMap.sub_apply]
  linear_combination (norm:=module) -h

private theorem quadratic_add (v w : QuadraticIndex → QuantumTest) (x : ℝ×ℝ) :
    quadraticSource (v+w) x = quadraticSource v x+quadraticSource w x := by
  simp only [quadraticSource,Pi.add_apply,smul_add,Finset.sum_add_distrib]
private theorem quadratic_smul (c : ℂ) (v : QuadraticIndex → QuantumTest) (x : ℝ×ℝ) :
    quadraticSource (c • v) x = c • quadraticSource v x := by
  simp only [quadraticSource,Pi.smul_apply,smul_smul,Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [mul_comm]
private def singleColumn (a : QuadraticIndex) (f : QuantumTest) : QuadraticIndex → QuantumTest :=
  fun b => if b=a then f else 0
private theorem quadratic_single (a : QuadraticIndex) (f : QuantumTest) (x : ℝ×ℝ) :
    quadraticSource (singleColumn a f) x = (noiseQuadratic a x:ℂ) • f := by
  classical
  unfold quadraticSource singleColumn
  rw [Finset.sum_eq_single a]
  · simp
  · intro b _ hb
    simp [hb]
  · intro ha
    exact (ha (Finset.mem_univ a)).elim
private theorem affine_source (q₀ q₁ q₂ : QuantumTest) (x : ℝ×ℝ) :
    quadraticSource (singleColumn (0,0) q₀+singleColumn (1,0) q₁+singleColumn (2,0) q₂) x =
      q₀+(x.1:ℂ) • q₁+(x.2:ℂ) • q₂ := by
  rw [quadratic_add,quadratic_add,quadratic_single,quadratic_single,quadratic_single]
  simp only [noiseQuadratic,(noiseLinear_values x).1,(noiseLinear_values x).2.1,
    (noiseLinear_values x).2.2,mul_one,Complex.ofReal_one,one_smul]

def coframeJointPacket (t : ℝ) (ht : 0 < t) (z : ℂ) (w : QuantumTest) : QuadraticIndex → QuantumTest :=
  singleColumn (0,0) (matchedTester w-((α:ℂ)*z) • w)+
    singleColumn (1,0) (-(noiseAction t ht 1 0 (combinedGenerator w)))+
    singleColumn (2,0) (-(noiseAction t ht 0 1 (combinedGenerator w)))+
    (α:ℂ) • (fun a => coframeQuadraticColumn t ht a w)
private theorem noise_linear (t : ℝ) (ht : 0 < t) (x : ℝ×ℝ) (f : QuantumTest) :
    noiseAction t ht x.1 x.2 f=(x.1:ℂ) • noiseAction t ht 1 0 f+(x.2:ℂ) • noiseAction t ht 0 1 f := by
  apply DFunLike.ext
  intro z
  change (covarianceNoise t x.1 x.2 z:ℂ) • f z =
    (x.1:ℂ) • ((covarianceNoise t 1 0 z:ℂ) • f z)+(x.2:ℂ) • ((covarianceNoise t 0 1 z:ℂ) • f z)
  rw [actual_covariance_noise_affine]
  simp only [Complex.ofReal_add,Complex.ofReal_mul,add_smul,mul_smul]

theorem actual_coframe_joint_carrier (t : ℝ) (ht : 0 < t) (x : ℝ×ℝ) (z : ℂ) (w : QuantumTest) :
    embed (coframeCompleted t ht x z w) = correctedQuadraticColumn t ht (coframeJointPacket t ht z w) x := by
  unfold coframeCompleted coframeForcing correctedQuadraticColumn coframeJointPacket
  rw [quadratic_add,quadratic_smul,affine_source,actual_corrected_complete_matched_tester,
    actual_corrected_coframe_quadratic_return,noise_linear]
  simp only [map_add,map_sub,map_smul,map_neg,smul_neg]
  module

/-- The original full forcing loses its native square and all coframe-native quadratic cross terms jointly.
The remaining native leg retains its full first-order coupling to the same matched tester. -/
theorem actual_full_forcing_joint_cancellation (t : ℝ) (ht : 0 < t) (x : ℝ×ℝ)
    (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im ≠ 0) (g : diagonal.domain) :
    let w := normalizedState m ell F z hz g
    let u := correctedCompleteCore t ht x.1 x.2 w
    let f := updatedForcing t ht x m ell F z hz g
    (432/n)*‖embed f‖^2-(n/48)*‖embed (matchedTester u)+(α:ℂ) • embed f‖^2 =
      (432/n)*‖embed (coframeForcing t ht x z w)‖^2-(n/48)*‖embed (coframeCompleted t ht x z w)‖^2-
      6*(sourcePair (matchedTester u) (originalComplement u)).re := by
  dsimp only
  rw [forcing_split]
  unfold coframeCompleted
  simp only [map_add,map_smul]
  rw [←FiniteCausalSylvester.noether_clock_square n n_positive,
    ←FiniteCausalSylvester.noether_clock_square n n_positive]
  simp only [sourcePair,inner_add_right,Complex.add_re]
  ring

/-- The negative completed square has its own actual Gaussian mean and nonnegative variance cost. -/
theorem actual_normalized_coframe_completed_variance (t : ℝ) (ht : 0 < t)
    (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im ≠ 0) (g : diagonal.domain) :
    let w := normalizedState m ell F z hz g
    let v := coframeJointPacket t ht z w
    Integrable (fun x : ℝ×ℝ => embed (coframeCompleted t ht x z w)) (γ.prod γ) ∧
    Integrable (fun x : ℝ×ℝ => ‖embed (coframeCompleted t ht x z w)‖^2) (γ.prod γ) ∧
    -(n/48)*(∫ x : ℝ×ℝ, ‖embed (coframeCompleted t ht x z w)‖^2 ∂γ.prod γ) =
      -(n/48)*‖correctedQuadraticMean t ht v‖^2-
      (n/48)*(∫ x : ℝ×ℝ, ‖embed (coframeCompleted t ht x z w)-correctedQuadraticMean t ht v‖^2 ∂γ.prod γ) ∧
    -(n/48)*(∫ x : ℝ×ℝ, ‖embed (coframeCompleted t ht x z w)‖^2 ∂γ.prod γ) ≤
      -(n/48)*‖correctedQuadraticMean t ht v‖^2 := by
  dsimp only
  let v := coframeJointPacket t ht z (normalizedState m ell F z hz g)
  have h := actual_corrected_quadratic_carrier t ht v
  simp_rw [actual_coframe_joint_carrier]
  refine ⟨h.1,h.2.1,?_,?_⟩
  · rw [h.2.2.1,h.2.2.2.2.1]
    ring
  · rw [h.2.2.1]
    have hp : 0 ≤ n/48 := div_nonneg n_positive.le (by norm_num)
    nlinarith [mul_nonneg hp h.2.2.2.2.2]
end LowEnergy.FirstCurrentPayerNext
