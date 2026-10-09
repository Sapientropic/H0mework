import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockResponse.SourceActualThreeParticleCutoffFamily
import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockResponse.SourceActualThreeParticleJointInsertion

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
noncomputable section
namespace LowEnergy.ActualThreeParticleCutoffFamily
open GaussCoreHilbert GaussCoreDifferential GaussUnitaryHistory GaussCoreLabel
open ActualThreeParticleCutoffGram ActualThreeParticleJointInsertion ActualCutoffFrequencyBase
open ActualVectorJointCost SourceFamilyHilbert FullYSourceFiniteTimeIntegral
open MeasureTheory Filter
open scoped Topology InnerProductSpace

private theorem finite_difference_square (F : Index) (m ell : ℕ) (advanced : Bool)
    (μ : ℝ) (hμ : 0<μ) (q : QuantumTest) (hq : project (3,0) q=q) :
    ‖finiteResponse F ell advanced μ hμ q hq-finiteResponse F m advanced μ hμ q hq‖^2=
      ∫w : ℝ,‖inverse F ell (frequency advanced μ w) (embed q)-
        inverse F m (frequency advanced μ w) (embed q)‖^2 := by
  rw [FullYSourceCutoffTimeGraph.square_integral]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_sub (finiteResponse F ell advanced μ hμ q hq)
    (finiteResponse F m advanced μ hμ q hq),
    actual_finite_response_read F ell advanced μ hμ q hq,
    actual_finite_response_read F m advanced μ hμ q hq] with w hs he hm
  rw [hs,Pi.sub_apply,he,hm]

/-- The original same-F cutoff difference generates the norm difference in
TimeSpace. No cross-F strong descent or n-limit is assumed. -/
theorem actual_frequency_difference_energy_limit (m ell : ℕ) (advanced : Bool)
    (μ : ℝ) (hμ : 0<μ) (q : QuantumTest) (hq : project (3,0) q=q) :
    Tendsto (fun F : Index => ∫w : ℝ,
      ‖inverse F ell (frequency advanced μ w) (embed q)-
        inverse F m (frequency advanced μ w) (embed q)‖^2) sourceFilter
      (𝓝 (‖sourceFrequency ell advanced μ hμ q hq-sourceFrequency m advanced μ hμ q hq‖^2)) := by
  have h := square_tendsto sourceFilter
    (responseFamily ell advanced μ hμ q hq-responseFamily m advanced μ hμ q hq)
  change Tendsto (fun F : Index =>
    ‖finiteResponse F ell advanced μ hμ q hq-finiteResponse F m advanced μ hμ q hq‖^2)
    sourceFilter (𝓝 (‖responseFamily ell advanced μ hμ q hq-responseFamily m advanced μ hμ q hq‖^2)) at h
  simp_rw [finite_difference_square] at h
  simpa only [sourceFrequency,←UniformSpace.Completion.coe_sub,UniformSpace.Completion.norm_coe] using h

/-- The three actual orthogonal grade tails are the full TimeSpace difference price. -/
theorem actual_three_grade_difference_energy_limit (m ell : ℕ) (advanced : Bool)
    (μ : ℝ) (hμ : 0<μ) (q : QuantumTest) (hq : project (3,0) q=q) :
    Tendsto (fun F : Index => ∫w : ℝ,∑j : Fin 3,
      ‖embed (differenceLeg F m ell (frequency advanced μ w)
        (frequency_nonreal advanced μ hμ w) q (j.val+1))‖^2) sourceFilter
      (𝓝 (‖sourceFrequency ell advanced μ hμ q hq-sourceFrequency m advanced μ hμ q hq‖^2)) := by
  have h := actual_frequency_difference_energy_limit m ell advanced μ hμ q hq
  have he (F : Index) :
      (∫w : ℝ,‖inverse F ell (frequency advanced μ w) (embed q)-
        inverse F m (frequency advanced μ w) (embed q)‖^2)=
      ∫w : ℝ,∑j : Fin 3,‖embed (differenceLeg F m ell (frequency advanced μ w)
        (frequency_nonreal advanced μ hμ w) q (j.val+1))‖^2 := by
    apply integral_congr_ae
    exact Eventually.of_forall (fun w => actual_response_difference_norm F m ell _
      (frequency_nonreal advanced μ hμ w) q hq)
  simpa only [he] using h

/-- All six joint/Hardy insertions, including their within-grade interference,
feed the same original TimeSpace norm before any cutoff-Cauchy estimate. -/
theorem actual_joint_hardy_difference_energy_limit (m ell : ℕ) (advanced : Bool)
    (μ : ℝ) (hμ : 0<μ) (q : QuantumTest) (hq : project (3,0) q=q) :
    Tendsto (fun F : Index => ∫w : ℝ,∑j : Fin 3,‖∑r : Fin (j.val+1),
      -((step F m (frequency advanced μ w))^r.val)
        (jointVector advanced false m ell F μ (rightInput F ell (frequency advanced μ w) q j r) w+
         hardyVector advanced false m ell F μ (rightInput F ell (frequency advanced μ w) q j r) w)‖^2)
      sourceFilter
      (𝓝 (‖sourceFrequency ell advanced μ hμ q hq-sourceFrequency m advanced μ hμ q hq‖^2)) := by
  have h := actual_frequency_difference_energy_limit m ell advanced μ hμ q hq
  have he (F : Index) :
      (∫w : ℝ,‖inverse F ell (frequency advanced μ w) (embed q)-
        inverse F m (frequency advanced μ w) (embed q)‖^2)=
      ∫w : ℝ,∑j : Fin 3,‖∑r : Fin (j.val+1),
        -((step F m (frequency advanced μ w))^r.val)
          (jointVector advanced false m ell F μ (rightInput F ell (frequency advanced μ w) q j r) w+
           hardyVector advanced false m ell F μ (rightInput F ell (frequency advanced μ w) q j r) w)‖^2 := by
    apply integral_congr_ae
    exact Eventually.of_forall (fun w => actual_joint_hardy_response_norm F m ell advanced μ hμ q hq w)
  simpa only [he] using h

end LowEnergy.ActualThreeParticleCutoffFamily
