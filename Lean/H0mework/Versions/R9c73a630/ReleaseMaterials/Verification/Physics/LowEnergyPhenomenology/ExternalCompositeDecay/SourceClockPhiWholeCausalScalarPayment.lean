import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiScalarCausalPositiveCurrent
import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiWholeReverseFrequencyWork
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.ScalarCausalFrequencyMoment
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussNativeForm
open GaussDiagonalHistory GaussUnitaryHistory GaussNativeEnergy SourceQuantumConfigurationHilbert
open SourceScalarEssentialBudget SourceScalarDoubleCurrent SourceScalarPositiveBulkWard SourceScalarShiftedBulk
open SourceClockPhiNormalizedScalarBudget SourceLocalizedInverseFormPayment SourceResolventBandLimit
open FirstCurrentWholeCarrier FirstCurrentAdmissibleElectric FirstCurrentJointBudget
open ReverseNativeClock ReverseNativeFrequencyWard ClockPhiHeatCorrectedCovarianceSource
open SourceJointResidualEnergy MeasureTheory Filter
open scoped Topology InnerProductSpace
attribute [local irreducible] sourcePair embed scalarBulkComplete wholeClockState wholeResponseDerivative

private theorem frequency_positive (half : Bool) : 0 < sourceNoetherFrequency half := by
  have hn : 0 < sourceTime 0 := by
    rw [source_time_generated]
    exact SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair.lapse_pos
  linarith [actual_source_noether_gap half]
private theorem causal_pole_actual (advanced : Bool) (μ a q : ℝ) :
    causalPole advanced μ a q = ((a : ℂ)-actualFrequency advanced μ q)⁻¹ := by
  cases advanced <;> simp [causalPole, pole, actualFrequency]
private theorem whole_wave (s : ℝ) (hs : 0 < s) (half advanced : Bool) (m ell : ℕ) (F : Index)
    (g : diagonal.domain) (x : ℝ×ℝ) (q : ℝ) :
    scalarFrequencyWave advanced (sourceNoetherFrequency half) (channelValue F)
      (wholeClockColumn s hs half advanced m ell F g x) q =
        wholeClockState s hs half advanced m ell F g x q := by
  rw [actual_whole_clock_channels]
  unfold scalarFrequencyWave
  simp_rw [causal_pole_actual]
private theorem whole_derivative (s : ℝ) (hs : 0 < s) (half advanced : Bool) (m ell : ℕ) (F : Index)
    (g : diagonal.domain) (x : ℝ×ℝ) (q : ℝ) :
    scalarFrequencyDerivative advanced (sourceNoetherFrequency half) (channelValue F)
      (wholeClockColumn s hs half advanced m ell F g x) q =
        wholeResponseDerivative s hs half advanced m ell F g x q := by
  rw [actual_whole_clock_derivative_channels]
  unfold scalarFrequencyDerivative
  simp_rw [causal_pole_actual]
private theorem physical_im (advanced : Bool) (μ q : ℝ) :
    (actualFrequency advanced μ q).im = causalDirection advanced*μ := by
  cases advanced <;> simp [actualFrequency, causalDirection, line_im]

/-- The original whole-source virtual-frequency cross is paid by its actual
causal scalar profile. Both chosen electric steps and all source columns stay. -/
theorem actual_whole_scalar_causal_cross_payment (s : ℝ) (hs : 0 < s) (half advanced : Bool)
    (m ell : ℕ) (F : Index) (g : diagonal.domain) (x : ℝ×ℝ) :
    Integrable (fun q : ℝ => sourcePair (wholeResponseDerivative s hs half advanced m ell F g x q)
      (scalarBulkComplete (wholeClockState s hs half advanced m ell F g x q))) ∧
    (∫ q : ℝ, (actualFrequency advanced (sourceNoetherFrequency half) q).im*
      (sourcePair (wholeResponseDerivative s hs half advanced m ell F g x q)
        (scalarBulkComplete (wholeClockState s hs half advanced m ell F g x q))).im) ≤ 0 := by
  have h := actual_scalar_causal_frequency_cross_payment advanced (sourceNoetherFrequency half)
    (frequency_positive half) (channelValue F) (wholeClockColumn s hs half advanced m ell F g x)
  simp_rw [whole_derivative, whole_wave] at h
  refine ⟨h.1, ?_⟩
  simp_rw [physical_im]
  rw [integral_const_mul]
  exact h.2
end LowEnergy.ScalarCausalFrequencyMoment
