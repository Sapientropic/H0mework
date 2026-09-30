import H0mework.Physics.LowEnergy.Quantum.GaussFockWeights
import H0mework.Physics.LowEnergy.Quantum.GaussDensityCore

set_option autoImplicit false
set_option maxHeartbeats 1500000
noncomputable section
namespace LowEnergy.GaussFockPair
open GaussDensityCore GaussFockWeights GaussNativeMatter GaussCoreDifferential GaussCoreHilbert
open SourceQuantumScalarChart SourceQuantumConfigurationHilbert SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open MeasureTheory Set
open scoped ContDiff Distributions

private theorem complexDensity_continuous (N : ℕ) : Continuous (complexDensity N) := by
  have hg : Continuous (fun z : SourceCoordinateSlice => (z.2.2 : Gauge)) := by fun_prop
  have hv : Continuous (fun z : SourceCoordinateSlice => z.1 0 * z.1 2 * z.1 5) := by fun_prop
  exact Complex.continuous_ofReal.comp
    ((GaussHistoryHilbert.jacobian_continuous.comp hg).mul (hv.pow _))

def densityPair (f g : QuantumTest) (z : SourceCoordinateSlice) : ℂ :=
  inner ℂ (weight (fun N => complexDensity N z) (f z)) (g z)

theorem densityPair_sum (f g : QuantumTest) (z : SourceCoordinateSlice) :
    densityPair f g z = ∑ word : Occupation,
      complexDensity word.card z * star (f z word) * g z word := by
  rw [densityPair, PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro word _
  rw [RCLike.inner_apply, weight_apply]
  change g z word * star (complexDensity word.card z * f z word) = _
  rw [star_mul]
  have hs : star (complexDensity word.card z) = complexDensity word.card z := by simp [complexDensity]
  rw [hs]
  ring

private theorem component_pair_integrable (f g : QuantumTest) (word : Occupation) :
    Integrable (fun z => complexDensity word.card z * star (f z word) * g z word)
      GaussHistoryHilbert.configurationMeasure := by
  have hc := ((complexDensity_continuous word.card).mul (component word f).continuous.star).mul
    (component word g).continuous
  exact hc.integrable_of_hasCompactSupport (component word g).hasCompactSupport.mul_left

theorem densityPair_integrable (f g : QuantumTest) :
    Integrable (densityPair f g) GaussHistoryHilbert.configurationMeasure := by
  have hi := integrable_finsetSum Finset.univ (fun word _ => component_pair_integrable f g word)
  apply hi.congr
  exact Filter.Eventually.of_forall (fun z => (densityPair_sum f g z).symm)

def sourcePair (f g : QuantumTest) : ℂ := inner ℂ (embed f) (embed g)

theorem sourcePair_integral (f g : QuantumTest) :
    sourcePair f g = ∫ z, densityPair f g z ∂GaussHistoryHilbert.configurationMeasure := by
  calc
    _ = ∑ word : Occupation, pair word.card (component word f) (component word g) := by
      rw [sourcePair, PiLp.inner_apply]
      apply Finset.sum_congr rfl
      intro word _
      exact hilbert_pair word.card (component word f) (component word g)
    _ = ∫ z, ∑ word : Occupation, complexDensity word.card z * star (f z word) * g z word
        ∂GaussHistoryHilbert.configurationMeasure :=
      (integral_finsetSum Finset.univ (fun word _ => component_pair_integrable f g word)).symm
    _ = _ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun z => (densityPair_sum f g z).symm)

def connectionAction (v : GaussLiveMomentum.Ambient) : QuantumTest →ₗ[ℂ] QuantumTest :=
  localMultiplier (connection v) (connection_smooth v)

theorem connection_pair_skew (v : GaussLiveMomentum.Ambient) (f g : QuantumTest) :
    sourcePair (connectionAction v f) g + sourcePair f (connectionAction v g) = 0 := by
  rw [sourcePair_integral, sourcePair_integral,
    ← integral_add (densityPair_integrable (connectionAction v f) g)
      (densityPair_integrable f (connectionAction v g))]
  apply integral_eq_zero_of_ae
  exact Filter.Eventually.of_forall (fun z =>
    native_weighted_skew (fun N => complexDensity N z) (GaussLiveMomentum.inverseL z v).1 (f z) (g z))

#print axioms sourcePair_integral
#print axioms connection_pair_skew
end LowEnergy.GaussFockPair
