import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceNamedMatterCAR
import H0mework.Versions.AB.Physics.LowEnergy.Quantum.GaussFockPair

set_option autoImplicit false
noncomputable section
namespace LowEnergy.NamedMatterWedgeQt
open SourceQuantumConfigurationHilbert SourceQuantumFockGauge SourceQuantumGaugeSliceCoordinates
open GaussCoreDifferential GaussCoreHilbert GaussFockPair GaussDensityCore GaussFockWeights
open MeasureTheory Set
open scoped BigOperators InnerProductSpace ContDiff

theorem actual_profile_component (dual : Bool) (w : WedgeIndex) (f : ScalarTest)
    (z : SourceCoordinateSlice) (v : Occupation) :
    profileTest dual w f z v = if v = occupation dual w.val then f z else 0 := by
  classical
  simp [profileTest, fiberBasis, EuclideanSpace.single]

theorem actual_profile_density (dual : Bool) (w v : WedgeIndex) (f g : ScalarTest)
    (z : SourceCoordinateSlice) :
    densityPair (profileTest dual w f) (profileTest dual v g) z =
      if w = v then complexDensity 3 z * star (f z) * g z else 0 := by
  classical
  rw [densityPair_sum]
  simp only [actual_profile_component]
  by_cases h : w = v
  · subst v
    simp [mul_ite, occupation_card, w.property]
  · have ho : occupation dual w.val ≠ occupation dual v.val := by
      intro he
      exact h (Subtype.ext (occupation_injective dual he))
    simp [mul_ite, Ne.symm ho, h]

theorem actual_profile_source_pair (dual : Bool) (w v : WedgeIndex) (f g : ScalarTest) :
    sourcePair (profileTest dual w f) (profileTest dual v g) =
      if w = v then GaussDensityCore.pair 3 f g else 0 := by
  classical
  rw [sourcePair_integral]
  simp_rw [actual_profile_density]
  by_cases h : w = v
  · simp only [if_pos h]
    rfl
  · simp [h]

theorem actual_profile_norm (dual : Bool) (w : WedgeIndex) (f : ScalarTest) :
    ‖embed (profileTest dual w f)‖ = ‖scalarLp 3 f‖ := by
  have h := actual_profile_source_pair dual w w f f
  rw [if_pos rfl, ← GaussDensityCore.hilbert_pair] at h
  change inner ℂ (embed (profileTest dual w f)) (embed (profileTest dual w f)) =
    inner ℂ (scalarLp 3 f) (scalarLp 3 f) at h
  simp only [inner_self_eq_norm_sq_to_K] at h
  have hs : ‖embed (profileTest dual w f)‖ ^ 2 = ‖scalarLp 3 f‖ ^ 2 := by
    exact_mod_cast h
  nlinarith [norm_nonneg (embed (profileTest dual w f)), norm_nonneg (scalarLp 3 f)]

end LowEnergy.NamedMatterWedgeQt
