import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceNamedMatterColorEpsilon

set_option autoImplicit false
noncomputable section
namespace LowEnergy.NamedMatterWedgeQt
open SourceQuantumConfigurationHilbert SourceQuantumFockGauge
open GaussCoreDifferential GaussCoreHilbert GaussDensityCore GaussFockPair
open SourceQuantumGaugeSliceCoordinates
open scoped BigOperators InnerProductSpace ContDiff

abbrev WedgeFiber := EuclideanSpace ℂ WedgeIndex

def wedgeFiber (dual : Bool) (a : WedgeFiber) : FockFiber :=
  ∑ w : WedgeIndex, a w • fiberBasis dual w

theorem actual_wedge_fiber_pair (dual : Bool) (a b : WedgeFiber) :
    inner ℂ (wedgeFiber dual a) (wedgeFiber dual b) = inner ℂ a b := by
  classical
  simp only [wedgeFiber, sum_inner, inner_sum, inner_smul_left, inner_smul_right,
    actual_fiber_pair, starRingEnd_apply]
  simp [mul_ite, PiLp.inner_apply, RCLike.inner_apply, mul_comm]

def wedgeTest (dual : Bool) (a : WedgeFiber) (f : ScalarTest) : QuantumTest :=
  ∑ w : WedgeIndex, a w • profileTest dual w f

theorem actual_wedge_test_value (dual : Bool) (a : WedgeFiber) (f : ScalarTest)
    (z : SourceCoordinateSlice) : wedgeTest dual a f z = f z • wedgeFiber dual a := by
  simp only [wedgeTest, _root_.sum_apply, _root_.smul_apply,
    actual_source_profile, wedgeFiber, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro w _
  rw [smul_comm]

theorem actual_wedge_source_pair (dual : Bool) (a b : WedgeFiber) (f g : ScalarTest) :
    sourcePair (wedgeTest dual a f) (wedgeTest dual b g) =
      inner ℂ a b * GaussDensityCore.pair 3 f g := by
  classical
  simp only [sourcePair, wedgeTest, map_sum, map_smul, sum_inner, inner_sum,
    inner_smul_left, inner_smul_right, starRingEnd_apply]
  change (∑ v, b v * ∑ w, star (a w) *
    sourcePair (profileTest dual w f) (profileTest dual v g)) = _
  simp_rw [actual_profile_source_pair]
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [PiLp.inner_apply]
  simp only [RCLike.inner_apply, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro w _
  rw [starRingEnd_apply]
  ring

theorem actual_wedge_source_norm (dual : Bool) (a : WedgeFiber) (f : ScalarTest) :
    ‖embed (wedgeTest dual a f)‖ = ‖a‖ * ‖scalarLp 3 f‖ := by
  have h := actual_wedge_source_pair dual a a f f
  rw [← GaussDensityCore.hilbert_pair] at h
  simp only [sourcePair, inner_self_eq_norm_sq_to_K] at h
  have hs : ‖embed (wedgeTest dual a f)‖ ^ 2 = (‖a‖ * ‖scalarLp 3 f‖) ^ 2 := by
    rw [mul_pow]
    exact_mod_cast h
  nlinarith [norm_nonneg (embed (wedgeTest dual a f)),
    mul_nonneg (norm_nonneg a) (norm_nonneg (scalarLp 3 f))]

end LowEnergy.NamedMatterWedgeQt
