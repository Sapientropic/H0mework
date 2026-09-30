import H0mework.Versions.Y.Arithmetic.RiemannUnitRegularity.RegularityPhysical
import H0mework.Versions.Y.Arithmetic.RiemannBandResponse.Class

/-! The same zero's original unit pair and every native comb resolvent response are integrable; no regularity field is supplied by the caller. -/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
open Complex Filter FourierTransform MeasureTheory Set
open scoped ENNReal InnerProductSpace SchwartzMap Topology
noncomputable section

theorem burnolZeroOwnedUnitOnePair_integrable {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (rightHalf : 1 / 2 < observation.coordinate.re) :
    let one := burnolZeroOwnedUnitOneState observation nontrivial rightHalf
    Integrable ((one + evenFaceFourierEquiv burnolUnscaledCommonGapRadius one :
      BurnolPaAmbientCarrier) : BurnolL2) volume := by
  dsimp only
  apply burnolPhysicalStrong_integrable
  exact burnolUnitFourierPair_hasDerivAt
    (burnolDivisionZeroCompletedMellinCoordinate observation rightHalf)

theorem burnolPaCombPhysicalResponse_integrable {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (rightHalf : 1 / 2 < observation.coordinate.re) (n : ℕ) :
    Integrable (burnolPaCombPhysicalResponse observation nontrivial rightHalf n : BurnolL2)
      volume := by
  apply burnolPhysicalStrong_integrable
  apply burnolDirectRightResolventOrbit_hasDerivAt
  rw [Complex.div_re]
  norm_num
  linarith

theorem burnolPaCombPhysicalResponse_fourier_integrable {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (rightHalf : 1 / 2 < observation.coordinate.re) (n : ℕ) :
    Integrable (fourierL2 (burnolPaCombPhysicalResponse observation nontrivial rightHalf n :
      BurnolL2)) volume := by
  apply burnolPhysicalStrong_integrable
    (evenFaceFourierEquiv burnolUnscaledCommonGapRadius
      (burnolPaCombPhysicalResponse observation nontrivial rightHalf n))
  apply burnolFourierOrbit_hasDerivAt
  apply burnolDirectRightResolventOrbit_hasDerivAt
  rw [Complex.div_re]
  norm_num
  linarith

theorem burnolPaCombPairedPhysicalResponse_integrable {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (rightHalf : 1 / 2 < observation.coordinate.re) (n : ℕ) :
    Integrable (burnolPaCombPairedPhysicalResponse observation nontrivial rightHalf n : BurnolL2)
      volume := by
  have same := (burnolPaCombPhysicalResponse_integrable observation nontrivial rightHalf n).add
    (burnolPaCombPhysicalResponse_fourier_integrable observation nontrivial rightHalf n)
  apply (same.const_mul (1 / 2 : ℂ)).congr
  filter_upwards [Lp.coeFn_smul (1 / 2 : ℂ)
    ((burnolPaCombPhysicalResponse observation nontrivial rightHalf n : BurnolL2) +
      fourierL2 (burnolPaCombPhysicalResponse observation nontrivial rightHalf n : BurnolL2)),
    Lp.coeFn_add (burnolPaCombPhysicalResponse observation nontrivial rightHalf n : BurnolL2)
      (fourierL2 (burnolPaCombPhysicalResponse observation nontrivial rightHalf n : BurnolL2))]
    with x scaleAt sumAt
  change _ = ((1 / 2 : ℂ) •
    ((burnolPaCombPhysicalResponse observation nontrivial rightHalf n : BurnolL2) +
      fourierL2 (burnolPaCombPhysicalResponse observation nontrivial rightHalf n : BurnolL2)) :
      BurnolL2) x
  rw [scaleAt]
  change (1 / 2 : ℂ) * _ = (1 / 2 : ℂ) * _
  rw [sumAt]

theorem burnolPaCombPairedPhysicalResponse_firstMoment {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (rightHalf : 1 / 2 < observation.coordinate.re) (n : ℕ) :
    MemLp (fun x : ℝ => (x : ℂ) *
      (burnolPaCombPairedPhysicalResponse observation nontrivial rightHalf n : BurnolL2) x) 2 volume := by
  let D := (burnolPaCombPhysicalResponse observation nontrivial rightHalf n : BurnolL2)
  let velocity := (observation.coordinate / 2 - 1 / 4) • D +
    (burnolPaCombApproximation n : BurnolL2)
  have native : HasDerivAt (fun h : ℝ => burnolMultiplicativeDilation (-h / 2) D)
      velocity 0 := by
    apply burnolDirectRightResolventOrbit_hasDerivAt
    rw [Complex.div_re]
    norm_num
    linarith
  have pair := (native.add (burnolFourierOrbit_hasDerivAt D velocity native)).const_smul (1 / 2 : ℂ)
  apply burnolPhysicalStrong_firstMoment
    (burnolPaCombPairedPhysicalResponse observation nontrivial rightHalf n)
    (velocity := (1 / 2 : ℂ) • (velocity + -fourierL2 velocity))
  convert! pair using 1
  funext h
  change burnolMultiplicativeDilation (-h / 2) ((1 / 2 : ℂ) • (D + fourierL2 D)) =
    (1 / 2 : ℂ) • (burnolMultiplicativeDilation (-h / 2) D +
      burnolMultiplicativeDilation (-h / 2) (fourierL2 D))
  rw [map_smul, map_add]

end
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
