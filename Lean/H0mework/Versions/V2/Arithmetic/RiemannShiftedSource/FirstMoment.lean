import H0mework.Versions.V2.Arithmetic.RiemannShiftedSource.PhysicalMean

/-! The original W strong action pays its first moment after each actual dilation. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalPaPhysicalGreen

open Complex MeasureTheory Set Filter
open scoped InnerProductSpace Topology
noncomputable section

private theorem dilation_firstMoment (value : BurnolL2)
    (moment : MemLp (fun x : ℝ => (x : ℂ) * value x) 2 volume) (h : ℝ) :
    MemLp (fun x : ℝ => (x : ℂ) * burnolMultiplicativeDilation h value x) 2 volume := by
  let m := moment.toLp (fun x : ℝ => (x : ℂ) * value x)
  have qmp := Measure.quasiMeasurePreserving_smul (μ := (volume : Measure ℝ))
    (r := Real.exp h) (Real.exp_ne_zero h)
  have representation : (fun x : ℝ => (Real.exp (-h) : ℂ) *
      burnolMultiplicativeDilation h m x) =ᵐ[volume]
      fun x : ℝ => (x : ℂ) * burnolMultiplicativeDilation h value x := by
    filter_upwards [burnolMultiplicativeDilation_coeFn h value,
      burnolMultiplicativeDilation_coeFn h m, qmp.ae moment.coeFn_toLp]
        with x valueAt momentAt rawAt
    change m (Real.exp h * x) = ((Real.exp h * x : ℝ) : ℂ) *
      value (Real.exp h * x) at rawAt
    rw [valueAt, momentAt]
    unfold burnolL2RawNormalizedDilation
    rw [rawAt]
    have cancel : (Real.exp (-h) : ℂ) * (Real.exp h : ℂ) = 1 := by
      rw [← Complex.ofReal_mul, ← Real.exp_add, neg_add_cancel,
        Real.exp_zero, Complex.ofReal_one]
    simp only [Complex.ofReal_mul]
    calc
      _ = ((Real.exp (-h) : ℂ) * (Real.exp h : ℂ)) *
        ((x : ℂ) * ((Real.exp (h / 2) : ℂ) * value (Real.exp h * x))) := by ring
      _ = _ := by rw [cancel, one_mul]
  exact MemLp.ae_eq representation ((Lp.memLp (burnolMultiplicativeDilation h m)).const_mul _)

theorem original_shifted_wave_firstMoment {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial : ¬ ∃ k : Nat, observation.coordinate = -2 * (k + 1))
    (rightHalf : 1 / 2 < observation.coordinate.re) (h : ℝ) :
    let one := burnolZeroOwnedUnitOneState observation nontrivial rightHalf
    let W : BurnolL2 := (one +
      evenFaceFourierEquiv burnolUnscaledCommonGapRadius one : BurnolPaAmbientCarrier)
    MemLp (fun x : ℝ => (x : ℂ) * burnolMultiplicativeDilation h W x) 2 volume := by
  intro one W
  apply dilation_firstMoment
  apply burnolPhysicalStrong_firstMoment
    (one + evenFaceFourierEquiv burnolUnscaledCommonGapRadius one)
  exact burnolUnitFourierPair_hasDerivAt
    (burnolDivisionZeroCompletedMellinCoordinate observation rightHalf)

end
end OriginalPaPhysicalGreen
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
