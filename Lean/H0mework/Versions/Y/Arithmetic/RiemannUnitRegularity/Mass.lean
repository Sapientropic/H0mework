import H0mework.Versions.Y.Arithmetic.RiemannUnitRegularity.RegularitySource
import H0mework.Versions.Y.Arithmetic.RiemannBandKernel.PairedSource

/-! The generated L¹ sources read their full Fourier-gap masses as ordinary integrals. -/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
open Complex Filter FourierTransform MeasureTheory Set
open scoped ENNReal InnerProductSpace SchwartzMap Topology
noncomputable section

private def ordinaryFourier (value : BurnolL2) (x : ℝ) : ℂ :=
  VectorFourier.fourierIntegral 𝐞 volume (innerₗ ℝ) (value : ℝ → ℂ) x

private theorem ordinaryFourier_continuous (value : BurnolL2) (integrable : Integrable value) :
    Continuous (ordinaryFourier value) :=
  VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
    (by fun_prop) integrable

private theorem ordinaryFourier_pairing (value : BurnolL2) (integrable : Integrable value)
    (test : SchwartzMap ℝ ℂ) :
    (∫ x : ℝ, FourierTransform.fourier test x * value x) =
      ∫ x : ℝ, test x * ordinaryFourier value x := by
  have source := VectorFourier.integral_fourierIntegral_smul_eq_flip
    (e := 𝐞) (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))
    (L := innerₗ ℝ) Real.continuous_fourierChar (by fun_prop)
    integrable test.integrable
  rw [flip_innerₗ] at source
  simp only [SchwartzMap.fourier_coe, Real.fourier_eq] at ⊢
  unfold ordinaryFourier
  simpa only [VectorFourier.fourierIntegral, innerₗ_apply_apply, smul_eq_mul, mul_comm]
    using source.symm

private theorem ordinaryFourier_coeFn (value : BurnolL2) (integrable : Integrable value) :
    (fourierL2 value : ℝ → ℂ) =ᵐ[volume] ordinaryFourier value := by
  apply ae_eq_of_integral_contDiff_smul_eq
  · exact (Lp.memLp (fourierL2 value)).locallyIntegrable (by norm_num)
  · exact (ordinaryFourier_continuous value integrable).locallyIntegrable
  · intro testReal testSmooth testCompact
    have compactComplex : HasCompactSupport (Complex.ofRealCLM ∘ testReal) :=
      testCompact.comp_left rfl
    let test : SchwartzMap ℝ ℂ := compactComplex.toSchwartzMap
      (Complex.ofRealCLM.contDiff.comp testSmooth)
    have source := Lp.fourier_toTemperedDistribution_eq value
    have read := congrArg (fun T : TemperedDistribution ℝ ℂ => T test) source
    rw [TemperedDistribution.fourier_apply, Lp.toTemperedDistribution_apply,
      Lp.toTemperedDistribution_apply] at read
    have swap := ordinaryFourier_pairing value integrable test
    change (∫ x : ℝ, FourierTransform.fourier test x * value x) =
      ∫ x : ℝ, test x * fourierL2 value x at read
    calc
      _ = ∫ x : ℝ, test x * fourierL2 value x := rfl
      _ = ∫ x : ℝ, FourierTransform.fourier test x * value x := read.symm
      _ = _ := swap

private theorem integral_of_fourier_gap
    (value : BurnolL2) (integrable : Integrable value) (constant : ℂ)
    (source : (fourierL2 value : ℝ → ℂ) =ᵐ[volume.restrict
      (symmetricInterval burnolUnscaledCommonGapRadius)] fun _ => constant) :
    (∫ x : ℝ, value x) = constant := by
  have raw : (fourierL2 value : ℝ → ℂ) =ᵐ[volume.restrict
      (symmetricInterval burnolUnscaledCommonGapRadius)] ordinaryFourier value :=
    ae_restrict_of_ae (ordinaryFourier_coeFn value integrable)
  have ordinary := raw.symm.trans source
  have pointwise := volume.eqOn_Icc_of_ae_eq (by norm_num : (-1 / 4 : ℝ) ≠ 1 / 4)
    (by simpa only [symmetricInterval, burnolUnscaledCommonGapRadius, neg_div] using ordinary)
    (ordinaryFourier_continuous value integrable).continuousOn continuous_const.continuousOn
  have atZero := pointwise (show (0 : ℝ) ∈ Icc (-1 / 4) (1 / 4) by constructor <;> norm_num)
  simpa [ordinaryFourier, VectorFourier.fourierIntegral] using atZero

theorem burnolPhysical_integral_eq_fourierGap
    (value : BurnolPaAmbientCarrier) (integrable : Integrable (value : BurnolL2)) :
    (∫ x : ℝ, (value : BurnolL2) x) =
      burnolConstantGapCoefficient burnolUnscaledCommonGapRadius
        (evenFaceFourierEquiv burnolUnscaledCommonGapRadius value) := by
  apply integral_of_fourier_gap (value : BurnolL2) integrable
  exact burnolAmbientGap_ae (evenFaceFourierEquiv burnolUnscaledCommonGapRadius value)

private theorem fourier_even_pair (value : BurnolPaAmbientCarrier) :
    fourierL2 ((value : BurnolL2) + fourierL2 (value : BurnolL2)) =
      (value : BurnolL2) + fourierL2 (value : BurnolL2) := by
  rw [map_add, fourierL2_fourierL2, mem_evenL2ClosedFace_iff.mp value.2.2, add_comm]

theorem burnolZeroOwnedUnitOnePair_integral {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (rightHalf : 1 / 2 < observation.coordinate.re) :
    let one := burnolZeroOwnedUnitOneState observation nontrivial rightHalf
    (∫ x : ℝ, ((one + evenFaceFourierEquiv burnolUnscaledCommonGapRadius one :
      BurnolPaAmbientCarrier) : BurnolL2) x) =
        1 / observation.coordinate - 1 / (1 - observation.coordinate) := by
  dsimp only
  apply integral_of_fourier_gap _ (burnolZeroOwnedUnitOnePair_integrable observation nontrivial rightHalf)
  change (fourierL2 ((burnolZeroOwnedUnitOneState observation nontrivial rightHalf : BurnolL2) +
    fourierL2 (burnolZeroOwnedUnitOneState observation nontrivial rightHalf : BurnolL2)) : ℝ → ℂ)
      =ᵐ[volume.restrict (symmetricInterval burnolUnscaledCommonGapRadius)] _
  rw [fourier_even_pair (burnolZeroOwnedUnitOneState observation nontrivial rightHalf)]
  filter_upwards [ae_restrict_of_ae
    (burnolZeroOwnedUnitOnePair_dirichlet_coeFn observation nontrivial rightHalf),
    ae_restrict_mem (measurableSet_symmetricInterval burnolUnscaledCommonGapRadius)] with x read inside
  change (burnolUnitTailResponse (burnolDivisionZeroCompletedMellinCoordinate observation rightHalf) 1 +
    fourierL2 (burnolUnitTailResponse (burnolDivisionZeroCompletedMellinCoordinate observation rightHalf) 1) :
      BurnolL2) x = _ at read ⊢
  rw [read, burnolUnitPairDirichletRaw_forward]
  have small : |x| ≤ (1 / 4 : ℝ) := abs_le.mpr inside
  rw [burnolInnerGapForward_innerGap _ (fun small =>
    burnolUnitPairRawSource_innerMargin _ (by linarith)) small, zero_add]

theorem burnolPaCombPairedPhysicalResponse_integral {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (rightHalf : 1 / 2 < observation.coordinate.re) (n : ℕ) :
    (∫ x : ℝ, (burnolPaCombPairedPhysicalResponse observation nontrivial rightHalf n : BurnolL2) x) =
      burnolPaCombPairedRawMean observation.coordinate n := by
  apply integral_of_fourier_gap _ (burnolPaCombPairedPhysicalResponse_integrable observation nontrivial rightHalf n)
  have fixed : fourierL2 (burnolPaCombPairedPhysicalResponse observation nontrivial rightHalf n :
      BurnolL2) = (burnolPaCombPairedPhysicalResponse observation nontrivial rightHalf n : BurnolL2) := by
    change fourierL2 ((1 / 2 : ℂ) •
      ((burnolPaCombPhysicalResponse observation nontrivial rightHalf n : BurnolL2) +
        fourierL2 (burnolPaCombPhysicalResponse observation nontrivial rightHalf n : BurnolL2))) = _
    rw [map_smul, fourier_even_pair]
    rfl
  rw [fixed]
  filter_upwards [ae_restrict_of_ae
    (burnolPaCombPairedPhysicalResponse_coeFn observation nontrivial rightHalf n),
    ae_restrict_mem (measurableSet_symmetricInterval burnolUnscaledCommonGapRadius)] with x read inside
  rw [read, burnolPaCombPairedDirichletRaw_forward]
  have small : |x| ≤ (1 / 4 : ℝ) := abs_le.mpr inside
  rw [burnolInnerGapForward_innerGap _ (fun small =>
    burnolPaCombPairedRawSource_innerGap _ _ small) small, zero_add]

end
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
