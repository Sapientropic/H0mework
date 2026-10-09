import H0mework.Versions.V2.Arithmetic.RiemannResolvent.CompleteTate
import H0mework.Versions.V2.Arithmetic.RemainderSource.BochnerPairing

/-! The existing Hilbert/Fubini kernel reads the literal raw source, without a gap-zero premise. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
open Complex MeasureTheory Set
open scoped ArithmeticFunction
noncomputable section

private def rawDivisionPairingKernel (radius : ℝ) (z : ℂ) (raw : ℝ → ℂ)
    (test : Lp ℂ 2 (volume.restrict (symmetricInterval radius))) (point : ℝ × ℝ) : ℂ :=
  inner ℂ ((Lp.aestronglyMeasurable test).mk test point.2)
    (Complex.exp (((1 / 2 : ℂ) - z) * (point.1 : ℂ)) * raw (Real.exp (point.1 / 2) * point.2))

private theorem rawDivisionPairingKernel_strong (radius : ℝ) (z : ℂ) (raw : ℝ → ℂ)
    (rawStrong : StronglyMeasurable raw)
    (test : Lp ℂ 2 (volume.restrict (symmetricInterval radius))) :
    StronglyMeasurable (rawDivisionPairingKernel radius z raw test) := by
  have testStrong : StronglyMeasurable (fun point : ℝ × ℝ =>
      (Lp.aestronglyMeasurable test).mk test point.2) :=
    (Lp.aestronglyMeasurable test).stronglyMeasurable_mk.comp_measurable measurable_snd
  have sourceStrong : StronglyMeasurable (fun point : ℝ × ℝ =>
      raw (Real.exp (point.1 / 2) * point.2)) :=
    rawStrong.comp_measurable (by fun_prop)
  have weightStrong : StronglyMeasurable (fun point : ℝ × ℝ =>
      Complex.exp (((1 / 2 : ℂ) - z) * (point.1 : ℂ))) := by fun_prop
  exact testStrong.inner (weightStrong.mul sourceStrong)

private theorem rawDivisionPairingKernel_same (radius : ℝ) (z : ℂ) (value : BurnolL2)
    (even : reflectL2 value = value) (raw : ℝ → ℂ) (rawStrong : StronglyMeasurable raw)
    (rawRead : raw =ᵐ[volume] value)
    (test : Lp ℂ 2 (volume.restrict (symmetricInterval radius))) :
    rawDivisionPairingKernel radius z raw test =ᵐ[
      (volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (symmetricInterval radius))]
        burnolFourierDivisionPairingKernel radius z value test := by
  refine (Measure.ae_prod_iff_ae_ae (measurableSet_eq_fun
      (rawDivisionPairingKernel_strong radius z raw rawStrong test).measurable
      (burnolFourierDivisionPairingKernel_stronglyMeasurable radius z value test).measurable)).mpr ?_
  filter_upwards with h
  have qmp : Measure.QuasiMeasurePreserving (fun x : ℝ => Real.exp (h / 2) * x)
      volume volume := by
    simpa only [smul_eq_mul] using
      (Measure.quasiMeasurePreserving_smul (μ := (volume : Measure ℝ))
        (r := Real.exp (h / 2)) (Real.exp_ne_zero _))
  have same := rawRead.trans (burnolEvenStrongRepresentative_ae_eq value even).symm
  filter_upwards [ae_restrict_of_ae (qmp.ae same)] with x hsource
  unfold rawDivisionPairingKernel burnolFourierDivisionPairingKernel
  rw [hsource]

/-- Reuse the original Hilbert/Fubini kernel with the actual source raw;
there is no gap-constant or completed-value-zero input. -/
theorem burnolExpandingRightResolvent_pairing_raw (radius : ℝ)
    (coordinate : BurnolCompletedMellinCoordinate) (value : BurnolL2)
    (even : reflectL2 value = value) (raw : ℝ → ℂ) (rawStrong : StronglyMeasurable raw)
    (rawRead : raw =ᵐ[volume] value)
    (test : Lp ℂ 2 (volume.restrict (symmetricInterval radius))) :
    inner ℂ test (restrictToInterval radius
      (-∫ h : ℝ in Ioi 0, positiveMellinQuarterRightResolventWeight (coordinate.value / 2) h •
        burnolMultiplicativeDilation (h / 2) value)) =
      ∫ x : ℝ in symmetricInterval radius, inner ℂ (test x)
        (burnolFourierRightDivisionRaw (coordinate.value / 2) raw x) := by
  let z := coordinate.value / 2
  let orbit : ℝ → BurnolL2 := fun h => positiveMellinQuarterRightResolventWeight z h •
    burnolMultiplicativeDilation (h / 2) value
  have rightQuarter : 1 / 4 < z.re := by
    dsimp only [z]
    rw [Complex.div_re]
    norm_num
    linarith [coordinate.rightHalf]
  have orbitIntegrable : IntegrableOn orbit (Ioi 0) := by
    have ordinary := burnolDirectRightResolventIntegrand_integrableOn z rightQuarter
      (burnolTateReciprocalL2 value)
    have mapped := burnolTateReciprocalL2.integrable_comp ordinary
    apply mapped.congr
    filter_upwards with h
    unfold burnolDirectRightResolventIntegrand
    rw [map_smul]
    have action := burnolTateReciprocalL2_dilation_inverse (h / 2) (burnolTateReciprocalL2 value)
    rw [burnolTateReciprocalL2_involutive] at action
    simpa only [neg_div, orbit] using congrArg
      (fun current : BurnolL2 => positiveMellinQuarterRightResolventWeight z h • current) action.symm
  have restricted := (restrictToInterval radius).integrable_comp orbitIntegrable
  have sameKernel := rawDivisionPairingKernel_same radius z value even raw rawStrong rawRead test
  have joint := (burnolFourierDivisionPairingKernel_integrable radius coordinate value even test).congr
    sameKernel.symm
  rw [map_neg, ← (restrictToInterval radius).integral_comp_comm orbitIntegrable,
    inner_neg_right, ← integral_inner restricted test]
  have sections : (fun h : ℝ => inner ℂ test (restrictToInterval radius (orbit h))) =ᵐ[
      volume.restrict (Ioi 0)] fun h => ∫ x : ℝ in symmetricInterval radius,
        rawDivisionPairingKernel radius z raw test (h, x) := by
    have kernelSections := Measure.ae_ae_of_ae_prod sameKernel
    filter_upwards [kernelSections] with h hkernel
    rw [L2.inner_def]
    apply integral_congr_ae
    have kernelRead : (fun x => rawDivisionPairingKernel radius z raw test (h, x)) =ᵐ[
        volume.restrict (symmetricInterval radius)]
      (fun x => burnolFourierDivisionPairingKernel radius z value test (h, x)) := hkernel
    exact (burnolFourierDivisionPairingKernel_section_ae radius z value even test h).symm.trans
      kernelRead.symm
  rw [integral_congr_ae sections, ← integral_prod _ joint, integral_prod_symm _ joint, ← integral_neg]
  apply integral_congr_ae
  filter_upwards [(Lp.aestronglyMeasurable test).ae_eq_mk] with x htest
  unfold rawDivisionPairingKernel burnolFourierRightDivisionRaw
  simp only [RCLike.inner_apply]
  rw [integral_mul_const, ← htest, neg_mul]

theorem burnolCompleteFirstSourceTate_pairing (coordinate : BurnolCompletedMellinCoordinate)
    (source : burnolCompactAnnulusSource) (test : BurnolL2) :
    inner ℂ test (burnolTateReciprocalL2 (burnolCompleteRemainderSource (coordinate.value / 2) source 1)) =
      ∫ x : ℝ, inner ℂ (test x)
        (burnolFourierRightDivisionRaw (coordinate.value / 2) (fun t => (2 : ℂ) * source.1 t) x) := by
  let z := coordinate.value / 2
  let value : BurnolL2 := (2 : ℂ) • source.1.toLp 2 volume
  let family : ℝ → BurnolL2 := fun h => positiveMellinQuarterRightResolventWeight z h •
    burnolMultiplicativeDilation (h / 2) value
  let raw : ℝ × ℝ → ℂ := fun point => Complex.exp (((1 / 2 : ℂ) - z) * (point.1 : ℂ)) *
    ((2 : ℂ) * source.1 (Real.exp (point.1 / 2) * point.2))
  have rightQuarter : 1 / 4 < z.re := by
    dsimp only [z]
    rw [Complex.div_re]
    norm_num
    linarith [coordinate.rightHalf]
  have integrable : IntegrableOn family (Ioi (0 : ℝ)) := by
    have ordinary := burnolDirectRightResolventIntegrand_integrableOn z rightQuarter (burnolTateReciprocalL2 value)
    apply (burnolTateReciprocalL2.integrable_comp ordinary).congr
    filter_upwards with h
    unfold burnolDirectRightResolventIntegrand
    rw [map_smul]
    have action := burnolTateReciprocalL2_dilation_inverse (h / 2) (burnolTateReciprocalL2 value)
    rw [burnolTateReciprocalL2_involutive] at action
    simpa only [neg_div, family] using congrArg
      (fun current : BurnolL2 => positiveMellinQuarterRightResolventWeight z h • current) action.symm
  have sourceRead : (value : ℝ → ℂ) =ᵐ[volume] fun x => (2 : ℂ) * source.1 x := by
    filter_upwards [Lp.coeFn_smul (2 : ℂ) (source.1.toLp 2 volume), source.1.coeFn_toLp 2 volume]
      with x hsmul hsource
    change ((2 : ℂ) • source.1.toLp 2 volume : BurnolL2) x = _
    rw [hsmul]
    change (2 : ℂ) * source.1.toLp 2 volume x = _
    rw [hsource]
  have measured : Measurable raw := by
    have smooth : Continuous raw := by unfold raw; fun_prop
    exact smooth.measurable
  have reads : ∀ᵐ h ∂volume.restrict (Ioi (0 : ℝ)), (family h : ℝ → ℂ) =ᵐ[volume] fun x => raw (h, x) := by
    filter_upwards with h
    have qmp : Measure.QuasiMeasurePreserving (fun x : ℝ => Real.exp (h / 2) * x) volume volume := by
      simpa only [smul_eq_mul] using (Measure.quasiMeasurePreserving_smul (μ := (volume : Measure ℝ))
        (r := Real.exp (h / 2)) (Real.exp_ne_zero _))
    filter_upwards [Lp.coeFn_smul (positiveMellinQuarterRightResolventWeight z h)
      (burnolMultiplicativeDilation (h / 2) value), burnolMultiplicativeDilation_coeFn (h / 2) value,
      qmp.ae sourceRead] with x hsmul hdilate hraw
    change (positiveMellinQuarterRightResolventWeight z h • burnolMultiplicativeDilation (h / 2) value : BurnolL2) x = _
    rw [hsmul]
    change positiveMellinQuarterRightResolventWeight z h * burnolMultiplicativeDilation (h / 2) value x = _
    rw [hdilate, burnolFourierRightDivision_integrand_eq, hraw]
  have actual := burnolL2Bochner_pairing_raw (volume.restrict (Ioi (0 : ℝ))) family integrable raw measured reads test
  rw [burnolCompleteRemainderSource_tateFirst _ rightQuarter, inner_neg_right, actual.2, ← integral_neg]
  apply integral_congr_ae
  filter_upwards with x
  simp only [burnolFourierRightDivisionRaw, inner_neg_right]
  rfl

end
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
