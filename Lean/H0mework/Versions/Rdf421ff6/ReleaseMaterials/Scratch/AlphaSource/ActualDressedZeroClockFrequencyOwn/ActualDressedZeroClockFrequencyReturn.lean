import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedZeroClockFrequencyCarrier

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
noncomputable section
namespace LowEnergy.GaussComposite.ActualDressedZeroClockFrequency
open Polynomial CanonicalGradedSpatialSource PreparationVacuumMixedFieldReturn
open PreparationVacuumPhysicalFeedback ActualDressedFullCoulomb ActualDressedCorrectedGreen
open ActualDressedCorrectedElectronRead ActualDressedUniformMaterialCoefficients
open LowEnergy.GaussComposite.ActualDressedVisiblePole LowEnergy.ActualDressedVisiblePole
open ActualDressedEMTensorClock ActualDressedZeroDamping ActualDressedOrderedStatic
open ActualCompositeFieldCurrent Filter Set
open scoped Topology
open scoped Matrix
attribute [local irreducible] commonEMTensorNumerator commonDeterminant correctedEMTensor

private theorem specialized_nonzero (D : (ℂ[X])[X]) (m : ℕ) (eps : ℝ)
    (regular : (D.coeff m).eval (eps : ℂ)≠0) : clockSpecialize eps D≠0 := by
  intro zero
  have coefficient := congrArg (fun P : ℂ[X] => P.coeff m) zero
  simp only [clockSpecialize,Polynomial.coe_mapRingHom,coeff_map,coeff_zero] at coefficient
  exact regular coefficient

private theorem coefficient_after_factor (Q : (ℂ[X])[X]) (m : ℕ) (eps : ℝ) :
    (clockSpecialize eps Q).eval 0=((X^m*Q).coeff m).eval (eps : ℂ) := by
  have coefficient : (X^m*Q).coeff m=Q.coeff 0 := by
    simpa only [zero_add] using coeff_X_pow_mul Q m 0
  rw [coefficient,← coeff_zero_eq_eval_zero]
  simp only [clockSpecialize,Polynomial.coe_mapRingHom,coeff_map]
  rfl

private theorem canceled_clock_read (N D : (ℂ[X])[X]) (m : ℕ) (eps : ℝ)
    (nFactor : X^m∣N) (dFactor : X^m∣D) (regular : (D.coeff m).eval (eps : ℂ)≠0) :
    let R := readFraction (clockSpecialize eps N) (clockSpecialize eps D)
    poleOrder R 0=0 ∧ leadingPoleCoefficient R 0=(N.coeff m).eval (eps : ℂ)/(D.coeff m).eval (eps : ℂ) := by
  dsimp only
  obtain ⟨Nq,nEq⟩ := nFactor
  obtain ⟨Dq,dEq⟩ := dFactor
  have nValue := coefficient_after_factor Nq m eps
  have dValue := coefficient_after_factor Dq m eps
  rw [← nEq] at nValue
  rw [← dEq] at dValue
  have qRegular : (clockSpecialize eps Dq).eval 0≠0 := by rw [dValue]; exact regular
  have ratio : readFraction (clockSpecialize eps N) (clockSpecialize eps D)=
      readFraction (clockSpecialize eps Nq) (clockSpecialize eps Dq) := by
    rw [nEq,dEq]
    simp only [map_mul,map_pow,clockSpecialize,Polynomial.coe_mapRingHom,Polynomial.map_X,readFraction]
    exact mul_div_mul_left _ _ (pow_ne_zero m (RatFunc.algebraMap_ne_zero (X_ne_zero : (X : ℂ[X])≠0)))
  let R := readFraction (clockSpecialize eps Nq) (clockSpecialize eps Dq)
  have rRegular : R.denom.eval 0≠0 := reduced_denominator_at_regular _ _ 0 qRegular
  have zeroOrder : poleOrder R 0=0 := rootMultiplicity_eq_zero rRegular
  rw [ratio]
  refine ⟨zeroOrder,?_⟩
  have leading : leadingPoleCoefficient R 0=R.num.eval 0/R.denom.eval 0 := by
    simp only [leadingPoleCoefficient,rootRemainder,rootPower,zeroOrder,pow_zero,divByMonic_one]
  change leadingPoleCoefficient R 0=_
  rw [leading]
  exact (reduced_read_at_regular _ _ 0 qRegular).trans (by rw [nValue,dValue])

private theorem positive_complex_punctured :
    Tendsto (fun sigma : ℝ => (sigma : ℂ)) (nhdsWithin 0 (Ioi 0)) (nhdsWithin 0 ({0}ᶜ)) := by
  apply tendsto_nhdsWithin_iff.mpr
  refine ⟨Complex.continuous_ofReal.continuousAt.tendsto.mono_left inf_le_left, ?_⟩
  filter_upwards [self_mem_nhdsWithin] with sigma positive
  simpa only [mem_compl_iff,mem_singleton_iff,Complex.ofReal_eq_zero] using (ne_of_gt positive)

private theorem positive_chart (D : ℂ[X]) (nonzero : D≠0) :
    ∀ᶠ sigma : ℝ in nhdsWithin 0 (Ioi 0), 0<sigma ∧ D.eval (sigma : ℂ)≠0 := by
  have inclusion : Ioi (0 : ℝ) ⊆ ({0}ᶜ) := by
    intro sigma positive
    simpa only [mem_compl_iff,mem_singleton_iff] using (ne_of_gt positive)
  filter_upwards [(source_static_punctured_chart D nonzero).filter_mono (nhdsWithin_mono 0 inclusion),
    self_mem_nhdsWithin] with sigma regular positive
  exact ⟨positive,regular⟩

private theorem raw_clock_ratio_limit (N D : (ℂ[X])[X]) (m : ℕ) (s : ℝ)
    (nFactor : X^m∣N) (dFactor : X^m∣D) (regular : (D.coeff m).eval (s : ℂ)≠0) :
    Tendsto (fun sigma : ℝ => (clockSpecialize s N).eval (sigma : ℂ)/
      (clockSpecialize s D).eval (sigma : ℂ)) (nhdsWithin 0 (Ioi 0))
      (𝓝 ((N.coeff m).eval (s : ℂ)/(D.coeff m).eval (s : ℂ))) := by
  let R := readFraction (clockSpecialize s N) (clockSpecialize s D)
  have paid := canceled_clock_read N D m s nFactor dFactor regular
  have base := (pole_order_limit R 0).comp positive_complex_punctured
  rw [paid.1,paid.2] at base
  simp only [Function.comp_def,sub_zero,pow_zero,one_mul] at base
  apply Tendsto.congr' _ base
  filter_upwards [positive_chart _ (specialized_nonzero D m s regular)] with sigma chart
  exact reduced_read_at_regular _ _ (sigma : ℂ) chart.2

/-- The first original clock coefficient generates a frequency chart and its positive-damping original pencil chart. -/
theorem source_zero_clock_frequency_chart (event : DressedEvent) (eps : ℝ) (n : PhysicalMomentum)
    (s : ℝ) (regular : (zeroClockFrequencyDenominator event eps n).eval (s : ℂ)≠0) :
    ∀ᶠ sigma : ℝ in nhdsWithin 0 (Ioi 0), 0<sigma ∧ correctedDet event eps s sigma n≠0 := by
  have nonzero := specialized_nonzero (frequencyClockDeterminant event eps n)
    (frequencyClockOrder event eps n) s regular
  filter_upwards [positive_chart _ nonzero] with sigma chart
  have commonRegular : MvPolynomial.eval (irValues eps sigma s) (commonDeterminant event n)≠0 := by
    rw [← frequency_damping_eval eps s sigma, ← frequency_clock_specialize eps s]
    exact chart.2
  exact ⟨chart.1,actual_common_chart_original event eps sigma s n chart.1 commonRegular⟩

def zeroClockFrequencyEMRead (event : DressedEvent) (eps s : ℝ) (n : PhysicalMomentum) :
    Matrix (Fin 4) (Fin 4) ℂ :=
  fun mu nu => (zeroClockFrequencyEMFraction event eps n mu nu).num.eval (s : ℂ)/
    (zeroClockFrequencyEMFraction event eps n mu nu).denom.eval (s : ℂ)

def zeroClockFrequencyProbeRead (event : DressedEvent) (eps s : ℝ) (n pd ps : PhysicalMomentum)
    (dL dR sL sR : CompositeLeg) : ℂ :=
  (zeroClockFrequencyProbeFraction event eps n pd ps dL dR sL sR).num.eval (s : ℂ)/
    (zeroClockFrequencyProbeFraction event eps n pd ps dL dR sL sR).denom.eval (s : ℂ)

theorem actual_zero_clock_frequency_em_entry (event : DressedEvent) (eps s : ℝ)
    (n : PhysicalMomentum) (mu nu : Fin 4)
    (regular : (zeroClockFrequencyDenominator event eps n).eval (s : ℂ)≠0)
    (factor : X^frequencyClockOrder event eps n∣frequencyClockEMNumerator event eps n mu nu) :
    Tendsto (fun sigma : ℝ => correctedEMTensor event eps s sigma n mu nu)
      (nhdsWithin 0 (Ioi 0)) (𝓝 (zeroClockFrequencyEMRead event eps s n mu nu)) := by
  have base := raw_clock_ratio_limit (frequencyClockEMNumerator event eps n mu nu)
    (frequencyClockDeterminant event eps n) (frequencyClockOrder event eps n) s
    factor (source_frequency_clock_factor event eps n) regular
  have value := reduced_read_at_regular (zeroClockFrequencyEMNumerator event eps n mu nu)
    (zeroClockFrequencyDenominator event eps n) (s : ℂ) regular
  dsimp only [zeroClockFrequencyEMNumerator,zeroClockFrequencyDenominator] at value
  rw [← value] at base
  apply Tendsto.congr' _ base
  filter_upwards [source_zero_clock_frequency_chart event eps n s regular] with sigma chart
  have commonRegular := actual_common_determinant_nonzero event eps sigma s n chart.1 chart.2
  have paid := congrFun (congrFun (actual_corrected_em_tensor_clear event eps sigma s n chart.1 chart.2) mu) nu
  have raw : correctedEMTensor event eps s sigma n mu nu=
      MvPolynomial.eval (irValues eps sigma s) (commonEMTensorNumerator event n mu nu)/
        MvPolynomial.eval (irValues eps sigma s) (commonDeterminant event n) := by
    apply (eq_div_iff commonRegular).mpr
    exact (mul_comm _ _).trans paid
  rw [frequencyClockEMNumerator,Matrix.map_apply,frequency_clock_specialize,
    frequencyClockDeterminant,frequency_clock_specialize,frequency_damping_eval,frequency_damping_eval]
  exact raw.symm

theorem actual_zero_clock_frequency_probe (event : DressedEvent) (eps s : ℝ)
    (n pd ps : PhysicalMomentum) (dL dR sL sR : CompositeLeg)
    (regular : (zeroClockFrequencyDenominator event eps n).eval (s : ℂ)≠0)
    (factor : X^frequencyClockOrder event eps n∣frequencyClockProbeNumerator event eps n pd ps dL dR sL sR) :
    Tendsto (fun sigma : ℝ => correctedProbeRead event eps s sigma n pd ps dL dR sL sR)
      (nhdsWithin 0 (Ioi 0)) (𝓝 (zeroClockFrequencyProbeRead event eps s n pd ps dL dR sL sR)) := by
  have base := raw_clock_ratio_limit (frequencyClockProbeNumerator event eps n pd ps dL dR sL sR)
    (frequencyClockDeterminant event eps n) (frequencyClockOrder event eps n) s
    factor (source_frequency_clock_factor event eps n) regular
  have value := reduced_read_at_regular (zeroClockFrequencyProbeNumerator event eps n pd ps dL dR sL sR)
    (zeroClockFrequencyDenominator event eps n) (s : ℂ) regular
  dsimp only [zeroClockFrequencyProbeNumerator,zeroClockFrequencyDenominator] at value
  rw [← value] at base
  apply Tendsto.congr' _ base
  filter_upwards [source_zero_clock_frequency_chart event eps n s regular] with sigma chart
  rw [frequencyClockProbeNumerator,frequency_clock_specialize,
    frequencyClockDeterminant,frequency_clock_specialize,frequency_damping_eval,frequency_damping_eval]
  exact (actual_common_current_read_fraction event eps sigma s n pd ps dL dR sL sR chart.1 chart.2).symm

theorem actual_zero_clock_frequency_tensor (event : DressedEvent) (eps s : ℝ)
    (n : PhysicalMomentum) (regular : (zeroClockFrequencyDenominator event eps n).eval (s : ℂ)≠0)
    (factors : ∀mu nu, X^frequencyClockOrder event eps n∣frequencyClockEMNumerator event eps n mu nu) :
    Tendsto (fun sigma : ℝ => correctedEMTensor event eps s sigma n)
      (nhdsWithin 0 (Ioi 0)) (𝓝 (zeroClockFrequencyEMRead event eps s n)) := by
  apply tendsto_pi_nhds.2
  intro mu
  apply tendsto_pi_nhds.2
  intro nu
  exact actual_zero_clock_frequency_em_entry event eps s n mu nu regular (factors mu nu)

end LowEnergy.GaussComposite.ActualDressedZeroClockFrequency

