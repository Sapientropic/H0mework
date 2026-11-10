import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedAngularFullReadPrice

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
noncomputable section
namespace LowEnergy.GaussComposite.ActualDressedAngularSectorFourier
open Polynomial CanonicalGradedSpatialSource PreparationVacuumMixedFieldReturn PreparationVacuumPhysicalFeedback
open PreparationVacuumPhysicalCharacteristic ActualDressedFullCoulomb ActualDressedOrderedStatic
open ActualDressedAngularSpherePrice ActualDressedCorrectedElectronRead ActualDressedEMTensorClock ActualCompositeFieldCurrent
open LowEnergy.ActualDressedVisiblePole Filter Set
open scoped Topology Matrix

def directionCoulombCoefficient (event : DressedEvent) (N : DirectionParameters[X]) (n : PhysicalMomentum) : ℂ :=
  -MvPolynomial.eval (directionValues n) ((directionScaledNumerator event N).coeff 0)/directionLeadingRead event n

def directionEMCoefficient (event : DressedEvent) (n : PhysicalMomentum) : Matrix (Fin 4) (Fin 4) ℂ :=
  fun mu nu => directionCoulombCoefficient event (directionZeroClockEM event mu nu) n

def directionProbeCoefficient (event : DressedEvent) (pd ps : PhysicalMomentum) (dL dR sL sR : CompositeLeg)
    (n : PhysicalMomentum) : ℂ := directionCoulombCoefficient event (directionZeroClockProbe event pd ps dL dR sL sR) n

private theorem quotient_factor {R : Type*} [CommRing R] (P : R[X]) (m : ℕ) (factor : X^m∣P) :
    X^m*(P /ₘ X^m)=P := by
  obtain ⟨Q,eq⟩ := factor
  rw [eq,mul_divByMonic_cancel_left Q (monic_X_pow m)]

private theorem reduced_constant (event : DressedEvent) :
    (directionReducedDenominator event).coeff 0=directionLeadingDenominator event := by
  have paid := congrArg (fun P : DirectionParameters[X] => P.coeff (directionSpatialOrder event))
    (quotient_factor (directionSpatialDenominator event) (directionSpatialOrder event)
      (X_pow_dvd_iff.mpr (fun _ less => coeff_eq_zero_of_lt_natTrailingDegree less)))
  have coefficient := coeff_X_pow_mul (directionReducedDenominator event) (directionSpatialOrder event) 0
  have normalized : (directionReducedDenominator event).coeff 0=
      (X^directionSpatialOrder event*directionReducedDenominator event).coeff (directionSpatialOrder event) := by
    simpa only [zero_add] using coefficient.symm
  exact normalized.trans paid

private theorem normalized_ratio (event : DressedEvent) (N : DirectionParameters[X]) (n : PhysicalMomentum)
    (eps : ℝ) (away : eps≠0) (factor : X^directionSpatialOrder event∣X^4*N) :
    -(eps : ℂ)^4*N.eval₂ (MvPolynomial.eval (directionValues n)) (eps : ℂ)/
      (directionSpatialDenominator event).eval₂ (MvPolynomial.eval (directionValues n)) (eps : ℂ)=
    -(directionScaledNumerator event N).eval₂ (MvPolynomial.eval (directionValues n)) (eps : ℂ)/
      (directionReducedDenominator event).eval₂ (MvPolynomial.eval (directionValues n)) (eps : ℂ) := by
  let f := MvPolynomial.eval (directionValues n)
  have nEq := congrArg (fun P : DirectionParameters[X] => P.eval₂ f (eps : ℂ)) (quotient_factor _ _ factor)
  have dEq := congrArg (fun P : DirectionParameters[X] => P.eval₂ f (eps : ℂ))
    (quotient_factor (directionSpatialDenominator event) (directionSpatialOrder event)
      (X_pow_dvd_iff.mpr (fun _ less => coeff_eq_zero_of_lt_natTrailingDegree less)))
  simp only [eval₂_mul,eval₂_pow,eval₂_X] at nEq dEq
  have positiveRatio : (eps : ℂ)^4*N.eval₂ f (eps : ℂ)/
      (directionSpatialDenominator event).eval₂ f (eps : ℂ)=
      (directionScaledNumerator event N).eval₂ f (eps : ℂ)/
      (directionReducedDenominator event).eval₂ f (eps : ℂ) := by
    rw [←dEq,←nEq]
    exact mul_div_mul_left _ _ (pow_ne_zero _ (Complex.ofReal_ne_zero.mpr away))
  simpa only [neg_mul,neg_div] using congrArg Neg.neg positiveRatio

private theorem quotient_limit (P Q : DirectionParameters[X]) (f : DirectionParameters→+*ℂ)
    (regular : f (Q.coeff 0)≠0) :
    Tendsto (fun eps : ℝ => -P.eval₂ f (eps : ℂ)/Q.eval₂ f (eps : ℂ))
      (𝓝 0) (𝓝 (-f (P.coeff 0)/f (Q.coeff 0))) := by
  have numerator := (((P.continuous_eval₂ f).comp Complex.continuous_ofReal).continuousAt (x:=0)).tendsto.neg
  have denominator := (((Q.continuous_eval₂ f).comp Complex.continuous_ofReal).continuousAt (x:=0)).tendsto
  have nLimit : Tendsto (fun eps : ℝ => -P.eval₂ f (eps : ℂ)) (𝓝 0) (𝓝 (-f (P.coeff 0))) := by
    simpa only [Function.comp_def,Complex.ofReal_zero,eval₂_at_zero] using numerator
  have dLimit : Tendsto (fun eps : ℝ => Q.eval₂ f (eps : ℂ)) (𝓝 0) (𝓝 (f (Q.coeff 0))) := by
    simpa only [Function.comp_def,Complex.ofReal_zero,eval₂_at_zero] using denominator
  exact nLimit.div dLimit regular

private theorem direction_ratio_limit (event : DressedEvent) (N : DirectionParameters[X]) (n : PhysicalMomentum)
    (regular : directionLeadingRead event n≠0) (factor : X^directionSpatialOrder event∣X^4*N) :
    Tendsto (fun eps : ℝ => -(eps : ℂ)^4*N.eval₂ (MvPolynomial.eval (directionValues n)) (eps : ℂ)/
      (directionSpatialDenominator event).eval₂ (MvPolynomial.eval (directionValues n)) (eps : ℂ))
      (nhdsWithin 0 ({0}ᶜ)) (𝓝 (directionCoulombCoefficient event N n)) := by
  let f := MvPolynomial.eval (directionValues n)
  have qRegular : f ((directionReducedDenominator event).coeff 0)≠0 := by
    rw [reduced_constant]
    exact regular
  have qLimit := quotient_limit (directionScaledNumerator event N) (directionReducedDenominator event) f qRegular
  have point : -f ((directionScaledNumerator event N).coeff 0)/f ((directionReducedDenominator event).coeff 0)=
      directionCoulombCoefficient event N n := by
    rw [reduced_constant]
    rfl
  rw [point] at qLimit
  apply Tendsto.congr' _ (qLimit.mono_left nhdsWithin_le_nhds)
  filter_upwards [self_mem_nhdsWithin] with eps away
  exact (normalized_ratio event N n eps (by simpa only [mem_compl_iff,mem_singleton_iff] using away) factor).symm

theorem actual_direction_coulomb_coefficient (event : DressedEvent) (pd ps : PhysicalMomentum)
    (dL dR sL sR : CompositeLeg) (n : PhysicalMomentum) (regular : directionLeadingRead event n≠0)
    (spatial : DirectionSpatialFinite event pd ps dL dR sL sR) :
    Tendsto (fun eps : ℝ => -(eps : ℂ)^4 • zeroClockEMRead event eps n)
      (nhdsWithin 0 ({0}ᶜ)) (𝓝 (directionEMCoefficient event n)) ∧
    Tendsto (fun eps : ℝ => -(eps : ℂ)^4*zeroClockProbeRead event eps n pd ps dL dR sL sR)
      (nhdsWithin 0 ({0}ᶜ)) (𝓝 (directionProbeCoefficient event pd ps dL dR sL sR n)) := by
  have chart := (actual_direction_original_chart event n regular).mono (fun _ h => h.1)
  constructor
  · apply tendsto_pi_nhds.2
    intro mu
    apply tendsto_pi_nhds.2
    intro nu
    apply Tendsto.congr' _ (direction_ratio_limit event (directionZeroClockEM event mu nu) n regular (spatial.1 mu nu))
    filter_upwards [chart] with eps dRegular
    simp only [Matrix.smul_apply,smul_eq_mul]
    rw [zeroClockEMRead,zeroClockEMFraction,reduced_read_at_regular _ _ _ dRegular,
      actual_direction_zero_clock_em event n regular mu nu,actual_direction_spatial_denominator event n regular,
      eval_map,eval_map,←mul_div_assoc]
  · apply Tendsto.congr' _ (direction_ratio_limit event (directionZeroClockProbe event pd ps dL dR sL sR) n regular spatial.2)
    filter_upwards [chart] with eps dRegular
    rw [zeroClockProbeRead,zeroClockProbeFraction,reduced_read_at_regular _ _ _ dRegular,
      actual_direction_zero_clock_probe event n pd ps dL dR sL sR regular,actual_direction_spatial_denominator event n regular,
      eval_map,eval_map,←mul_div_assoc]

end LowEnergy.GaussComposite.ActualDressedAngularSectorFourier
