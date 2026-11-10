import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedAngularSectorSymbol

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
noncomputable section
namespace LowEnergy.GaussComposite.ActualDressedAngularSectorFourier
open Polynomial CanonicalGradedSpatialSource PreparationVacuumMixedFieldReturn PreparationVacuumPhysicalFeedback
open PreparationVacuumPhysicalCharacteristic ActualDressedFullCoulomb ActualDressedOrderedStatic
open ActualDressedAngularSpherePrice ActualDressedCorrectedElectronRead ActualDressedEMTensorClock ActualCompositeFieldCurrent
open LowEnergy.ActualDressedVisiblePole Filter Set
open scoped Topology Matrix

private theorem quotient_factor {R : Type*} [CommRing R] (P : R[X]) (m : ℕ) (factor : X^m∣P) :
    X^m*(P /ₘ X^m)=P := by
  obtain ⟨Q,eq⟩ := factor
  rw [eq,mul_divByMonic_cancel_left Q (monic_X_pow m)]

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
  have paid : (eps : ℂ)^4*N.eval₂ f (eps : ℂ)/(directionSpatialDenominator event).eval₂ f (eps : ℂ)=
      (directionScaledNumerator event N).eval₂ f (eps : ℂ)/(directionReducedDenominator event).eval₂ f (eps : ℂ) := by
    rw [←dEq,←nEq]
    exact mul_div_mul_left _ _ (pow_ne_zero _ (Complex.ofReal_ne_zero.mpr away))
  simpa only [neg_mul,neg_div] using congrArg Neg.neg paid

theorem sector_ir_positive (event : DressedEvent) (eta scale : ℝ) (k : PhysicalMomentum)
    (active : sectorActive event eta scale k) : 0<sectorIR scale k :=
  Real.sqrt_pos.mpr (mul_pos active.1 (Real.sqrt_pos.mpr active.2.1))

/-- The source chart uses precisely the original physical spatial transfer, without choosing a new ray. -/
theorem sector_transfer_identity (event : DressedEvent) (eta scale : ℝ) (k : PhysicalMomentum)
    (active : sectorActive event eta scale k) : (sectorIR scale k)^2 • sectorDirection k=scale • k := by
  have radius := Real.sqrt_pos.mpr active.2.1
  have irSquare := Real.sq_sqrt (mul_pos active.1 radius).le
  rw [sectorIR,irSquare,sectorDirection,smul_smul]
  congr 1
  field_simp [radius.ne']

theorem sector_ir_weight (event : DressedEvent) (eta scale : ℝ) (k : PhysicalMomentum)
    (active : sectorActive event eta scale k) :
    (sectorIR scale k : ℂ)^4=(scale : ℂ)^2*(spatialSquare k : ℂ) := by
  have irSquare := Real.sq_sqrt (mul_pos active.1 (Real.sqrt_pos.mpr active.2.1)).le
  have radiusSquare := Real.sq_sqrt active.2.1.le
  have realWeight : (sectorIR scale k)^4=scale^2*spatialSquare k := by
    calc
      _=((sectorIR scale k)^2)^2 := by ring
      _=(scale*Real.sqrt (spatialSquare k))^2 := by rw [sectorIR,irSquare]
      _=scale^2*spatialSquare k := by rw [mul_pow,radiusSquare]
  exact_mod_cast realWeight

private theorem sector_scaled_read (event : DressedEvent) (N : DirectionParameters[X]) (eta scale : ℝ)
    (k : PhysicalMomentum) (active : sectorActive event eta scale k)
    (factor : X^directionSpatialOrder event∣X^4*N) :
    sectorSymbol event N eta scale k=-(scale : ℂ)^2*
      (N.eval₂ (MvPolynomial.eval (directionValues (sectorDirection k))) (sectorIR scale k : ℂ)/
        (directionSpatialDenominator event).eval₂ (MvPolynomial.eval (directionValues (sectorDirection k))) (sectorIR scale k : ℂ)) := by
  rw [sectorSymbol,if_pos active,←normalized_ratio event N (sectorDirection k) (sectorIR scale k)
    (sector_ir_positive event eta scale k active).ne' factor,sector_ir_weight event eta scale k active]
  field_simp [Complex.ofReal_ne_zero.mpr active.2.1.ne']

theorem actual_sector_probe_read (event : DressedEvent) (pd ps : PhysicalMomentum) (dL dR sL sR : CompositeLeg)
    (eta : ℝ) (positive : 0<eta) (scale : ℝ) (k : PhysicalMomentum) (active : sectorActive event eta scale k)
    (spatial : DirectionSpatialFinite event pd ps dL dR sL sR) :
    sectorProbeSymbol event pd ps dL dR sL sR eta scale k=
      -(scale : ℂ)^2*zeroClockProbeRead event (sectorIR scale k) (sectorDirection k) pd ps dL dR sL sR := by
  have chart : sectorDirection k∈sourceDirectionChart event eta := ⟨sector_direction_unit k active.2.1,active.2.2.1⟩
  have regular := (direction_chart_regular event eta positive _ chart).2
  have small : |sectorIR scale k|<sourceDirectionRadius event eta := by rw [abs_of_nonneg (show 0≤ sectorIR scale k from Real.sqrt_nonneg _)];exact active.2.2.2
  have dRegular := actual_direction_spatial_chart event eta positive _ chart _ (sector_ir_positive event eta scale k active).ne' small
  rw [zeroClockProbeRead,zeroClockProbeFraction,reduced_read_at_regular _ _ _ dRegular,
    actual_direction_zero_clock_probe event _ pd ps dL dR sL sR regular,actual_direction_spatial_denominator event _ regular,eval_map,eval_map]
  exact sector_scaled_read event _ eta scale k active spatial.2

theorem actual_sector_em_read (event : DressedEvent) (pd ps : PhysicalMomentum) (dL dR sL sR : CompositeLeg)
    (eta : ℝ) (positive : 0<eta) (scale : ℝ) (k : PhysicalMomentum) (active : sectorActive event eta scale k)
    (spatial : DirectionSpatialFinite event pd ps dL dR sL sR) :
    sectorEMSymbol event eta scale k=-(scale : ℂ)^2 •zeroClockEMRead event (sectorIR scale k) (sectorDirection k) := by
  have chart : sectorDirection k∈sourceDirectionChart event eta := ⟨sector_direction_unit k active.2.1,active.2.2.1⟩
  have regular := (direction_chart_regular event eta positive _ chart).2
  have small : |sectorIR scale k|<sourceDirectionRadius event eta := by rw [abs_of_nonneg (show 0≤ sectorIR scale k from Real.sqrt_nonneg _)];exact active.2.2.2
  have dRegular := actual_direction_spatial_chart event eta positive _ chart _ (sector_ir_positive event eta scale k active).ne' small
  ext mu nu
  simp only [sectorEMSymbol,Matrix.smul_apply,smul_eq_mul]
  rw [zeroClockEMRead,zeroClockEMFraction,reduced_read_at_regular _ _ _ dRegular,
    actual_direction_zero_clock_em event _ regular mu nu,actual_direction_spatial_denominator event _ regular,eval_map,eval_map]
  exact sector_scaled_read event _ eta scale k active (spatial.1 mu nu)

/-- The chart Fourier symbol is the actual full corrected response after its original inner damping limit. -/
theorem actual_sector_response_return (event : DressedEvent) (pd ps : PhysicalMomentum) (dL dR sL sR : CompositeLeg)
    (eta : ℝ) (positive : 0<eta) (scale : ℝ) (k : PhysicalMomentum) (active : sectorActive event eta scale k)
    (clock : DirectionClockFinite event pd ps dL dR sL sR) (spatial : DirectionSpatialFinite event pd ps dL dR sL sR) :
    Tendsto (fun sigma : ℝ => -(scale : ℂ)^2 •correctedEMTensor event (sectorIR scale k) 0 sigma (sectorDirection k))
      (nhdsWithin 0 (Ioi 0)) (𝓝 (sectorEMSymbol event eta scale k)) ∧
    Tendsto (fun sigma : ℝ => -(scale : ℂ)^2*correctedProbeRead event (sectorIR scale k) 0 sigma (sectorDirection k) pd ps dL dR sL sR)
      (nhdsWithin 0 (Ioi 0)) (𝓝 (sectorProbeSymbol event pd ps dL dR sL sR eta scale k)) := by
  have chart : sectorDirection k∈sourceDirectionChart event eta := ⟨sector_direction_unit k active.2.1,active.2.2.1⟩
  have small : |sectorIR scale k|<sourceDirectionRadius event eta := by rw [abs_of_nonneg (show 0≤ sectorIR scale k from Real.sqrt_nonneg _)];exact active.2.2.2
  have paid := actual_direction_finite_chart_return event pd ps dL dR sL sR clock spatial eta positive _ chart _
    (sector_ir_positive event eta scale k active).ne' small
  constructor
  · rw [actual_sector_em_read event pd ps dL dR sL sR eta positive scale k active spatial]
    exact paid.1.const_smul _
  · rw [actual_sector_probe_read event pd ps dL dR sL sR eta positive scale k active spatial]
    exact paid.2.1.const_mul _

end LowEnergy.GaussComposite.ActualDressedAngularSectorFourier
