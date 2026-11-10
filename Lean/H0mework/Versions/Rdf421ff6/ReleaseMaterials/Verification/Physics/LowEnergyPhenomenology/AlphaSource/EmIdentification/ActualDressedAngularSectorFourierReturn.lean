import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedAngularSectorActualRead

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
noncomputable section
namespace LowEnergy.GaussComposite.ActualDressedAngularSectorFourier
open Polynomial CanonicalGradedSpatialSource PreparationVacuumMixedFieldReturn PreparationVacuumPhysicalFeedback
open PreparationVacuumPhysicalCharacteristic PreparationVacuumStaticSpatialSource ActualDressedFullCoulomb
open ActualDressedAngularSpherePrice ActualDressedOrderedStatic ActualDressedCorrectedElectronRead ActualDressedEMTensorClock ActualCompositeFieldCurrent
open ActualEMCarrierOwn MeasureTheory Filter Set
open scoped Topology Matrix SchwartzMap

/-- The angular coefficient remains a function of direction inside the original physical Newton multiplier. -/
def sectorCoefficientSymbol (event : DressedEvent) (N : DirectionParameters[X]) (eta : ℝ) (k : PhysicalMomentum) : ℂ := by
  classical
  exact if 0<spatialSquare k ∧ eta≤‖directionLeadingRead event (sectorDirection k)‖ then
    (spatialSquare k : ℂ)⁻¹*directionCoulombCoefficient event N (sectorDirection k) else 0

def sectorCoefficientPacket (event : DressedEvent) (N : DirectionParameters[X]) (eta : ℝ)
    (test : 𝓢(PhysicalMomentum,ℂ)) (x : PhysicalMomentum) : ℂ :=
  ∫frequency,sourceSpatialPhase frequency x*test frequency*sectorCoefficientSymbol event N eta (sourceSpatialMomentum frequency)

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

private theorem reduced_constant (event : DressedEvent) :
    (directionReducedDenominator event).coeff 0=directionLeadingDenominator event := by
  have factor : X^directionSpatialOrder event∣directionSpatialDenominator event :=
    X_pow_dvd_iff.mpr (fun _ less => coeff_eq_zero_of_lt_natTrailingDegree less)
  obtain ⟨Q,eq⟩ := factor
  have quotient : directionReducedDenominator event=Q := by
    unfold directionReducedDenominator
    rw [eq,mul_divByMonic_cancel_left Q (monic_X_pow _)]
  rw [quotient]
  change Q.coeff 0=(directionSpatialDenominator event).coeff (directionSpatialOrder event)
  rw [eq]
  simpa only [zero_add] using (coeff_X_pow_mul Q (directionSpatialOrder event) 0).symm

private theorem sector_ir_limit (k : PhysicalMomentum) :
    Tendsto (fun scale : ℝ => sectorIR scale k) (nhdsWithin 0 (Ioi 0)) (𝓝 0) := by
  have continuous : Continuous (fun scale : ℝ => Real.sqrt (scale*Real.sqrt (spatialSquare k))) := by fun_prop
  simpa only [sectorIR,zero_mul,Real.sqrt_zero] using (continuous.continuousAt (x:=0)).tendsto.mono_left nhdsWithin_le_nhds

theorem actual_sector_symbol_spatial_return (event : DressedEvent) (N : DirectionParameters[X]) (eta : ℝ)
    (positive : 0<eta) (k : PhysicalMomentum) :
    Tendsto (fun scale : ℝ => sectorSymbol event N eta scale k) (nhdsWithin 0 (Ioi 0))
      (𝓝 (sectorCoefficientSymbol event N eta k)) := by
  classical
  by_cases region : 0<spatialSquare k ∧ eta≤‖directionLeadingRead event (sectorDirection k)‖
  · let n := sectorDirection k
    let f := MvPolynomial.eval (directionValues n)
    have chart : n∈sourceDirectionChart event eta := ⟨sector_direction_unit k region.1,region.2⟩
    have regular := (direction_chart_regular event eta positive n chart).2
    have qRegular : f ((directionReducedDenominator event).coeff 0)≠0 := by rw [reduced_constant];exact regular
    have qLimit := quotient_limit (directionScaledNumerator event N) (directionReducedDenominator event) f qRegular
    have point : -f ((directionScaledNumerator event N).coeff 0)/f ((directionReducedDenominator event).coeff 0)=
        directionCoulombCoefficient event N n := by rw [reduced_constant];rfl
    rw [point] at qLimit
    have read := (tendsto_const_nhds (x:=(spatialSquare k : ℂ)⁻¹)).mul (qLimit.comp (sector_ir_limit k))
    rw [sectorCoefficientSymbol,if_pos region]
    apply Tendsto.congr' _ read
    have near := (sector_ir_limit k).eventually (eventually_lt_nhds (source_direction_radius_positive event eta positive))
    filter_upwards [near,self_mem_nhdsWithin] with scale small positiveScale
    have active : sectorActive event eta scale k := ⟨positiveScale,region.1,region.2,small⟩
    rw [sectorSymbol,if_pos active]
    rfl
  · have inactive (scale : ℝ) : ¬sectorActive event eta scale k := fun active => region ⟨active.2.1,active.2.2.1⟩
    simp only [sectorSymbol,if_neg (inactive _),sectorCoefficientSymbol,if_neg region]
    exact tendsto_const_nhds

/-- The original spatial Fourier test consumes the complete angular source read with its internally paid chart domination. -/
theorem actual_sector_fourier_return (event : DressedEvent) (N : DirectionParameters[X]) (eta : ℝ) (positive : 0<eta)
    (test : 𝓢(PhysicalMomentum,ℂ)) (x : PhysicalMomentum) :
    Tendsto (fun scale : ℝ => sectorFourierPacket event N eta scale test x) (nhdsWithin 0 (Ioi 0))
      (𝓝 (sectorCoefficientPacket event N eta test x)) := by
  unfold sectorFourierPacket sectorCoefficientPacket
  apply tendsto_integral_filter_of_dominated_convergence (μ:=volume)
    (fun frequency=>sourceAngularReadPrice event N eta*‖test frequency‖/spatialSquare (sourceSpatialMomentum frequency))
  · exact Eventually.of_forall (fun scale => (actual_sector_fourier_integrable event N eta positive scale test x).aestronglyMeasurable)
  · exact Eventually.of_forall (fun scale => Eventually.of_forall (fun frequency => by
      have phase : ‖sourceSpatialPhase frequency x‖=1 := by simp [sourceSpatialPhase,Complex.norm_exp]
      rw [norm_mul,norm_mul,phase,one_mul]
      exact (mul_le_mul_of_nonneg_left (actual_sector_symbol_price event N eta positive scale _) (norm_nonneg _)).trans_eq (by ring)))
  · exact em_physical_coulomb_budget_integrable _ test
  · exact Eventually.of_forall (fun frequency => (tendsto_const_nhds (x:=sourceSpatialPhase frequency x*test frequency)).mul
      (actual_sector_symbol_spatial_return event N eta positive (sourceSpatialMomentum frequency)))

theorem source_sector_full_probe_packet_return (event : DressedEvent) (pd ps : PhysicalMomentum)
    (dL dR sL sR : CompositeLeg) (eta : ℝ) (positive : 0<eta) (test : 𝓢(PhysicalMomentum,ℂ)) (x : PhysicalMomentum) :
    Tendsto (fun scale : ℝ => sectorFourierPacket event (directionZeroClockProbe event pd ps dL dR sL sR) eta scale test x)
      (nhdsWithin 0 (Ioi 0)) (𝓝 (sectorCoefficientPacket event (directionZeroClockProbe event pd ps dL dR sL sR) eta test x)) :=
  actual_sector_fourier_return event _ eta positive test x

theorem source_sector_full_tensor_packet_return (event : DressedEvent) (eta : ℝ) (positive : 0<eta)
    (test : 𝓢(PhysicalMomentum,ℂ)) (x : PhysicalMomentum) :
    Tendsto (fun scale : ℝ => fun mu nu : Fin 4 => sectorFourierPacket event (directionZeroClockEM event mu nu) eta scale test x)
      (nhdsWithin 0 (Ioi 0)) (𝓝 (fun mu nu : Fin 4 => sectorCoefficientPacket event (directionZeroClockEM event mu nu) eta test x)) := by
  apply tendsto_pi_nhds.2
  intro mu
  apply tendsto_pi_nhds.2
  intro nu
  exact actual_sector_fourier_return event _ eta positive test x

/-- The source chart branch connects actual inner damping, all sixteen directional Fourier packets and both full probe legs. -/
theorem actual_sector_full_fourier_return (event : DressedEvent) (pd ps : PhysicalMomentum)
    (dL dR sL sR : CompositeLeg) (clock : DirectionClockFinite event pd ps dL dR sL sR)
    (spatial : DirectionSpatialFinite event pd ps dL dR sL sR) (eta : ℝ) (positive : 0<eta)
    (test : 𝓢(PhysicalMomentum,ℂ)) (x : PhysicalMomentum) :
    (∀scale : ℝ,∀k : PhysicalMomentum,sectorActive event eta scale k→
      Tendsto (fun sigma : ℝ => -(scale : ℂ)^2 •correctedEMTensor event (sectorIR scale k) 0 sigma (sectorDirection k))
        (nhdsWithin 0 (Ioi 0)) (𝓝 (sectorEMSymbol event eta scale k)) ∧
      Tendsto (fun sigma : ℝ => -(scale : ℂ)^2*correctedProbeRead event (sectorIR scale k) 0 sigma (sectorDirection k) pd ps dL dR sL sR)
        (nhdsWithin 0 (Ioi 0)) (𝓝 (sectorProbeSymbol event pd ps dL dR sL sR eta scale k))) ∧
    Tendsto (fun scale : ℝ => fun mu nu : Fin 4 => sectorFourierPacket event (directionZeroClockEM event mu nu) eta scale test x)
      (nhdsWithin 0 (Ioi 0)) (𝓝 (fun mu nu : Fin 4 => sectorCoefficientPacket event (directionZeroClockEM event mu nu) eta test x)) ∧
    Tendsto (fun scale : ℝ => sectorFourierPacket event (directionZeroClockProbe event pd ps dL dR sL sR) eta scale test x)
      (nhdsWithin 0 (Ioi 0)) (𝓝 (sectorCoefficientPacket event (directionZeroClockProbe event pd ps dL dR sL sR) eta test x)) :=
  ⟨fun scale k active => actual_sector_response_return event pd ps dL dR sL sR eta positive scale k active clock spatial,
    source_sector_full_tensor_packet_return event eta positive test x,
    source_sector_full_probe_packet_return event pd ps dL dR sL sR eta positive test x⟩

end LowEnergy.GaussComposite.ActualDressedAngularSectorFourier
