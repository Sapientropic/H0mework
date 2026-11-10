import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedNoetherSpatialSplit

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
noncomputable section
namespace LowEnergy.GaussComposite.ActualDressedNoetherCoulombUnit
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open CanonicalGradedSpatialSource PreparationVacuumMixedFieldReturn PreparationVacuumPhysicalFeedback
open PreparationVacuumActionFieldLift PreparationVacuumRawJointFeedback PreparationVacuumNoetherChart
open SourceQuantumConfigurationHilbert GaussCoreHilbert
open ActualCompositeFieldCurrent ActualCompositeGaugeBand ActualEMCurrentSplit ActualEMResponseSplit ActualEMCarrierOwn
open ActualDressedFullCoulomb ActualDressedCorrectedGreen ActualDressedEMTensorClock ActualDressedOrderedStatic
open ActualDressedConstraintRead PhysicalEMGaugeRealization MeasureTheory
open scoped Matrix BigOperators Topology SchwartzMap
attribute [local irreducible] correctedEMTensor correctedGreen compositeUnitLeg ActualCompositeFieldCurrent.compositeCurrent

def sourceInputCharge (leg : CompositeLeg) : ℂ := if leg.dual then -1 else 1

def noetherChargeCalibration (p : PhysicalMomentum) (left right : CompositeLeg) : ℂ :=
  sourceInputCharge right*(actualChargeOverlap left right-1)+actualChargeMixingRead left right+
    noetherDensityDefect p left right

theorem actual_calibrated_noether_charge (p : PhysicalMomentum) (left right : CompositeLeg) :
    noetherEMCurrent p left right 0=sourceInputCharge right+noetherChargeCalibration p left right := by
  rw [actual_noether_unit_charge]
  unfold noetherChargeCalibration sourceInputCharge
  ring

def directionalNoetherCoulombCoefficient (event : DressedEvent) (n : PhysicalMomentum) : ℂ :=
  noetherTensorCoefficient event n 0 0/(4*(Real.pi:ℂ))

def otherEMCoefficient (event : DressedEvent) (n pd ps : PhysicalMomentum)
    (dL dR sL sR : CompositeLeg) : ℂ :=
  ∑mu : Fin 4,∑nu : Fin 4,if mu=0 ∧ nu=0 then 0 else
    noetherEMCurrent pd dL dR mu*noetherTensorCoefficient event n mu nu*noetherEMCurrent ps sL sR nu

private theorem temporal_read_split (T : Matrix (Fin 4) (Fin 4) ℂ) (qd qs : Fin 4→ℂ) :
    dotProduct qd (T*ᵥqs)=qd 0*T 0 0*qs 0+
      ∑mu : Fin 4,∑nu : Fin 4,if mu=0 ∧ nu=0 then 0 else qd mu*T mu nu*qs nu := by
  simp [dotProduct,Matrix.mulVec,Fin.sum_univ_four]
  ring

/-- Both actual charge calibrations, all fifteen other EM components and all three non-pure pieces remain in the generated energy coefficient. -/
theorem actual_noether_coulomb_coefficient (event : DressedEvent) (n pd ps : PhysicalMomentum)
    (dL dR sL sR : CompositeLeg) :
    sourceOrderedProbeCoefficient event n pd ps dL dR sL sR/(4*(Real.pi:ℂ))=
      sourceInputCharge dR*sourceInputCharge sR*directionalNoetherCoulombCoefficient event n+
      (noetherChargeCalibration pd dL dR*sourceInputCharge sR+
        sourceInputCharge dR*noetherChargeCalibration ps sL sR+
        noetherChargeCalibration pd dL dR*noetherChargeCalibration ps sL sR)*
          directionalNoetherCoulombCoefficient event n+
      otherEMCoefficient event n pd ps dL dR sL sR/(4*(Real.pi:ℂ))+
      noetherNonPureCoefficient event n pd ps dL dR sL sR/(4*(Real.pi:ℂ)) := by
  have split := temporal_read_split (noetherTensorCoefficient event n)
    (noetherEMCurrent pd dL dR) (noetherEMCurrent ps sL sR)
  have total : sourceOrderedProbeCoefficient event n pd ps dL dR sL sR=
      noetherPureCoefficient event n pd ps dL dR sL sR+noetherNonPureCoefficient event n pd ps dL dR sL sR := by
    unfold noetherNonPureCoefficient
    ring
  rw [total,noetherPureCoefficient,split,actual_calibrated_noether_charge,actual_calibrated_noether_charge]
  unfold directionalNoetherCoulombCoefficient otherEMCoefficient
  ring

/-- Fourier of the generated coefficient packet. Its identification with a direction-varying full physical symbol still requires the source radial read return. -/
theorem actual_coefficient_packet_fourier (event : DressedEvent) (n pd ps : PhysicalMomentum)
    (dL dR sL sR : CompositeLeg) (test : 𝓢(PhysicalMomentum,ℂ)) (x : PhysicalMomentum) :
    sourceOrderedProbeCoefficient event n pd ps dL dR sL sR*emNewtonPacket 1 0 test x=
      ∫y : PhysicalMomentum,
        (sourceOrderedProbeCoefficient event n pd ps dL dR sL sR/(4*(Real.pi:ℂ)))/
          (Real.sqrt (PreparationVacuumPhysicalCharacteristic.spatialSquare y):ℂ)*emPacket test (x-y) := by
  rw [em_newton_massless_convolution,←integral_const_mul]
  apply integral_congr_ae
  filter_upwards with y
  simp only [div_eq_mul_inv,mul_inv_rev]
  ring

def rescaledFieldNoetherCurrent (a : ℝ) (p : PhysicalMomentum) (left right : CompositeLeg) : Fin 4→ℂ :=
  fun mu => -(Stage10.ActionNormalization.phaseMomentum : ℂ)⁻¹*
    rawForm (a • emGaugeField mu) p (compositeUnitLeg left) (compositeUnitLeg right) 0

/-- Actual source field directions are rescaled before their independent current read. -/
theorem actual_generator_current_rescale (a : ℝ) (p : PhysicalMomentum) (left right : CompositeLeg) :
    rescaledFieldNoetherCurrent a p left right=(a:ℂ) • noetherEMCurrent p left right := by
  funext mu
  have one := source_reader_form_basis (emGaugeField mu) p (compositeUnitLeg left) (compositeUnitLeg right) 0
    (by simpa only [norm_zero] using ambientRadius_positive (compositeUnitLeg left))
  have scaled := source_reader_form_basis (a • emGaugeField mu) p (compositeUnitLeg left) (compositeUnitLeg right) 0
    (by simpa only [norm_zero] using ambientRadius_positive (compositeUnitLeg left))
  have reader : rawForm (a • emGaugeField mu) p (compositeUnitLeg left) (compositeUnitLeg right) 0=
      (a:ℂ)*rawForm (emGaugeField mu) p (compositeUnitLeg left) (compositeUnitLeg right) 0 := by
    simp only [noetherForm_source,smul_eq_mul,Pi.smul_apply,Complex.ofReal_mul] at one scaled
    rw [one]
    simpa only [mul_assoc,Finset.mul_sum] using scaled
  simp only [rescaledFieldNoetherCurrent,Pi.smul_apply,smul_eq_mul,actual_noether_em_reader,reader]
  ring

theorem actual_generator_charge_unit_rescale (a : ℝ) (nonzero : a≠0)
    (p : PhysicalMomentum) (left right : CompositeLeg) :
    (a:ℂ)⁻¹ • rescaledFieldNoetherCurrent a p left right=noetherEMCurrent p left right := by
  rw [actual_generator_current_rescale,smul_smul,inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr nonzero),one_smul]

theorem actual_generator_input_charge_rescale (a : ℝ) (leg : CompositeLeg) :
    ((a:ℂ) • compositeChargeCore) (compositeInput leg)=
      ((a:ℂ)*sourceInputCharge leg) • compositeInput leg := by
  rw [LinearMap.smul_apply,composite_input_charge_core,smul_smul]
  rfl

def rescaledEMTensor (a : ℝ) (event : DressedEvent) (eps sigma : ℝ) (n : PhysicalMomentum) :
    Matrix (Fin 4) (Fin 4) ℂ :=
  ((a:ℂ) • emInsertion).transpose*correctedGreen event eps 0 sigma n*((a:ℂ) • emInsertion)

theorem actual_generator_tensor_rescale (a : ℝ) (event : DressedEvent) (eps sigma : ℝ) (n : PhysicalMomentum) :
    rescaledEMTensor a event eps sigma n=(a:ℂ)^2 • correctedEMTensor event eps 0 sigma n := by
  unfold rescaledEMTensor correctedEMTensor emResponseTensor
  rw [Matrix.transpose_smul,Matrix.smul_mul,Matrix.mul_smul,Matrix.smul_mul,smul_smul]
  congr 1
  ring

theorem actual_generator_gram (a : ℝ) :
    ((a:ℂ) • emInsertion).transpose*((a:ℂ) • emInsertion)=
      ((a:ℂ)^2*(3/4:ℂ)) • (1 : Matrix (Fin 4) (Fin 4) ℂ) := by
  rw [Matrix.transpose_smul,Matrix.smul_mul,Matrix.mul_smul,smul_smul,em_coordinate_gram,smul_smul]
  congr 1
  ring

def rescaledNoetherTensorCoefficient (a : ℝ) (event : DressedEvent) (n : PhysicalMomentum) :
    Matrix (Fin 4) (Fin 4) ℂ :=
  (noetherPairScale/(a:ℂ))^2 • ((a:ℂ)^2 • sourceOrderedEMCoefficient event n)

/-- Generator, dual Gram coordinates and electron Noether unit move together on the same actual EM occurrence. -/
theorem actual_noether_tensor_generator_covariance (a : ℝ) (nonzero : a≠0)
    (event : DressedEvent) (n : PhysicalMomentum) :
    rescaledNoetherTensorCoefficient a event n=noetherTensorCoefficient event n := by
  have ac : (a:ℂ)≠0 := Complex.ofReal_ne_zero.mpr nonzero
  have scalar : (noetherPairScale/(a:ℂ))^2*(a:ℂ)^2=noetherPairScale^2 := by
    field_simp [ac]
  unfold rescaledNoetherTensorCoefficient noetherTensorCoefficient
  rw [smul_smul]
  exact congrArg (fun c : ℂ => c • sourceOrderedEMCoefficient event n) scalar

end LowEnergy.GaussComposite.ActualDressedNoetherCoulombUnit
