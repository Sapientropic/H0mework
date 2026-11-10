import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedCompleteUnitResponse
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedNoetherCoulombCoefficient

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
noncomputable section
namespace LowEnergy.GaussComposite.ActualDressedEMWholeUnitCovariance
open SaturationMonoid.PhysicsCore CanonicalGradedSpatialSource PreparationVacuumMixedFieldReturn
open GaussCoreHilbert GaussCoreDifferential GaussHistoryHilbert
open PreparationVacuumJointFieldResponse PreparationVacuumRawJointFeedback PreparationVacuumNoetherChart
open PreparationVacuumActionFieldLift PreparationVacuumGaugeSourceInjection
open PreparationPhysicalActionUnits PreparationVacuumPhysicalHalfAxis PreparationVacuumPhysicalFeedback
open ActualDressedFullCoulomb ActualDressedCorrectedGreen ActualDressedCorrectedElectronRead
open ActualDressedEMTensorClock ActualDressedOrderedStatic ActualDressedNoetherCoulombUnit
open ActualDressedConstraintRead
open ActualCompositeFieldCurrent ActualCompositeGaugeBand ActualEMCurrentSplit ActualEMResponseSplit ActualEMCarrierOwn
open ActualDressedEMSourceSpectrum ActualDressedZeroClockFrequency ActualDressedZeroClockVector
open ActualDressedEMPhysicalResidueFlux ActualDressedEMVisiblePoleTransport ActualDressedEMPolePairEnergy
open ActualDressedEMFullPoleFlux ActualDressedEMTaylorPoleFlux ActualDressedEMClockDispersion
open ActualDressedEMQuantumThreshold ActualDressedEMZeroClockColumns
open PreparationVacuumPhysicalCharacteristic PreparationVacuumPhysicalPoleSheet
open LowEnergy.ActualDressedVisiblePole
open Filter MeasureTheory Set
open scoped Matrix BigOperators Topology InnerProductSpace
local instance : NormedAlgebra ℝ (H→L[ℂ]H) := NormedAlgebra.restrictScalars ℝ ℂ _
attribute [local irreducible] physicalTime jointGenerator rawForm compositeUnitLeg ActualCompositeFieldCurrent.compositeCurrent
  emInsertion emCoordinateCurrent noetherEMCurrent sourceDensityEnergyRead sourceActualUnitDefect
  Stage10.ActionNormalization.phaseMomentum correctedEMTensor correctedProbeRead
  emPhysicalSpectralRoots emCommonSpectralRoots emPhysicalLeftPoleCoefficient
  emVisiblePairedClockEnergy emVisiblePairedHigherEnergy emVisiblePairedSourceInput emVisiblePairedAnalyticDebt
  emCorrectedPoleSeries emNormalizedPoleColumnSeries emLeftPoleSeries emLeftClockDefectSeries
  emFullColumnPoleOrder emFullRowPoleOrder correctedPhysicalClockJet

def sourceUnitActionMomentum (u : SourceUnits) : ℝ :=
  Stage10.ActionNormalization.phaseMomentum/(u.energy*u.time)

def sourceUnitEnergyHamiltonian (u : SourceUnits) (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) : H→L[ℂ]H :=
  sourceUnitHamiltonian u (u.length • p) F 0

private theorem real_scale_twice {V : Type*} [AddCommMonoid V] [Module ℝ V]
    (c d : ℝ) (v : V) : c • (d • v)=(c*d) • v := smul_smul c d v

theorem source_unit_energy_hamiltonian (u : SourceUnits) (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) :
    sourceUnitEnergyHamiltonian u p F=(Stage10.ActionNormalization.phaseMomentum/u.energy) • jointGenerator p F 0 0 := by
  have generator : sourceUnitGenerator u (u.length • p) F 0 0=u.time • jointGenerator p F 0 0 := by
    simpa only [sourceUnitOccurrenceGenerator,mul_zero,smul_zero] using
      source_unit_occurrence_generator u p F 0 0
  have scalar : (Stage10.ActionNormalization.phaseMomentum/(u.energy*u.time))*u.time=
      Stage10.ActionNormalization.phaseMomentum/u.energy := by
    field_simp [u.energy_positive.ne',u.time_positive.ne']
  unfold sourceUnitEnergyHamiltonian sourceUnitHamiltonian
  exact (congrArg (fun M : H→L[ℂ]H => (Stage10.ActionNormalization.phaseMomentum/(u.energy*u.time)) • M)
    generator).trans ((real_scale_twice (V:=H→L[ℂ]H)
      (Stage10.ActionNormalization.phaseMomentum/(u.energy*u.time)) u.time (jointGenerator p F 0 0)).trans
        (congrArg (fun c : ℝ => c • jointGenerator p F 0 0) scalar))

def sourceUnitOriginalEnergyRead (u : SourceUnits) (p : PhysicalMomentum) (a b : QuantumTest) : ℂ :=
  (u.energy : ℂ)⁻¹*sourceDensityEnergyRead p a b

private theorem real_operator_pair (c : ℝ) (G : H→L[ℂ]H) (a b : H) :
    inner ℂ a ((c • G) b)=(c : ℂ)*inner ℂ a (G b) := by
  change inner ℂ a (c • G b)=(c : ℂ)*inner ℂ a (G b)
  have scale : c • G b=(c : ℂ) • G b := RCLike.real_smul_eq_coe_smul (K:=ℂ) c (G b)
  rw [scale,inner_smul_right]

/-- The original time/action Hamiltonian and its complete calibration share the new energy unit. -/
theorem source_unit_original_energy_read (u : SourceUnits) (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index)
    (a b : QuantumTest) :
    sourceUnitOriginalEnergyRead u p a b=inner ℂ (embed a) (sourceUnitEnergyHamiltonian u p F (embed b))+
      ((Stage10.ActionNormalization.phaseMomentum/u.energy : ℝ) : ℂ)*sourceActualUnitDefect p F a b := by
  have pair := (congrArg (fun M : H→L[ℂ]H => inner ℂ (embed a) (M (embed b)))
    (source_unit_energy_hamiltonian u p F)).trans
      (real_operator_pair (Stage10.ActionNormalization.phaseMomentum/u.energy)
        (jointGenerator p F 0 0) (embed a) (embed b))
  rw [sourceUnitOriginalEnergyRead,source_action_hamiltonian_energy,pair]
  push_cast
  ring

private theorem unit_phase_energy_product (U G : H→L[ℂ]H) (h : ℂ) :
    (Complex.I*h) • (U*((-Complex.I) • G))=U*(h • G) := by
  apply ContinuousLinearMap.ext
  intro b
  change (Complex.I*h) • U ((-Complex.I) • G b)=U (h • G b)
  have scalar : (Complex.I*h)*(-Complex.I)=h := by
    calc
      _= -(Complex.I*Complex.I)*h := by ring
      _=_ := by rw [←pow_two,Complex.I_sq,neg_neg,one_mul]
  calc
    _=(Complex.I*h) • ((-Complex.I) • U (G b)) :=
      congrArg (fun v : H => (Complex.I*h) • v) (U.map_smul (-Complex.I) (G b))
    _=((Complex.I*h)*(-Complex.I)) • U (G b) := smul_smul _ _ _
    _=h • U (G b) := congrArg (fun c : ℂ => c • U (G b)) scalar
    _=U (h • G b) := (U.map_smul h (G b)).symm

private theorem real_complex_operator_scale (c : ℝ) (G : H→L[ℂ]H) : c • G=(c : ℂ) • G := by
  apply ContinuousLinearMap.ext
  intro b
  change c • G b=(c : ℂ) • G b
  exact RCLike.real_smul_eq_coe_smul (K:=ℂ) c (G b)

attribute [local irreducible] sourceUnitCircuitTime sourceUnitOccurrenceGenerator sourceUnitEnergyHamiltonian

/-- The new clock derivative pays i*h_new against the generated energy Hamiltonian, including the original action calibration. -/
theorem source_unit_clock_action_energy (u : SourceUnits) (p : PhysicalMomentum)
    (F : GaussUnitaryHistory.Index) (age : ℝ) :
    HasDerivAt (fun t : ℝ => sourceUnitCircuitTime u p F t 0)
      (sourceUnitCircuitTime u p F age 0*((-Complex.I) • sourceUnitOccurrenceGenerator u p F 0 0)) age ∧
    (Complex.I*(sourceUnitActionMomentum u : ℂ)) •
      (sourceUnitCircuitTime u p F age 0*((-Complex.I) • sourceUnitOccurrenceGenerator u p F 0 0))=
        sourceUnitCircuitTime u p F age 0*sourceUnitEnergyHamiltonian u p F ∧
    ∀a b : QuantumTest, sourceUnitOriginalEnergyRead u p a b=
      inner ℂ (embed a) (sourceUnitEnergyHamiltonian u p F (embed b))+
        ((Stage10.ActionNormalization.phaseMomentum/u.energy : ℝ) : ℂ)*sourceActualUnitDefect p F a b := by
  refine ⟨?_,?_,source_unit_original_energy_read u p F⟩
  · have original := (source_action_clock_energy p F (u.time*age)).1
    have timeDerivative : HasDerivAt (fun t : ℝ => physicalTime p F (u.time*t) 0)
        (u.time • (physicalTime p F (u.time*age) 0*((-Complex.I) • jointGenerator p F 0 0))) age := by
      simpa only [Function.comp_def,mul_one] using original.scomp age ((hasDerivAt_id age).const_mul u.time)
    have time (t : ℝ) : sourceUnitCircuitTime u p F t 0=physicalTime p F (u.time*t) 0 := by
      simpa only [smul_zero] using source_unit_circuit_time u p F t 0
    have same : (fun t : ℝ => sourceUnitCircuitTime u p F t 0)=
        (fun t : ℝ => physicalTime p F (u.time*t) 0) := funext time
    have actual : HasDerivAt (fun t : ℝ => sourceUnitCircuitTime u p F t 0)
        (u.time • (physicalTime p F (u.time*age) 0*((-Complex.I) • jointGenerator p F 0 0))) age := by
      exact Eq.mpr (congrArg (fun f : ℝ→(H→L[ℂ]H) => HasDerivAt f
        (u.time • (physicalTime p F (u.time*age) 0*((-Complex.I) • jointGenerator p F 0 0))) age) same)
          timeDerivative
    have generator : sourceUnitOccurrenceGenerator u p F 0 0=u.time • jointGenerator p F 0 0 := by
      simpa only [smul_zero] using source_unit_occurrence_generator u p F 0 0
    apply actual.congr_deriv
    apply ContinuousLinearMap.ext
    intro b
    change u.time • (physicalTime p F (u.time*age) 0) ((-Complex.I) • jointGenerator p F 0 0 b)=
      sourceUnitCircuitTime u p F age 0 ((-Complex.I) • sourceUnitOccurrenceGenerator u p F 0 0 b)
    have timeValue := congrArg (fun M : H→L[ℂ]H => M ((-Complex.I) • sourceUnitOccurrenceGenerator u p F 0 0 b)) (time age)
    have value : sourceUnitOccurrenceGenerator u p F 0 0 b=(u.time : ℂ) • jointGenerator p F 0 0 b := by
      have equation := congrArg (fun M : H→L[ℂ]H => M b) generator
      change sourceUnitOccurrenceGenerator u p F 0 0 b=u.time • jointGenerator p F 0 0 b at equation
      exact equation.trans (RCLike.real_smul_eq_coe_smul (K:=ℂ) u.time (jointGenerator p F 0 0 b))
    have outer := RCLike.real_smul_eq_coe_smul (K:=ℂ) u.time
      ((physicalTime p F (u.time*age) 0) ((-Complex.I) • jointGenerator p F 0 0 b))
    calc
      _=(u.time : ℂ) • (physicalTime p F (u.time*age) 0) ((-Complex.I) • jointGenerator p F 0 0 b) := outer
      _=(u.time : ℂ) • ((-Complex.I) • (physicalTime p F (u.time*age) 0) (jointGenerator p F 0 0 b)) :=
        congrArg (fun v : H => (u.time : ℂ) • v)
          ((physicalTime p F (u.time*age) 0).map_smul (-Complex.I) (jointGenerator p F 0 0 b))
      _=((-Complex.I)*(u.time : ℂ)) • (physicalTime p F (u.time*age) 0) (jointGenerator p F 0 0 b) := by
        rw [smul_smul,mul_comm (u.time : ℂ) (-Complex.I)]
      _=(physicalTime p F (u.time*age) 0) ((-Complex.I) • ((u.time : ℂ) • jointGenerator p F 0 0 b)) :=
        ((physicalTime p F (u.time*age) 0).map_smul ((-Complex.I)*(u.time : ℂ))
          (jointGenerator p F 0 0 b)).symm.trans
            (congrArg (physicalTime p F (u.time*age) 0)
              (smul_smul (-Complex.I) (u.time : ℂ) (jointGenerator p F 0 0 b)).symm)
      _=(physicalTime p F (u.time*age) 0) ((-Complex.I) • sourceUnitOccurrenceGenerator u p F 0 0 b) :=
        congrArg (fun v : H => (physicalTime p F (u.time*age) 0) ((-Complex.I) • v)) value.symm
      _=sourceUnitCircuitTime u p F age 0 ((-Complex.I) • sourceUnitOccurrenceGenerator u p F 0 0 b) := timeValue.symm
  · have hamiltonian : sourceUnitEnergyHamiltonian u p F=
        (sourceUnitActionMomentum u : ℂ) • sourceUnitOccurrenceGenerator u p F 0 0 := by
      simp only [sourceUnitEnergyHamiltonian,sourceUnitHamiltonian,sourceUnitActionMomentum,
        sourceUnitOccurrenceGenerator,mul_zero,real_complex_operator_scale]
    exact (unit_phase_energy_product (sourceUnitCircuitTime u p F age 0)
      (sourceUnitOccurrenceGenerator u p F 0 0) (sourceUnitActionMomentum u : ℂ)).trans
        (congrArg (fun M : H→L[ℂ]H => sourceUnitCircuitTime u p F age 0*M) hamiltonian).symm

private theorem raw_reader_scale (r : ℝ) (reader : Field289) (p : PhysicalMomentum) (a b : QuantumTest) :
    rawForm (r • reader) p a b 0=(r : ℂ)*rawForm reader p a b 0 := by
  have one := source_reader_form_basis reader p a b 0
    (by simpa only [norm_zero] using ambientRadius_positive a)
  have scaled := source_reader_form_basis (r • reader) p a b 0
    (by simpa only [norm_zero] using ambientRadius_positive a)
  simp only [noetherForm_source,smul_eq_mul,Pi.smul_apply,Complex.ofReal_mul] at one scaled
  rw [one]
  simpa only [mul_assoc,Finset.mul_sum] using scaled

/-- Each current slot is read from the original action on the same actual independent-dual endpoints. -/
def sourceUnitWholeCurrent (u : SourceUnits) (p : PhysicalMomentum) (left right : CompositeLeg) : Fin 289→ℂ :=
  fun i => -(u.energy : ℂ)⁻¹*rawForm (u.field • fieldUnit i) p (compositeUnitLeg left) (compositeUnitLeg right) 0

theorem source_unit_whole_current_generated (u : SourceUnits) (p : PhysicalMomentum) (left right : CompositeLeg) :
    sourceUnitWholeCurrent u p left right=((u.field : ℂ)/(u.energy : ℂ)) •
      ActualCompositeFieldCurrent.compositeCurrent p left right := by
  funext i
  unfold sourceUnitWholeCurrent ActualCompositeFieldCurrent.compositeCurrent
  rw [raw_reader_scale,Pi.smul_apply,smul_eq_mul]
  ring

theorem source_unit_whole_current_contact (u : SourceUnits) (p : PhysicalMomentum) (left right : CompositeLeg)
    (i : Fin 289) (force : Field289) :
    HasDerivAt (fun r : ℝ => -(u.energy : ℂ)⁻¹*rawForm (u.field • fieldUnit i) p
      (compositeUnitLeg left) (compositeUnitLeg right) (r • (u.field • force)))
      (-(u.energy : ℂ)⁻¹*rawContactForm (u.field • fieldUnit i) (u.field • force) p
        (compositeUnitLeg left) (compositeUnitLeg right)) 0 :=
  (rawForm_direction (u.field • fieldUnit i) (u.field • force) p
    (compositeUnitLeg left) (compositeUnitLeg right)).const_mul _

def sourceUnitCoordinateCurrent (u : SourceUnits) (f : Fin 289→ℂ) : Fin 4→ℂ :=
  ((4/3 : ℂ)*(((u.field : ℂ)*(u.generator : ℂ))^2)⁻¹) • ((sourceUnitEMInsertion u).transpose*ᵥf)

def sourceUnitElectronVertex (u : SourceUnits) (p : PhysicalMomentum) (left right : CompositeLeg) : Fin 4→ℂ :=
  sourceUnitCoordinateCurrent u (sourceUnitWholeCurrent u p left right)

def sourceUnitNoetherPairScale (u : SourceUnits) : ℂ :=
  (4/3 : ℂ)*(sourceUnitActionMomentum u : ℂ)*(u.time : ℂ)/(u.generator : ℂ)

theorem source_unit_literal_gram (u : SourceUnits) :
    (sourceUnitEMInsertion u).transpose*sourceUnitEMInsertion u=
      (((u.field : ℂ)*(u.generator : ℂ))^2*(3/4 : ℂ)) • (1 : Matrix (Fin 4) (Fin 4) ℂ) := by
  rw [sourceUnitEMInsertion,Matrix.transpose_smul,Matrix.smul_mul,Matrix.mul_smul,
    smul_smul,em_coordinate_gram,smul_smul,pow_two]

theorem source_unit_actual_input_charge (u : SourceUnits) (leg : CompositeLeg) :
    (u.generator : ℂ)⁻¹ • (((u.generator : ℂ) • compositeChargeCore) (compositeInput leg))=
      sourceInputCharge leg • compositeInput leg := by
  rw [actual_generator_input_charge_rescale,smul_smul,←mul_assoc,
    inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr u.generator_nonzero),one_mul]

theorem source_unit_electron_coordinate (u : SourceUnits) (p : PhysicalMomentum) (left right : CompositeLeg) :
    sourceUnitElectronVertex u p left right=((u.energy : ℂ)*(u.generator : ℂ))⁻¹ •
      emCoordinateCurrent (ActualCompositeFieldCurrent.compositeCurrent p left right) := by
  rw [sourceUnitElectronVertex,sourceUnitCoordinateCurrent,source_unit_whole_current_generated,
    sourceUnitEMInsertion,Matrix.transpose_smul,Matrix.smul_mulVec,Matrix.mulVec_smul,smul_smul,smul_smul,
    emCoordinateCurrent,emCurrent,smul_smul]
  apply congrArg (fun c : ℂ => c • (emInsertion.transpose*ᵥActualCompositeFieldCurrent.compositeCurrent p left right))
  have field_ne := Complex.ofReal_ne_zero.mpr u.field_nonzero
  have generator_ne := Complex.ofReal_ne_zero.mpr u.generator_nonzero
  have energy_ne := Complex.ofReal_ne_zero.mpr u.energy_positive.ne'
  field_simp [field_ne,generator_ne,energy_ne]

/-- The electron unit is generated by the literal new Gram and the paid original time/action read. -/
theorem source_unit_electron_noether_vertex (u : SourceUnits) (p : PhysicalMomentum) (left right : CompositeLeg) :
    sourceUnitElectronVertex u p left right=sourceUnitNoetherPairScale u • noetherEMCurrent p left right := by
  rw [source_unit_electron_coordinate,actual_coordinate_noether_unit,smul_smul]
  apply congrArg (fun c : ℂ => c • noetherEMCurrent p left right)
  have energy_ne := Complex.ofReal_ne_zero.mpr u.energy_positive.ne'
  have time_ne := Complex.ofReal_ne_zero.mpr u.time_positive.ne'
  have generator_ne := Complex.ofReal_ne_zero.mpr u.generator_nonzero
  unfold sourceUnitNoetherPairScale sourceUnitActionMomentum
  push_cast
  field_simp [energy_ne,time_ne,generator_ne]

theorem source_unit_electron_calibration (u : SourceUnits) (p : PhysicalMomentum) (left right : CompositeLeg) :
    sourceUnitElectronVertex u p left right 0=sourceUnitNoetherPairScale u*
      (sourceInputCharge right+noetherChargeCalibration p left right) := by
  rw [source_unit_electron_noether_vertex,Pi.smul_apply,smul_eq_mul,actual_calibrated_noether_charge]

def sourceUnitFullProbe (u : SourceUnits) (event : DressedEvent) (eps s sigma : ℝ) (n pd ps : PhysicalMomentum)
    (dL dR sL sR : CompositeLeg) : ℂ :=
  emCurrentObservation (sourceUnitCorrectedGreen u event eps s sigma n)
    (sourceUnitWholeCurrent u pd dL dR) (sourceUnitWholeCurrent u ps sL sR)

theorem source_unit_full_probe_covariance (u : SourceUnits) (event : DressedEvent) (eps s sigma : ℝ)
    (n pd ps : PhysicalMomentum) (dL dR sL sR : CompositeLeg) :
    sourceUnitFullProbe u event eps s sigma n pd ps dL dR sL sR=
      ((u.energy : ℂ)*(u.length : ℂ)^3)⁻¹*correctedProbeRead event eps s sigma n pd ps dL dR sL sR := by
  rw [sourceUnitFullProbe,source_unit_whole_current_generated,source_unit_whole_current_generated,
    sourceUnitCorrectedGreen,actual_corrected_probe_raw_read]
  simp only [emCurrentObservation,Matrix.smul_mulVec,Matrix.mulVec_smul,
    dotProduct_smul,smul_dotProduct,smul_eq_mul,←mul_assoc]
  apply congrArg (fun c : ℂ => c*dotProduct (ActualCompositeFieldCurrent.compositeCurrent pd dL dR)
    (correctedGreen event eps s sigma n*ᵥActualCompositeFieldCurrent.compositeCurrent ps sL sR))
  have field_ne := Complex.ofReal_ne_zero.mpr u.field_nonzero
  have energy_ne := Complex.ofReal_ne_zero.mpr u.energy_positive.ne'
  have length_ne := Complex.ofReal_ne_zero.mpr u.length_positive.ne'
  unfold sourceUnitResponseFactor sourceDensityUnit
  push_cast
  field_simp [field_ne,energy_ne,length_ne]

/-- All three mixed and residual pieces remain explicit in the complete current read. -/
theorem source_unit_full_probe_four_parts (u : SourceUnits) (event : DressedEvent) (eps s sigma : ℝ)
    (n pd ps : PhysicalMomentum) (dL dR sL sR : CompositeLeg) :
    let G := sourceUnitCorrectedGreen u event eps s sigma n
    let fd := sourceUnitWholeCurrent u pd dL dR
    let fs := sourceUnitWholeCurrent u ps sL sR
    sourceUnitFullProbe u event eps s sigma n pd ps dL dR sL sR=
      emPureObservation G fd fs+emCurrentObservation G (emCurrentForce fd) (emCurrentResidual fs)+
        emCurrentObservation G (emCurrentResidual fd) (emCurrentForce fs)+
        emCurrentObservation G (emCurrentResidual fd) (emCurrentResidual fs) :=
  em_response_four_parts _ _ _

def sourceUnitZeroEMTensor (u : SourceUnits) (event : DressedEvent) (eps : ℝ) (n : PhysicalMomentum) :
    Matrix (Fin 4) (Fin 4) ℂ :=
  limUnder (nhdsWithin 0 (Ioi 0)) (fun sigma : ℝ => sourceUnitFullEMTensor u event eps 0 sigma n)

def sourceUnitCoulombTensor (u : SourceUnits) (event : DressedEvent) (n : PhysicalMomentum) : Matrix (Fin 4) (Fin 4) ℂ :=
  limUnder (nhdsWithin 0 ({0}ᶜ)) (fun eps : ℝ =>
    (-((u.length : ℂ)*(eps : ℂ)^2)^2) • (sourceUnitNoetherPairScale u)^2 • sourceUnitZeroEMTensor u event eps n)

def sourceUnitCoulomb (u : SourceUnits) (event : DressedEvent) (n : PhysicalMomentum) : ℂ :=
  sourceUnitCoulombTensor u event n 0 0/(4*(Real.pi : ℂ))

private theorem electron_tensor_scale (u : SourceUnits) :
    (u.length : ℂ)^2*(sourceUnitNoetherPairScale u)^2*((u.generator : ℂ)^2/(sourceDensityUnit u : ℂ))=
      ((u.energy : ℂ)*(u.length : ℂ))⁻¹*noetherPairScale^2 := by
  have energy_ne := Complex.ofReal_ne_zero.mpr u.energy_positive.ne'
  have length_ne := Complex.ofReal_ne_zero.mpr u.length_positive.ne'
  have time_ne := Complex.ofReal_ne_zero.mpr u.time_positive.ne'
  have generator_ne := Complex.ofReal_ne_zero.mpr u.generator_nonzero
  unfold sourceUnitNoetherPairScale sourceUnitActionMomentum sourceDensityUnit noetherPairScale
  push_cast
  field_simp [energy_ne,length_ne,time_ne,generator_ne]

private theorem zero_tensor_generated (u : SourceUnits) (event : DressedEvent) (eps : ℝ) (n : PhysicalMomentum)
    (returned : Tendsto (fun sigma : ℝ => correctedEMTensor event eps 0 sigma n)
      (nhdsWithin 0 (Ioi 0)) (𝓝 (zeroClockEMRead event eps n))) :
    sourceUnitZeroEMTensor u event eps n=((u.generator : ℂ)^2/(sourceDensityUnit u : ℂ)) • zeroClockEMRead event eps n := by
  have actual := returned.const_smul ((u.generator : ℂ)^2/(sourceDensityUnit u : ℂ))
  have unit : Tendsto (fun sigma : ℝ => sourceUnitFullEMTensor u event eps 0 sigma n)
      (nhdsWithin 0 (Ioi 0)) (𝓝 (((u.generator : ℂ)^2/(sourceDensityUnit u : ℂ)) • zeroClockEMRead event eps n)) := by
    simpa only [source_unit_all_sixteen_tensor] using actual
  exact unit.limUnder_eq

theorem source_unit_actual_coulomb_generated (u : SourceUnits) (event : DressedEvent) (n : PhysicalMomentum)
    (nonzero : irClockDeterminant event n≠0)
    (factors : ∀mu nu,Polynomial.X^sourceClockOrder event n∣irClockEMNumerator event n mu nu)
    (bounded : ∀mu nu,poleOrder (zeroClockEMFraction event n mu nu) 0≤4) :
    sourceUnitCoulombTensor u event n=((u.energy : ℂ)*(u.length : ℂ))⁻¹ • noetherTensorCoefficient event n := by
  have original := actual_ordered_em_return event n nonzero factors bounded
  have zero : ∀ᶠ eps : ℝ in nhdsWithin 0 ({0}ᶜ), sourceUnitZeroEMTensor u event eps n=
      ((u.generator : ℂ)^2/(sourceDensityUnit u : ℂ)) • zeroClockEMRead event eps n :=
    original.1.mono (fun eps h => zero_tensor_generated u event eps n h)
  let scalar := (u.length : ℂ)^2*(sourceUnitNoetherPairScale u)^2*((u.generator : ℂ)^2/(sourceDensityUnit u : ℂ))
  have limit := original.2.const_smul scalar
  have actual : Tendsto (fun eps : ℝ => (-((u.length : ℂ)*(eps : ℂ)^2)^2) •
      (sourceUnitNoetherPairScale u)^2 • sourceUnitZeroEMTensor u event eps n)
      (nhdsWithin 0 ({0}ᶜ)) (𝓝 (scalar • sourceOrderedEMCoefficient event n)) := by
    apply Tendsto.congr' _ limit
    filter_upwards [zero] with eps generated
    rw [generated,smul_smul,smul_smul,smul_smul]
    apply congrArg (fun c : ℂ => c • zeroClockEMRead event eps n)
    dsimp [scalar]
    ring
  rw [sourceUnitCoulombTensor,actual.limUnder_eq]
  dsimp only [scalar]
  rw [electron_tensor_scale,noetherTensorCoefficient,smul_smul]

theorem source_unit_coulomb_coordinate (u : SourceUnits) (event : DressedEvent) (n : PhysicalMomentum)
    (nonzero : irClockDeterminant event n≠0)
    (factors : ∀mu nu,Polynomial.X^sourceClockOrder event n∣irClockEMNumerator event n mu nu)
    (bounded : ∀mu nu,poleOrder (zeroClockEMFraction event n mu nu) 0≤4) :
    sourceUnitCoulomb u event n=directionalNoetherCoulombCoefficient event n/((u.energy*u.length : ℝ) : ℂ) := by
  rw [sourceUnitCoulomb,source_unit_actual_coulomb_generated u event n nonzero factors bounded,
    Matrix.smul_apply,smul_eq_mul,directionalNoetherCoulombCoefficient]
  push_cast
  ring

def sourceUnitZeroProbe (u : SourceUnits) (event : DressedEvent) (eps : ℝ) (n pd ps : PhysicalMomentum)
    (dL dR sL sR : CompositeLeg) : ℂ :=
  limUnder (nhdsWithin 0 (Ioi 0))
    (fun sigma : ℝ => sourceUnitFullProbe u event eps 0 sigma n pd ps dL dR sL sR)

def sourceUnitWholeCoulombCoefficient (u : SourceUnits) (event : DressedEvent) (n pd ps : PhysicalMomentum)
    (dL dR sL sR : CompositeLeg) : ℂ :=
  limUnder (nhdsWithin 0 ({0}ᶜ)) (fun eps : ℝ =>
    -((u.length : ℂ)*(eps : ℂ)^2)^2*sourceUnitZeroProbe u event eps n pd ps dL dR sL sR)

theorem source_unit_whole_coulomb_generated (u : SourceUnits) (event : DressedEvent) (n pd ps : PhysicalMomentum)
    (dL dR sL sR : CompositeLeg) (nonzero : irClockDeterminant event n≠0)
    (clock : ClockFinite event n pd ps dL dR sL sR)
    (bounded : poleOrder (zeroClockProbeFraction event n pd ps dL dR sL sR) 0≤4) :
    sourceUnitWholeCoulombCoefficient u event n pd ps dL dR sL sR=
      ((u.energy : ℂ)*(u.length : ℂ))⁻¹*sourceOrderedProbeCoefficient event n pd ps dL dR sL sR := by
  have original := actual_ordered_probe_return event n pd ps dL dR sL sR nonzero clock.2 bounded
  let factor : ℂ := ((u.energy : ℂ)*(u.length : ℂ)^3)⁻¹
  have zero : ∀ᶠ eps : ℝ in nhdsWithin 0 ({0}ᶜ),
      sourceUnitZeroProbe u event eps n pd ps dL dR sL sR=factor*zeroClockProbeRead event eps n pd ps dL dR sL sR := by
    filter_upwards [original.1] with eps returned
    have actual := returned.const_mul factor
    have new : Tendsto (fun sigma : ℝ => sourceUnitFullProbe u event eps 0 sigma n pd ps dL dR sL sR)
        (nhdsWithin 0 (Ioi 0)) (𝓝 (factor*zeroClockProbeRead event eps n pd ps dL dR sL sR)) := by
      simpa only [source_unit_full_probe_covariance,factor] using actual
    exact new.limUnder_eq
  let scalar : ℂ := (u.length : ℂ)^2*factor
  have limit := original.2.const_mul scalar
  have actual : Tendsto (fun eps : ℝ => -((u.length : ℂ)*(eps : ℂ)^2)^2*
      sourceUnitZeroProbe u event eps n pd ps dL dR sL sR)
      (nhdsWithin 0 ({0}ᶜ)) (𝓝 (scalar*sourceOrderedProbeCoefficient event n pd ps dL dR sL sR)) := by
    apply Tendsto.congr' _ limit
    filter_upwards [zero] with eps generated
    rw [generated]
    dsimp only [scalar]
    ring
  rw [sourceUnitWholeCoulombCoefficient,actual.limUnder_eq]
  apply congrArg (fun c : ℂ => c*sourceOrderedProbeCoefficient event n pd ps dL dR sL sR)
  have length_ne := Complex.ofReal_ne_zero.mpr u.length_positive.ne'
  have energy_ne := Complex.ofReal_ne_zero.mpr u.energy_positive.ne'
  dsimp only [scalar,factor]
  field_simp [length_ne,energy_ne]

/-- Both actual charge calibrations, the fifteen other EM components and all three nonpure pieces share the generated energy unit. -/
theorem source_unit_complete_energy_coefficient (u : SourceUnits) (event : DressedEvent) (n pd ps : PhysicalMomentum)
    (dL dR sL sR : CompositeLeg) (nonzero : irClockDeterminant event n≠0)
    (clock : ClockFinite event n pd ps dL dR sL sR)
    (tensor_orders : ∀mu nu,poleOrder (zeroClockEMFraction event n mu nu) 0≤4)
    (probe_order : poleOrder (zeroClockProbeFraction event n pd ps dL dR sL sR) 0≤4) :
    sourceUnitWholeCoulombCoefficient u event n pd ps dL dR sL sR/(4*(Real.pi : ℂ))=
      sourceInputCharge dR*sourceInputCharge sR*sourceUnitCoulomb u event n+
      (noetherChargeCalibration pd dL dR*sourceInputCharge sR+
        sourceInputCharge dR*noetherChargeCalibration ps sL sR+
        noetherChargeCalibration pd dL dR*noetherChargeCalibration ps sL sR)*sourceUnitCoulomb u event n+
      ((u.energy : ℂ)*(u.length : ℂ))⁻¹*
        (otherEMCoefficient event n pd ps dL dR sL sR/(4*(Real.pi : ℂ))+
          noetherNonPureCoefficient event n pd ps dL dR sL sR/(4*(Real.pi : ℂ))) := by
  rw [source_unit_whole_coulomb_generated u event n pd ps dL dR sL sR nonzero clock probe_order,
    source_unit_coulomb_coordinate u event n nonzero clock.1 tensor_orders]
  have original := actual_noether_coulomb_coefficient event n pd ps dL dR sL sR
  have scaled := congrArg (fun c : ℂ => ((u.energy : ℂ)*(u.length : ℂ))⁻¹*c) original
  push_cast
  linear_combination scaled

def sourceUnitSpectralFrequency (u : SourceUnits) (eps : ℝ) (a : ℂ) : ℂ :=
  (u.time : ℂ)*physicalFrequencyPole eps a

def sourceUnitPhysicalSpectralRoots (u : SourceUnits) (event : DressedEvent) (eps : ℝ) (n : PhysicalMomentum) : Multiset ℂ :=
  (emCommonSpectralRoots event eps n).map (sourceUnitSpectralFrequency u eps)

theorem source_unit_spectral_frequency_injective (u : SourceUnits) (eps : ℝ) (eps_ne : eps≠0) :
    Function.Injective (sourceUnitSpectralFrequency u eps) := by
  intro a b same
  apply source_em_physical_frequency_injective eps eps_ne
  exact mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr u.time_positive.ne') same

theorem source_unit_spectral_coverage (u : SourceUnits) (event : DressedEvent) (eps : ℝ) (n : PhysicalMomentum)
    (omega : ℂ) : omega∈sourceUnitPhysicalSpectralRoots u event eps n ↔
      ∃a : EMSourcePole event eps n, sourceUnitSpectralFrequency u eps a.val=omega := by
  rw [sourceUnitPhysicalSpectralRoots,Multiset.mem_map]
  exact ⟨fun ⟨a,root,same⟩ => ⟨⟨a,root⟩,same⟩,fun ⟨a,same⟩ => ⟨a.val,a.property,same⟩⟩

theorem source_unit_spectral_multiplicity (u : SourceUnits) (event : DressedEvent) (eps : ℝ) (n : PhysicalMomentum)
    (eps_ne : eps≠0) (a : ℂ) :
    (sourceUnitPhysicalSpectralRoots u event eps n).count (sourceUnitSpectralFrequency u eps a)=
      ∑c : EMChannel,poleOrder (zeroClockFrequencyEMFraction event eps n c.1 c.2) a := by
  classical
  rw [sourceUnitPhysicalSpectralRoots,Multiset.count_map_eq_count' _ _
    (source_unit_spectral_frequency_injective u eps eps_ne),source_em_complete_spectral_multiplicity]

theorem source_unit_spectral_real_iff (u : SourceUnits) (eps : ℝ) (eps_ne : eps≠0) (a : ℂ) :
    (sourceUnitSpectralFrequency u eps a).im=0 ↔ a.im=0 := by
  rw [sourceUnitSpectralFrequency,Complex.mul_im]
  simp only [Complex.ofReal_im,Complex.ofReal_re,zero_mul,add_zero,mul_eq_zero,u.time_positive.ne',false_or]
  exact source_em_physical_frequency_real_iff eps eps_ne a

def sourceUnitColumnScale (u : SourceUnits) : ℂ :=
  ((u.field : ℂ)*(u.generator : ℂ))/sourceUnitResponseFactor u

def sourceUnitFrequencyWeight (u : SourceUnits) (q r : ℕ) : ℂ :=
  (u.time : ℂ)^q/(u.time : ℂ)^r

def sourceUnitPoleRadius (u : SourceUnits) (eps : ℝ) : ℂ := (u.time : ℂ)*((eps^2 : ℝ) : ℂ)

def sourceUnitNormalizedSeries (u : SourceUnits) (eps : ℝ) (scale : ℂ) (q : ℕ) (S : PowerSeries ℂ) : PowerSeries ℂ :=
  PowerSeries.C (scale*(sourceUnitPoleRadius u eps)^q)*PowerSeries.rescale (sourceUnitPoleRadius u eps)⁻¹ S

private theorem unit_normalized_coefficient (u : SourceUnits) (eps : ℝ) (scale : ℂ) (q r : ℕ) (S : PowerSeries ℂ) :
    PowerSeries.coeff r (sourceUnitNormalizedSeries u eps scale q S)=
      scale*sourceUnitFrequencyWeight u q r*
        (((eps^2 : ℝ) : ℂ)^q*PowerSeries.coeff r S/((eps^2 : ℝ) : ℂ)^r) := by
  simp only [sourceUnitNormalizedSeries,sourceUnitPoleRadius,sourceUnitFrequencyWeight,
    PowerSeries.coeff_C_mul,PowerSeries.coeff_rescale,mul_pow,inv_pow,mul_inv_rev,div_eq_mul_inv]
  ring

/-- The complete old series is re-expressed in the new physical frequency, including every analytic coefficient. -/
def sourceUnitPoleClockSeries (u : SourceUnits) (event : DressedEvent) (eps : ℝ) (n : PhysicalMomentum) (a : ℂ) :
    Matrix (Fin 289) (Fin 289) (PowerSeries ℂ) :=
  fun i j => PowerSeries.C (sourceUnitResponseFactor u)*
    PowerSeries.rescale (sourceUnitPoleRadius u eps)⁻¹ (emCorrectedPoleSeries event eps n a i j)

def sourceUnitPoleClockCoefficient (u : SourceUnits) (event : DressedEvent) (eps : ℝ) (n : PhysicalMomentum)
    (a : ℂ) (r : ℕ) : Matrix (Fin 289) (Fin 289) ℂ :=
  fun i j => PowerSeries.coeff r (sourceUnitPoleClockSeries u event eps n a i j)

def sourceUnitPoleColumnSeries (u : SourceUnits) (event : DressedEvent) (eps : ℝ) (n : PhysicalMomentum)
    (nu : Fin 4) (a : ℂ) : Fin 289→PowerSeries ℂ :=
  fun i => sourceUnitNormalizedSeries u eps (sourceUnitColumnScale u)
    (emFullColumnPoleOrder event eps n nu a) (emNormalizedPoleColumnSeries event eps n nu a i)

def sourceUnitPoleColumnCoefficient (u : SourceUnits) (event : DressedEvent) (eps : ℝ) (n : PhysicalMomentum)
    (nu : Fin 4) (a : ℂ) (r : ℕ) : Fin 289→ℂ :=
  fun i => PowerSeries.coeff r (sourceUnitPoleColumnSeries u event eps n nu a i)

def sourceUnitPoleLeftSeries (u : SourceUnits) (event : DressedEvent) (eps : ℝ) (n : PhysicalMomentum)
    (mu : Fin 4) (a : ℂ) : Fin 289→PowerSeries ℂ :=
  fun i => sourceUnitNormalizedSeries u eps (sourceUnitColumnScale u)
    (emFullRowPoleOrder event eps n mu a) (emLeftPoleSeries event eps n mu a i)

def sourceUnitPoleLeftCoefficient (u : SourceUnits) (event : DressedEvent) (eps : ℝ) (n : PhysicalMomentum)
    (mu : Fin 4) (a : ℂ) (r : ℕ) : Fin 289→ℂ :=
  fun i => PowerSeries.coeff r (sourceUnitPoleLeftSeries u event eps n mu a i)

def sourceUnitPoleLeftClockSeries (u : SourceUnits) (event : DressedEvent) (eps : ℝ) (n : PhysicalMomentum)
    (mu : Fin 4) (a : ℂ) : Fin 289→PowerSeries ℂ :=
  fun i => sourceUnitNormalizedSeries u eps (sourceUnitResponseFactor u*sourceUnitColumnScale u)
    (emFullRowPoleOrder event eps n mu a) (emLeftClockDefectSeries event eps n mu a i)

def sourceUnitPoleLeftClockCoefficient (u : SourceUnits) (event : DressedEvent) (eps : ℝ) (n : PhysicalMomentum)
    (mu : Fin 4) (a : ℂ) (r : ℕ) : Fin 289→ℂ :=
  fun i => PowerSeries.coeff r (sourceUnitPoleLeftClockSeries u event eps n mu a i)

theorem source_unit_all_clock_pole_coefficients (u : SourceUnits) (event : DressedEvent) (eps : ℝ)
    (n : PhysicalMomentum) (a : ℂ) (r : ℕ) :
    sourceUnitPoleClockCoefficient u event eps n a r=(sourceUnitResponseFactor u/(u.time : ℂ)^r) •
      emPhysicalCorrectedPoleCoefficient event eps n a r := by
  funext i j
  simp only [sourceUnitPoleClockCoefficient,sourceUnitPoleClockSeries,sourceUnitPoleRadius,
    emPhysicalCorrectedPoleCoefficient,emCorrectedPoleCoefficient,PowerSeries.coeff_C_mul,
    PowerSeries.coeff_rescale,Matrix.smul_apply,smul_eq_mul,mul_pow,inv_pow,mul_inv_rev,div_eq_mul_inv]
  ring

theorem source_unit_all_column_pole_coefficients (u : SourceUnits) (event : DressedEvent) (eps : ℝ)
    (n : PhysicalMomentum) (nu : Fin 4) (a : ℂ) (r : ℕ) :
    sourceUnitPoleColumnCoefficient u event eps n nu a r=
      (sourceUnitColumnScale u*sourceUnitFrequencyWeight u (emFullColumnPoleOrder event eps n nu a) r) •
        emPhysicalNormalizedPoleColumnCoefficient event eps n nu a r := by
  funext i
  exact unit_normalized_coefficient u eps (sourceUnitColumnScale u)
    (emFullColumnPoleOrder event eps n nu a) r (emNormalizedPoleColumnSeries event eps n nu a i)

theorem source_unit_all_left_pole_coefficients (u : SourceUnits) (event : DressedEvent) (eps : ℝ)
    (n : PhysicalMomentum) (mu : Fin 4) (a : ℂ) (r : ℕ) :
    sourceUnitPoleLeftCoefficient u event eps n mu a r=
      (sourceUnitColumnScale u*sourceUnitFrequencyWeight u (emFullRowPoleOrder event eps n mu a) r) •
        emPhysicalLeftPoleCoefficient event eps n mu a r := by
  funext i
  unfold sourceUnitPoleLeftCoefficient sourceUnitPoleLeftSeries emPhysicalLeftPoleCoefficient
  exact unit_normalized_coefficient u eps (sourceUnitColumnScale u)
    (emFullRowPoleOrder event eps n mu a) r (emLeftPoleSeries event eps n mu a i)

theorem source_unit_all_left_clock_defects (u : SourceUnits) (event : DressedEvent) (eps : ℝ)
    (n : PhysicalMomentum) (mu : Fin 4) (a : ℂ) (r : ℕ) :
    sourceUnitPoleLeftClockCoefficient u event eps n mu a r=
      (sourceUnitResponseFactor u*sourceUnitColumnScale u*
        sourceUnitFrequencyWeight u (emFullRowPoleOrder event eps n mu a) r) •
          emPhysicalLeftClockDefectCoefficient event eps n mu a r := by
  funext i
  exact unit_normalized_coefficient u eps (sourceUnitResponseFactor u*sourceUnitColumnScale u)
    (emFullRowPoleOrder event eps n mu a) r (emLeftClockDefectSeries event eps n mu a i)

def sourceUnitFullResidue (u : SourceUnits) (event : DressedEvent) (eps : ℝ) (n : PhysicalMomentum)
    (nu : Fin 4) (a : ℂ) : Fin 289→ℂ :=
  sourceUnitPoleColumnCoefficient u event eps n nu a (emFullColumnPoleOrder event eps n nu a-1)

theorem source_unit_actual_full_residue (u : SourceUnits) (event : DressedEvent) (eps : ℝ) (n : PhysicalMomentum)
    (mu nu : Fin 4) (a : ℂ) (eps_ne : eps≠0)
    (root : a∈visibleRoots (zeroClockFrequencyEMFraction event eps n mu nu)) :
    sourceUnitFullResidue u event eps n nu a=(sourceUnitColumnScale u*(u.time : ℂ)) •
      emFullPhysicalResidue event eps n nu a := by
  have positive := source_em_full_pole_order_positive event eps n mu nu a root
  have power : (u.time : ℂ)^emFullColumnPoleOrder event eps n nu a=
      (u.time : ℂ)^(emFullColumnPoleOrder event eps n nu a-1)*(u.time : ℂ) := by
    rw [←pow_succ,Nat.sub_add_cancel (Nat.succ_le_iff.mpr positive)]
  rw [sourceUnitFullResidue,source_unit_all_column_pole_coefficients,
    source_em_physical_canonical_residue event eps n mu nu a eps_ne root,
    sourceUnitFrequencyWeight,power,mul_div_cancel_left₀ _
      (pow_ne_zero _ (Complex.ofReal_ne_zero.mpr u.time_positive.ne'))]

theorem source_unit_actual_analytic_column (u : SourceUnits) (event : DressedEvent) (eps : ℝ) (n : PhysicalMomentum)
    (mu nu : Fin 4) (a : ℂ) (eps_ne : eps≠0)
    (root : a∈visibleRoots (zeroClockFrequencyEMFraction event eps n mu nu)) :
    sourceUnitPoleColumnCoefficient u event eps n nu a (emFullColumnPoleOrder event eps n nu a)=
      sourceUnitColumnScale u • emPairedAnalyticColumn event eps n nu a := by
  rw [source_unit_all_column_pole_coefficients,sourceUnitFrequencyWeight,
    div_self (pow_ne_zero _ (Complex.ofReal_ne_zero.mpr u.time_positive.ne')),mul_one,
    source_em_physical_canonical_analytic_coefficient event eps n mu nu a eps_ne root]
  rfl

theorem source_unit_actual_clock_pole_jet (u : SourceUnits) (event : DressedEvent) (eps s : ℝ) (n : PhysicalMomentum)
    (eps_ne : eps≠0) (regular : (zeroClockClearing event eps n).eval (s : ℂ)≠0) :
    sourceUnitPoleClockCoefficient u event eps n (s : ℂ) 1=(sourceUnitResponseFactor u/(u.time : ℂ)) •
      correctedPhysicalClockJet event eps (sourceFrequency eps s) n := by
  rw [source_unit_all_clock_pole_coefficients,pow_one,actual_em_physical_pole_clock_first event eps s n eps_ne regular]

private theorem convolution_unit_scale (u : SourceUnits) (q k i j : ℕ) (sum : i+j=k) :
    (sourceUnitResponseFactor u/(u.time : ℂ)^i)*
      (sourceUnitColumnScale u*sourceUnitFrequencyWeight u q j)=
        sourceUnitResponseFactor u*sourceUnitColumnScale u*sourceUnitFrequencyWeight u q k := by
  unfold sourceUnitFrequencyWeight
  rw [←sum,pow_add]
  simp only [div_eq_mul_inv,mul_inv_rev]
  ring

private theorem paired_unit_scale (u : SourceUnits) (w : ℂ) :
    sourceUnitColumnScale u*w*(sourceUnitResponseFactor u*sourceUnitColumnScale u)=
      ((u.generator : ℂ)^2/(sourceDensityUnit u : ℂ))*w := by
  have field_ne := Complex.ofReal_ne_zero.mpr u.field_nonzero
  have density_ne : (sourceDensityUnit u : ℂ)≠0 :=
    Complex.ofReal_ne_zero.mpr (div_ne_zero (pow_ne_zero _ u.length_positive.ne') u.energy_positive.ne')
  unfold sourceUnitColumnScale sourceUnitResponseFactor
  field_simp [field_ne,density_ne]

def sourceUnitCompleteLeftDefect (u : SourceUnits) (event : DressedEvent) (eps : ℝ) (n : PhysicalMomentum)
    (mu : Fin 4) (a : ℂ) (r : ℕ) : Fin 289→ℂ :=
  sourceUnitPoleLeftClockCoefficient u event eps n mu a r+
    ∑p∈(Finset.HasAntidiagonal.antidiagonal r).erase (0,r),
      (sourceUnitPoleClockCoefficient u event eps n a p.1).transpose*ᵥsourceUnitPoleLeftCoefficient u event eps n mu a p.2

theorem source_unit_complete_left_defect (u : SourceUnits) (event : DressedEvent) (eps : ℝ) (n : PhysicalMomentum)
    (mu : Fin 4) (a : ℂ) (r : ℕ) :
    sourceUnitCompleteLeftDefect u event eps n mu a r=
      (sourceUnitResponseFactor u*sourceUnitColumnScale u*
        sourceUnitFrequencyWeight u (emFullRowPoleOrder event eps n mu a) r) • emCompleteLeftDefect event eps n mu a r := by
  have term (p : ℕ×ℕ) (member : p∈(Finset.HasAntidiagonal.antidiagonal r).erase (0,r)) :
      (sourceUnitPoleClockCoefficient u event eps n a p.1).transpose*ᵥsourceUnitPoleLeftCoefficient u event eps n mu a p.2=
        (sourceUnitResponseFactor u*sourceUnitColumnScale u*sourceUnitFrequencyWeight u (emFullRowPoleOrder event eps n mu a) r) •
          ((emPhysicalCorrectedPoleCoefficient event eps n a p.1).transpose*ᵥemPhysicalLeftPoleCoefficient event eps n mu a p.2) := by
    have sum : p.1+p.2=r := Finset.HasAntidiagonal.mem_antidiagonal.mp (Finset.mem_of_mem_erase member)
    rw [source_unit_all_clock_pole_coefficients,source_unit_all_left_pole_coefficients,Matrix.transpose_smul,
      Matrix.smul_mulVec,Matrix.mulVec_smul,smul_smul,convolution_unit_scale u _ r p.1 p.2 sum]
  rw [sourceUnitCompleteLeftDefect,source_unit_all_left_clock_defects,emCompleteLeftDefect,emLeftFrequencyChain,smul_add,Finset.smul_sum]
  congr 1
  exact Finset.sum_congr rfl term

def sourceUnitPairedClockEnergy (u : SourceUnits) (event : DressedEvent) (eps s : ℝ) (n : PhysicalMomentum)
    (mu nu : Fin 4) (r : ℕ) : ℂ :=
  dotProduct (sourceUnitPoleLeftCoefficient u event eps n mu (s : ℂ) r)
    (sourceUnitPoleClockCoefficient u event eps n (s : ℂ) 1*ᵥsourceUnitFullResidue u event eps n nu (s : ℂ))

def sourceUnitPairedHigherEnergy (u : SourceUnits) (event : DressedEvent) (eps s : ℝ) (n : PhysicalMomentum)
    (mu nu : Fin 4) (r : ℕ) : ℂ :=
  dotProduct (sourceUnitPoleLeftCoefficient u event eps n mu (s : ℂ) r)
    (∑k∈Finset.range (emFullColumnPoleOrder event eps n nu (s : ℂ)-1),
      sourceUnitPoleClockCoefficient u event eps n (s : ℂ) (k+2)*ᵥsourceUnitPoleColumnCoefficient u event eps n nu (s : ℂ)
        (emFullColumnPoleOrder event eps n nu (s : ℂ)-(k+2)))

def sourceUnitPairedInput (u : SourceUnits) (event : DressedEvent) (eps s : ℝ) (n : PhysicalMomentum)
    (mu nu : Fin 4) (r : ℕ) : ℂ :=
  dotProduct (sourceUnitPoleLeftCoefficient u event eps n mu (s : ℂ) r) (fun i => sourceUnitEMInsertion u i nu)

def sourceUnitPairedAnalyticDebt (u : SourceUnits) (event : DressedEvent) (eps s : ℝ) (n : PhysicalMomentum)
    (mu nu : Fin 4) (r : ℕ) : ℂ :=
  dotProduct (sourceUnitCompleteLeftDefect u event eps n mu (s : ℂ) r)
    (sourceUnitPoleColumnCoefficient u event eps n nu (s : ℂ) (emFullColumnPoleOrder event eps n nu (s : ℂ)))

def sourceUnitEnergyFactor (u : SourceUnits) (event : DressedEvent) (eps s : ℝ) (n : PhysicalMomentum) (mu : Fin 4) (r : ℕ) : ℂ :=
  ((u.generator : ℂ)^2/(sourceDensityUnit u : ℂ))*sourceUnitFrequencyWeight u (emFullRowPoleOrder event eps n mu (s : ℂ)) r

theorem source_unit_paired_clock_energy (u : SourceUnits) (event : DressedEvent) (eps s : ℝ) (n : PhysicalMomentum)
    (mu nu : Fin 4) (r : ℕ) (eps_ne : eps≠0) (regular : (zeroClockClearing event eps n).eval (s : ℂ)≠0)
    (root : (s : ℂ)∈visibleRoots (zeroClockFrequencyEMFraction event eps n mu nu)) :
    sourceUnitPairedClockEnergy u event eps s n mu nu r=sourceUnitEnergyFactor u event eps s n mu r*
      emVisiblePairedClockEnergy event eps s n mu nu r := by
  rw [sourceUnitPairedClockEnergy,source_unit_all_left_pole_coefficients,
    source_unit_actual_clock_pole_jet u event eps s n eps_ne regular,
    source_unit_actual_full_residue u event eps n mu nu (s : ℂ) eps_ne root]
  unfold emVisiblePairedClockEnergy sourceUnitEnergyFactor
  simp only [Matrix.smul_mulVec,Matrix.mulVec_smul,dotProduct_smul,smul_dotProduct,smul_eq_mul,←mul_assoc]
  apply congrArg (fun c : ℂ => c*dotProduct (emPhysicalLeftPoleCoefficient event eps n mu (s : ℂ) r)
    (correctedPhysicalClockJet event eps (sourceFrequency eps s) n*ᵥemFullPhysicalResidue event eps n nu (s : ℂ)))
  have time_ne := Complex.ofReal_ne_zero.mpr u.time_positive.ne'
  have scalar : sourceUnitColumnScale u*(u.time : ℂ)*(sourceUnitResponseFactor u/(u.time : ℂ))*sourceUnitColumnScale u*
      sourceUnitFrequencyWeight u (emFullRowPoleOrder event eps n mu (s : ℂ)) r=
        sourceUnitColumnScale u*sourceUnitFrequencyWeight u (emFullRowPoleOrder event eps n mu (s : ℂ)) r*
          (sourceUnitResponseFactor u*sourceUnitColumnScale u) := by field_simp [time_ne]
  exact scalar.trans (paired_unit_scale u _)

theorem source_unit_paired_higher_energy (u : SourceUnits) (event : DressedEvent) (eps s : ℝ) (n : PhysicalMomentum)
    (mu nu : Fin 4) (r : ℕ) :
    sourceUnitPairedHigherEnergy u event eps s n mu nu r=sourceUnitEnergyFactor u event eps s n mu r*
      emVisiblePairedHigherEnergy event eps s n mu nu r := by
  have term (k : ℕ) (member : k∈Finset.range (emFullColumnPoleOrder event eps n nu (s : ℂ)-1)) :
      sourceUnitPoleClockCoefficient u event eps n (s : ℂ) (k+2)*ᵥ
        sourceUnitPoleColumnCoefficient u event eps n nu (s : ℂ) (emFullColumnPoleOrder event eps n nu (s : ℂ)-(k+2))=
      (sourceUnitResponseFactor u*sourceUnitColumnScale u) •
        (emPhysicalCorrectedPoleCoefficient event eps n (s : ℂ) (k+2)*ᵥ
          emPhysicalNormalizedPoleColumnCoefficient event eps n nu (s : ℂ) (emFullColumnPoleOrder event eps n nu (s : ℂ)-(k+2))) := by
    have lower : k+2≤emFullColumnPoleOrder event eps n nu (s : ℂ) := by
      have h := Finset.mem_range.mp member
      omega
    rw [source_unit_all_clock_pole_coefficients,source_unit_all_column_pole_coefficients,
      Matrix.smul_mulVec,Matrix.mulVec_smul,smul_smul,
      convolution_unit_scale u _ _ (k+2) _ (Nat.add_sub_of_le lower),sourceUnitFrequencyWeight,
      div_self (pow_ne_zero _ (Complex.ofReal_ne_zero.mpr u.time_positive.ne')),mul_one]
  have summed := Finset.sum_congr rfl term
  rw [←Finset.smul_sum] at summed
  rw [sourceUnitPairedHigherEnergy,summed,source_unit_all_left_pole_coefficients]
  unfold emVisiblePairedHigherEnergy sourceUnitEnergyFactor
  simp only [dotProduct_smul,smul_dotProduct,smul_eq_mul,←mul_assoc]
  apply congrArg (fun c : ℂ => c*dotProduct (emPhysicalLeftPoleCoefficient event eps n mu (s : ℂ) r)
    (∑k∈Finset.range (emFullColumnPoleOrder event eps n nu (s : ℂ)-1),
      emPhysicalCorrectedPoleCoefficient event eps n (s : ℂ) (k+2)*ᵥ
        emPhysicalNormalizedPoleColumnCoefficient event eps n nu (s : ℂ) (emFullColumnPoleOrder event eps n nu (s : ℂ)-(k+2))))
  calc
    _=sourceUnitColumnScale u*sourceUnitFrequencyWeight u (emFullRowPoleOrder event eps n mu (s : ℂ)) r*
        (sourceUnitResponseFactor u*sourceUnitColumnScale u) := by ring
    _=_ := paired_unit_scale u _

theorem source_unit_paired_input (u : SourceUnits) (event : DressedEvent) (eps s : ℝ) (n : PhysicalMomentum)
    (mu nu : Fin 4) (r : ℕ) : sourceUnitPairedInput u event eps s n mu nu r=
      sourceUnitEnergyFactor u event eps s n mu r*emVisiblePairedSourceInput event eps s n mu nu r := by
  rw [sourceUnitPairedInput,source_unit_all_left_pole_coefficients]
  have force : (fun i => sourceUnitEMInsertion u i nu)=
      (sourceUnitResponseFactor u*sourceUnitColumnScale u) • (fun i => emInsertion i nu) := by
    have factor := source_unit_response_factor_nonzero u
    funext i
    simp only [sourceUnitEMInsertion,sourceUnitColumnScale,Matrix.smul_apply,Pi.smul_apply,smul_eq_mul]
    field_simp [factor]
  rw [force]
  unfold sourceUnitEnergyFactor emVisiblePairedSourceInput
  simp only [dotProduct_smul,smul_dotProduct,smul_eq_mul,←mul_assoc]
  apply congrArg (fun c : ℂ => c*dotProduct (emPhysicalLeftPoleCoefficient event eps n mu (s : ℂ) r) (fun i => emInsertion i nu))
  calc
    _=sourceUnitColumnScale u*sourceUnitFrequencyWeight u (emFullRowPoleOrder event eps n mu (s : ℂ)) r*
        (sourceUnitResponseFactor u*sourceUnitColumnScale u) := by ring
    _=_ := paired_unit_scale u _

theorem source_unit_paired_analytic_debt (u : SourceUnits) (event : DressedEvent) (eps s : ℝ) (n : PhysicalMomentum)
    (mu nu : Fin 4) (r : ℕ) (eps_ne : eps≠0)
    (root : (s : ℂ)∈visibleRoots (zeroClockFrequencyEMFraction event eps n mu nu)) :
    sourceUnitPairedAnalyticDebt u event eps s n mu nu r=sourceUnitEnergyFactor u event eps s n mu r*
      emVisiblePairedAnalyticDebt event eps s n mu nu r := by
  rw [sourceUnitPairedAnalyticDebt,source_unit_complete_left_defect,
    source_unit_actual_analytic_column u event eps n mu nu (s : ℂ) eps_ne root]
  unfold sourceUnitEnergyFactor emVisiblePairedAnalyticDebt
  simp only [dotProduct_smul,smul_dotProduct,smul_eq_mul,←mul_assoc]
  apply congrArg (fun c : ℂ => c*dotProduct (emCompleteLeftDefect event eps n mu (s : ℂ) r) (emPairedAnalyticColumn event eps n nu (s : ℂ)))
  calc
    _=sourceUnitColumnScale u*sourceUnitFrequencyWeight u (emFullRowPoleOrder event eps n mu (s : ℂ)) r*
        (sourceUnitResponseFactor u*sourceUnitColumnScale u) := by ring
    _=_ := paired_unit_scale u _

private theorem right_chain_read (u : SourceUnits) (event : DressedEvent) (eps : ℝ) (n : PhysicalMomentum)
    (nu : Fin 4) (a : ℂ) (k : ℕ) (i : Fin 289) :
    (∑j,∑p∈Finset.HasAntidiagonal.antidiagonal k,
      sourceUnitPoleClockCoefficient u event eps n a p.1 i j*sourceUnitPoleColumnCoefficient u event eps n nu a p.2 j)=
      (sourceUnitResponseFactor u*sourceUnitColumnScale u*sourceUnitFrequencyWeight u (emFullColumnPoleOrder event eps n nu a) k)*
        (∑j,∑p∈Finset.HasAntidiagonal.antidiagonal k,
          emPhysicalCorrectedPoleCoefficient event eps n a p.1 i j*emPhysicalNormalizedPoleColumnCoefficient event eps n nu a p.2 j) := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p member
  have sum := Finset.HasAntidiagonal.mem_antidiagonal.mp member
  have scalar := convolution_unit_scale u (emFullColumnPoleOrder event eps n nu a) k p.1 p.2 sum
  simp only [source_unit_all_clock_pole_coefficients,source_unit_all_column_pole_coefficients,
    Matrix.smul_apply,Pi.smul_apply,smul_eq_mul]
  linear_combination scalar*emPhysicalCorrectedPoleCoefficient event eps n a p.1 i j*
    emPhysicalNormalizedPoleColumnCoefficient event eps n nu a p.2 j

theorem source_unit_all_right_chains (u : SourceUnits) (event : DressedEvent) (eps : ℝ) (n : PhysicalMomentum)
    (mu nu : Fin 4) (a : ℂ) (eps_ne : eps≠0) (balanced : PencilClockBalanced event eps n)
    (finite : EMColumnsClockFinite event eps n) (regular : (zeroClockClearing event eps n).eval a≠0)
    (root : a∈visibleRoots (zeroClockFrequencyEMFraction event eps n mu nu)) :
    (∀k : ℕ,k<emFullColumnPoleOrder event eps n nu a → ∀i : Fin 289,
      (∑j,∑p∈Finset.HasAntidiagonal.antidiagonal k,
        sourceUnitPoleClockCoefficient u event eps n a p.1 i j*sourceUnitPoleColumnCoefficient u event eps n nu a p.2 j)=0) ∧
    (∀i : Fin 289,(∑j,∑p∈Finset.HasAntidiagonal.antidiagonal (emFullColumnPoleOrder event eps n nu a),
      sourceUnitPoleClockCoefficient u event eps n a p.1 i j*sourceUnitPoleColumnCoefficient u event eps n nu a p.2 j)=sourceUnitEMInsertion u i nu) := by
  constructor
  · intro k lower i
    rw [right_chain_read,actual_em_physical_lower_pole_chain event eps n mu nu a balanced finite regular root k lower i,mul_zero]
  · intro i
    rw [right_chain_read,actual_em_physical_full_pole_balance event eps n mu nu a eps_ne balanced finite regular root i,
      sourceUnitFrequencyWeight,div_self (pow_ne_zero _ (Complex.ofReal_ne_zero.mpr u.time_positive.ne')),mul_one]
    simp only [sourceUnitColumnScale,sourceUnitEMInsertion,Matrix.smul_apply,smul_eq_mul]
    field_simp [source_unit_response_factor_nonzero u]

theorem source_unit_energy_factor_nonzero (u : SourceUnits) (event : DressedEvent) (eps s : ℝ)
    (n : PhysicalMomentum) (mu : Fin 4) (r : ℕ) : sourceUnitEnergyFactor u event eps s n mu r≠0 := by
  have density_ne : (sourceDensityUnit u : ℂ)≠0 :=
    Complex.ofReal_ne_zero.mpr (div_ne_zero (pow_ne_zero _ u.length_positive.ne') u.energy_positive.ne')
  have time_ne := Complex.ofReal_ne_zero.mpr u.time_positive.ne'
  exact mul_ne_zero (div_ne_zero (pow_ne_zero _ (Complex.ofReal_ne_zero.mpr u.generator_nonzero)) density_ne)
    (div_ne_zero (pow_ne_zero _ time_ne) (pow_ne_zero _ time_ne))

def sourceUnitClockGraphPrice (u : SourceUnits) (event : DressedEvent) (eps s : ℝ) (n : PhysicalMomentum)
    (mu nu : Fin 4) (r : ℕ) : ℝ :=
  ‖sourceUnitPairedHigherEnergy u event eps s n mu nu r‖+‖sourceUnitPairedAnalyticDebt u event eps s n mu nu r‖

theorem source_unit_complete_energy_and_price (u : SourceUnits) (event : DressedEvent) (eps s : ℝ)
    (n : PhysicalMomentum) (mu nu : Fin 4) (eps_ne : eps≠0) (balanced : PencilClockBalanced event eps n)
    (finite : EMColumnsClockFinite event eps n) (regular : (zeroClockClearing event eps n).eval (s : ℂ)≠0)
    (root : (s : ℂ)∈visibleRoots (zeroClockFrequencyEMFraction event eps n mu nu)) :
    let r := emRealSpectralIndex event eps s n mu nu eps_ne root
    sourceUnitPairedClockEnergy u event eps s n mu nu r+sourceUnitPairedHigherEnergy u event eps s n mu nu r-
      sourceUnitPairedAnalyticDebt u event eps s n mu nu r=sourceUnitPairedInput u event eps s n mu nu r ∧
    sourceUnitPairedInput u event eps s n mu nu r≠0 ∧
    sourceUnitPairedClockEnergy u event eps s n mu nu r/sourceUnitPairedInput u event eps s n mu nu r+
      sourceUnitPairedHigherEnergy u event eps s n mu nu r/sourceUnitPairedInput u event eps s n mu nu r-
        sourceUnitPairedAnalyticDebt u event eps s n mu nu r/sourceUnitPairedInput u event eps s n mu nu r=1 ∧
    ‖sourceUnitPairedInput u event eps s n mu nu r‖-sourceUnitClockGraphPrice u event eps s n mu nu r≤
      ‖sourceUnitPairedClockEnergy u event eps s n mu nu r‖ := by
  dsimp only
  let r := emRealSpectralIndex event eps s n mu nu eps_ne root
  have old := sourceEMRealEnergy event eps s n mu nu eps_ne balanced finite regular root
  have scalar_ne := source_unit_energy_factor_nonzero u event eps s n mu r
  have input_ne : sourceUnitPairedInput u event eps s n mu nu r≠0 := by
    rw [source_unit_paired_input]
    exact mul_ne_zero scalar_ne old.complete_nonzero.2
  have balance : sourceUnitPairedClockEnergy u event eps s n mu nu r+sourceUnitPairedHigherEnergy u event eps s n mu nu r-
      sourceUnitPairedAnalyticDebt u event eps s n mu nu r=sourceUnitPairedInput u event eps s n mu nu r := by
    rw [source_unit_paired_clock_energy u event eps s n mu nu r eps_ne regular root,
      source_unit_paired_higher_energy,source_unit_paired_analytic_debt u event eps s n mu nu r eps_ne root,
      source_unit_paired_input,←mul_add,←mul_sub,old.complete_nonzero.1]
  refine ⟨balance,input_ne,?_,?_⟩
  · rw [←add_div,←sub_div,balance,div_self input_ne]
  · rw [sourceUnitClockGraphPrice,source_unit_paired_input,source_unit_paired_higher_energy,
      source_unit_paired_analytic_debt u event eps s n mu nu r eps_ne root,
      source_unit_paired_clock_energy u event eps s n mu nu r eps_ne regular root]
    simp only [norm_mul]
    have price := mul_le_mul_of_nonneg_left old.graph_bound (norm_nonneg (sourceUnitEnergyFactor u event eps s n mu r))
    simpa only [emVisibleClockGraphPrice,mul_sub,mul_add] using price

theorem source_unit_price_chart_iff (u : SourceUnits) (event : DressedEvent) (eps s : ℝ)
    (n : PhysicalMomentum) (mu nu : Fin 4) (r : ℕ) (eps_ne : eps≠0)
    (root : (s : ℂ)∈visibleRoots (zeroClockFrequencyEMFraction event eps n mu nu)) :
    sourceUnitClockGraphPrice u event eps s n mu nu r<‖sourceUnitPairedInput u event eps s n mu nu r‖ ↔
      emVisibleClockGraphPrice event eps s n mu nu r<‖emVisiblePairedSourceInput event eps s n mu nu r‖ := by
  have positive : 0<‖sourceUnitEnergyFactor u event eps s n mu r‖ :=
    norm_pos_iff.mpr (source_unit_energy_factor_nonzero u event eps s n mu r)
  rw [sourceUnitClockGraphPrice,source_unit_paired_higher_energy,
    source_unit_paired_analytic_debt u event eps s n mu nu r eps_ne root,source_unit_paired_input]
  simp only [norm_mul,←mul_add]
  exact mul_lt_mul_iff_right₀ positive

def sourceUnitPrincipalRead (u : SourceUnits) (eps : ℝ) (R : RatFunc ℂ) (a : ℂ) (omega : ℝ) : ℂ :=
  ((u.generator : ℂ)^2/(sourceDensityUnit u : ℂ))*
    ((∑k∈Finset.range (poleOrder R a),clockPrincipalCoefficient R a (eps^2 : ℂ) k*
      ((omega : ℂ)-physicalFrequencyPole eps a)^k/((omega : ℂ)-physicalFrequencyPole eps a)^poleOrder R a)+
      (analyticNumerator R a).eval ((omega/eps^2 : ℝ) : ℂ)/(rootRemainder R a).eval ((omega/eps^2 : ℝ) : ℂ))

/-- The same source root and observer fibre return the entire actual principal and analytic signal in the new unit chart. -/
theorem source_unit_actual_principal_read (u : SourceUnits) (event : DressedEvent) (eps : ℝ)
    (n : PhysicalMomentum) (eps_ne : eps≠0) (tensor : EMTensorClockFinite event eps n)
    (balanced : PencilClockBalanced event eps n) (finite : EMColumnsClockFinite event eps n)
    (a : EMSourcePole event eps n) (c : EMSourceVisibleChannel event eps n a) (omega : ℝ)
    (regular : (zeroClockFrequencyDenominator event eps n).eval ((omega/eps^2 : ℝ) : ℂ)≠0)
    (away : (omega : ℂ)≠physicalFrequencyPole eps a.val)
    (tail : (rootRemainder (zeroClockFrequencyEMFraction event eps n c.val.1 c.val.2) a.val).eval
      ((omega/eps^2 : ℝ) : ℂ)≠0) :
    Tendsto (fun sigma : ℝ => sourceUnitFullEMTensor u event eps (omega/eps^2) sigma n c.val.1 c.val.2)
      (nhdsWithin 0 (Ioi 0))
      (𝓝 (sourceUnitPrincipalRead u eps (zeroClockFrequencyEMFraction event eps n c.val.1 c.val.2) a.val omega)) := by
  let original := sourceEMActualSpectralObservation event eps n eps_ne tensor balanced finite a c
  have returned := (original.actual_principal_return omega regular away tail).const_mul
    ((u.generator : ℂ)^2/(sourceDensityUnit u : ℂ))
  simpa only [source_unit_all_sixteen_tensor,Matrix.smul_apply,smul_eq_mul,sourceUnitPrincipalRead] using returned

def sourceSpectralBranchRate (event : DressedEvent) (eps : ℝ) (n : PhysicalMomentum) (a : EMSourcePole event eps n) : ℝ :=
  ‖physicalFrequencyPole eps a.val‖/‖(eps^2 : ℝ) • n‖

def sourceUnitSpectralBranchRate (u : SourceUnits) (event : DressedEvent) (eps : ℝ) (n : PhysicalMomentum)
    (a : EMSourcePole event eps n) : ℝ :=
  ‖sourceUnitSpectralFrequency u eps a.val‖/‖u.length • ((eps^2 : ℝ) • n)‖

/-- The rate is read from the generated frequency and the same actual spatial momentum, including corrected branches. -/
theorem source_unit_spectral_branch_rate (u : SourceUnits) (event : DressedEvent) (eps : ℝ) (n : PhysicalMomentum)
    (a : EMSourcePole event eps n) :
    sourceUnitSpectralBranchRate u event eps n a=(u.time/u.length)*sourceSpectralBranchRate event eps n a := by
  rw [sourceUnitSpectralBranchRate,sourceUnitSpectralFrequency,norm_mul,Complex.norm_real,
    Real.norm_eq_abs,norm_smul,Real.norm_eq_abs,abs_of_pos u.time_positive,abs_of_pos u.length_positive,
    sourceSpectralBranchRate]
  ring

theorem source_unit_generated_strength_invariant (u : SourceUnits) (event : DressedEvent) (eps : ℝ)
    (n : PhysicalMomentum) (a : EMSourcePole event eps n)
    (nonzero : irClockDeterminant event n≠0)
    (factors : ∀mu nu,Polynomial.X^sourceClockOrder event n∣irClockEMNumerator event n mu nu)
    (bounded : ∀mu nu,poleOrder (zeroClockEMFraction event n mu nu) 0≤4) :
    sourceUnitCoulomb u event n/
      ((sourceUnitActionMomentum u : ℂ)*(sourceUnitSpectralBranchRate u event eps n a : ℂ))=
        directionalNoetherCoulombCoefficient event n/
          ((Stage10.ActionNormalization.phaseMomentum : ℂ)*(sourceSpectralBranchRate event eps n a : ℂ)) := by
  rw [source_unit_coulomb_coordinate u event n nonzero factors bounded,source_unit_spectral_branch_rate]
  unfold sourceUnitActionMomentum
  push_cast
  have energy_ne := Complex.ofReal_ne_zero.mpr u.energy_positive.ne'
  have length_ne := Complex.ofReal_ne_zero.mpr u.length_positive.ne'
  have time_ne := Complex.ofReal_ne_zero.mpr u.time_positive.ne'
  field_simp [energy_ne,length_ne,time_ne]

inductive SourceUnitOrderedReturn (u : SourceUnits) (event : DressedEvent) (n pd ps : PhysicalMomentum)
    (dL dR sL sR : CompositeLeg) : Type
  | singular (original : OrderedStaticReturn event n pd ps dL dR sL sR) (zero : irClockDeterminant event n=0)
  | clock (original : OrderedStaticReturn event n pd ps dL dR sL sR) (failed : ¬ClockFinite event n pd ps dL dR sL sR)
  | spatial (original : OrderedStaticReturn event n pd ps dL dR sL sR)
      (higher : (∃mu nu,4<poleOrder (zeroClockEMFraction event n mu nu) 0) ∨
        4<poleOrder (zeroClockProbeFraction event n pd ps dL dR sL sR) 0)
  | realized (original : OrderedStaticReturn event n pd ps dL dR sL sR)
      (tensor : sourceUnitCoulombTensor u event n=((u.energy : ℂ)*(u.length : ℂ))⁻¹ • noetherTensorCoefficient event n)
      (whole : sourceUnitWholeCoulombCoefficient u event n pd ps dL dR sL sR=
        ((u.energy : ℂ)*(u.length : ℂ))⁻¹*sourceOrderedProbeCoefficient event n pd ps dL dR sL sR)
      (strength : ∀eps : ℝ,∀a : EMSourcePole event eps n,
        sourceUnitCoulomb u event n/((sourceUnitActionMomentum u : ℂ)*(sourceUnitSpectralBranchRate u event eps n a : ℂ))=
          directionalNoetherCoulombCoefficient event n/
            ((Stage10.ActionNormalization.phaseMomentum : ℂ)*(sourceSpectralBranchRate event eps n a : ℂ)))

/-- Finiteness, all failures and the entire coefficient are generated from the same source disposition. -/
def sourceUnitOrderedReturn (u : SourceUnits) (event : DressedEvent) (n pd ps : PhysicalMomentum)
    (dL dR sL sR : CompositeLeg) : SourceUnitOrderedReturn u event n pd ps dL dR sL sR := by
  let original := sourceOrderedStaticReturn event n pd ps dL dR sL sR
  cases original with
  | singular zero => exact .singular (.singular zero) zero
  | clockPrincipal nonzero failed pole => exact .clock (.clockPrincipal nonzero failed pole) failed
  | higherSpatial nonzero clock higher => exact .spatial (.higherSpatial nonzero clock higher) higher
  | finite nonzero clock tensor_orders probe_order tensor_return probe_return =>
      exact .realized (.finite nonzero clock tensor_orders probe_order tensor_return probe_return)
        (source_unit_actual_coulomb_generated u event n nonzero clock.1 tensor_orders)
        (source_unit_whole_coulomb_generated u event n pd ps dL dR sL sR nonzero clock probe_order)
        (fun eps a => source_unit_generated_strength_invariant u event eps n a nonzero clock.1 tensor_orders)


end LowEnergy.GaussComposite.ActualDressedEMWholeUnitCovariance
