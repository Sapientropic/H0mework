import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.PhysicalN3PoleRawEMObserver
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedReaderContactBasis
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedEMSourceMaxwellField

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.PhysicalN3SourceEnergy
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open GaussCoreHilbert GaussCoreDifferential CanonicalGradedSpatialSource
open ActualCompositeFieldCurrent ActualDressedFullCoulomb ActualElectronWholeChargeSoft
open ActualElectronWholeNoetherObserver GaussComposite.SourceGraph
open PreparationVacuumMixedFieldReturn PreparationVacuumNoetherChart
open PreparationVacuumFullFieldRiesz PreparationVacuumSourcePreparedResponse
open PreparationVacuumActionFieldLift PreparationVacuumPhysicalFeedback
open PreparationVacuumPhysicalCharacteristic PreparationVacuumPhysicalPoleSheet
open ActualDressedConstraintRead ActualEMCarrierOwn ActualEMCurrentSplit
open PhysicalEMGaugeRealization PhysicalEMVoltage
open ActualDressedCorrectedGreen ActualDressedEMPhysicalRead ActualDressedFrequencyHalf
open ActualDressedEMNativeMomentum
open SourceFamilyHilbert SourceFamilyOperator Filter
open scoped Topology InnerProductSpace BigOperators Matrix
attribute [local irreducible] physicalN3PoleState actualNoetherBackground
  prepared sourceProfile noetherReader noetherReaderContact physicalN3RawEMReader
  physicalN3PoleRawEMPoleObserver

private theorem current_unit_normalization (h a r : ℂ) (nonzero : h≠0)
    (eqn : -h⁻¹*a = -r) : a = h*r := by
  have positive : h⁻¹*a = r := by
    apply neg_injective
    simpa only [neg_mul] using eqn
  have multiplied := congrArg (fun x : ℂ => h*x) positive
  simpa only [← mul_assoc, mul_inv_cancel₀ nonzero, one_mul] using multiplied

/-- The original complete Noether operator consumer on the generated pole state. -/
def physicalN3PoleNoetherObserver (event : DressedEvent) (leg : CompositeLeg)
    (poles : N3SourceEnergyPoleSection event.momentum leg) : (H→L[ℂ]H)→L[ℂ]ℂ :=
  -(((innerSL ℂ (physicalN3PoleState event.momentum leg poles)).comp
      ((ContinuousLinearMap.apply ℂ ElectronHistory
        (physicalN3PoleState event.momentum leg poles)).comp actualHistoryReader)) -
    ((innerSL ℂ (actualNoetherBackground event)).comp
      ((ContinuousLinearMap.apply ℂ ElectronHistory (actualNoetherBackground event)).comp
        actualHistoryReader)))

attribute [local irreducible] physicalN3PoleNoetherObserver

theorem physical_n3_pole_noether_observer_value (event : DressedEvent) (leg : CompositeLeg)
    (poles : N3SourceEnergyPoleSection event.momentum leg) (A : H→L[ℂ]H) :
    physicalN3PoleNoetherObserver event leg poles A =
      -inner ℂ (physicalN3PoleState event.momentum leg poles)
        (GaussUnitaryHistory.reader A (physicalN3PoleState event.momentum leg poles)) +
      inner ℂ (actualNoetherBackground event)
        (GaussUnitaryHistory.reader A (actualNoetherBackground event)) := by
  have same : actualHistoryReader A = GaussUnitaryHistory.reader A := rfl
  simp only [physicalN3PoleNoetherObserver, neg_apply, sub_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply, innerSL_apply_apply, same]
  ring

/-- Every original field slot is emitted by the same charged external state and background. -/
def physicalN3PoleCurrent (event : DressedEvent) (leg : CompositeLeg)
    (poles : N3SourceEnergyPoleSection event.momentum leg) : Fin 289→ℂ :=
  fun i => physicalN3PoleNoetherObserver event leg poles
    (noetherReader (fieldUnit i) event.momentum event.frame 0)

def physicalN3PoleCurrentContact (event : DressedEvent) (leg : CompositeLeg)
    (poles : N3SourceEnergyPoleSection event.momentum leg) :
    Matrix (Fin 289) (Fin 289) ℂ :=
  fun i j => physicalN3PoleNoetherObserver event leg poles
    (noetherReaderContact (fieldUnit i) (fieldUnit j) event.momentum event.frame)

def physicalN3PoleCurrentPrice (event : DressedEvent) (i : Fin 289) : ℝ :=
  finitePrice event.frame (fun a b => noetherForm (fieldUnit i) event.momentum
    (frameTest event.frame a) (frameTest event.frame b) 0)

private theorem pole_current_reader_bound {I E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] (u : Ultrafilter I) (A : E→L[ℂ]E) :
    ‖SourceFamilyOperator.lift u (SourceFamilyOperator.constant A)‖ ≤ ‖A‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg A)
  intro x
  exact SourceBoundaryGram.lift_bound_explicit u (SourceFamilyOperator.constant A) ‖A‖
    (norm_nonneg A) (fun _ y => A.le_opNorm y) x

private theorem pole_current_native_bound (A : H→L[ℂ]H) :
    ‖GaussUnitaryHistory.reader A‖ ≤ ‖A‖ := by
  unfold GaussUnitaryHistory.reader
  exact pole_current_reader_bound (E := H) GaussUnitaryHistory.sourceFilter A

private theorem pole_current_unit_pair {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] (A : E→L[ℂ]E) (x : E) (hx : ‖x‖=1) :
    ‖inner ℂ x (A x)‖ ≤ ‖A‖ := by
  calc
    _ ≤ ‖x‖ * ‖A x‖ := norm_inner_le_norm _ _
    _ ≤ ‖x‖ * (‖A‖ * ‖x‖) :=
      mul_le_mul_of_nonneg_left (A.le_opNorm x) (norm_nonneg x)
    _ = _ := by rw [hx, one_mul, mul_one]

private theorem pole_current_two_unit_price {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] (A : E→L[ℂ]E) (x b : E) (hx : ‖x‖=1) (hb : ‖b‖=1) :
    ‖-inner ℂ x (A x) + inner ℂ b (A b)‖ ≤ 2*‖A‖ := by
  calc
    _ ≤ ‖-inner ℂ x (A x)‖ + ‖inner ℂ b (A b)‖ := norm_add_le _ _
    _ = ‖inner ℂ x (A x)‖ + ‖inner ℂ b (A b)‖ := by rw [norm_neg]
    _ ≤ ‖A‖ + ‖A‖ :=
      add_le_add (pole_current_unit_pair A x hx) (pole_current_unit_pair A b hb)
    _ = _ := by ring

theorem physical_n3_pole_current_price (event : DressedEvent) (leg : CompositeLeg)
    (poles : N3SourceEnergyPoleSection event.momentum leg) (i : Fin 289) :
    ‖physicalN3PoleCurrent event leg poles i‖ ≤ 2*physicalN3PoleCurrentPrice event i := by
  unfold physicalN3PoleCurrent
  rw [physical_n3_pole_noether_observer_value]
  have bound := pole_current_two_unit_price (E := ElectronHistory)
    (GaussUnitaryHistory.reader (noetherReader (fieldUnit i) event.momentum event.frame 0))
    (physicalN3PoleState event.momentum leg poles) (actualNoetherBackground event)
    (physical_n3_pole_state_norm event.momentum leg poles) (actual_noether_background_norm event)
  have source : ‖noetherReader (fieldUnit i) event.momentum event.frame 0‖ ≤
      physicalN3PoleCurrentPrice event i := by
    unfold noetherReader physicalN3PoleCurrentPrice
    exact finiteRiesz_price _ _
  exact bound.trans (mul_le_mul_of_nonneg_left
    ((pole_current_native_bound (noetherReader (fieldUnit i) event.momentum event.frame 0)).trans source)
    (by norm_num))

theorem physical_n3_pole_current_generated (event : DressedEvent) (leg : CompositeLeg)
    (poles : N3SourceEnergyPoleSection event.momentum leg) (i : Fin 289) :
    physicalN3PoleCurrent event leg poles i =
      -inner ℂ (physicalN3PoleState event.momentum leg poles)
        (GaussUnitaryHistory.reader
          (noetherReader (fieldUnit i) event.momentum event.frame 0)
          (physicalN3PoleState event.momentum leg poles)) +
      inner ℂ (actualNoetherBackground event)
        (GaussUnitaryHistory.reader
          (noetherReader (fieldUnit i) event.momentum event.frame 0)
          (actualNoetherBackground event)) :=
  physical_n3_pole_noether_observer_value event leg poles _

theorem physical_n3_pole_current_original_action (event : DressedEvent) (leg : CompositeLeg)
    (poles : N3SourceEnergyPoleSection event.momentum leg) (i : Fin 289) :
    physicalN3PoleCurrent event leg poles i =
      physicalN3PoleNoetherObserver event leg poles
        (PreparationVacuumRawJointFeedback.rawReader (fieldUnit i) event.momentum event.frame 0) :=
  congrArg (physicalN3PoleNoetherObserver event leg poles)
    (noetherReader_source (fieldUnit i) event.momentum event.frame)

theorem physical_n3_pole_contact_source_jet (event : DressedEvent) (leg : CompositeLeg)
    (poles : N3SourceEnergyPoleSection event.momentum leg) (i j : Fin 289) :
    physicalN3PoleCurrentContact event leg poles i j =
      physicalN3PoleNoetherObserver event leg poles
        (finiteRiesz event.frame (fun a b => noetherContactForm (fieldUnit i) (fieldUnit j)
          event.momentum (frameTest event.frame a) (frameTest event.frame b))) :=
  congrArg (physicalN3PoleNoetherObserver event leg poles)
    (noetherReaderContact_source (fieldUnit i) (fieldUnit j) event.momentum event.frame)

theorem physical_n3_pole_current_contact_generated (event : DressedEvent) (leg : CompositeLeg)
    (poles : N3SourceEnergyPoleSection event.momentum leg) (i j : Fin 289) :
    HasDerivAt (fun r : ℝ => physicalN3PoleNoetherObserver event leg poles
        (noetherReader (fieldUnit i) event.momentum event.frame (r • fieldUnit j)))
      (physicalN3PoleCurrentContact event leg poles i j) 0 := by
  exact ((physicalN3PoleNoetherObserver event leg poles).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0
    (noetherReader_generated (fieldUnit i) (fieldUnit j) event.momentum event.frame)

theorem physical_n3_pole_current_reader (event : DressedEvent) (leg : CompositeLeg)
    (poles : N3SourceEnergyPoleSection event.momentum leg) (f : Field289) :
    physicalN3PoleNoetherObserver event leg poles
        (noetherReader f event.momentum event.frame 0) =
      ∑ i : Fin 289, (f i : ℂ) * physicalN3PoleCurrent event leg poles i := by
  have generated := congrArg (physicalN3PoleNoetherObserver event leg poles)
    (source_reader_initial f event.momentum event.frame)
  simpa only [map_sum, map_smul, smul_eq_mul, physicalN3PoleCurrent] using generated

theorem physical_n3_pole_current_em_charge (event : DressedEvent) (leg : CompositeLeg)
    (poles : N3SourceEnergyPoleSection event.momentum leg) :
    (emCurrent (physicalN3PoleCurrent event leg poles)) 0 =
      (Stage10.ActionNormalization.phaseMomentum : ℂ) *
        physicalN3PoleRawEMPoleObserver event leg poles := by
  have hsource := physical_n3_pole_current_reader event leg poles (emGaugeField 0)
  have hnormal : physicalN3PoleNoetherObserver event leg poles (physicalN3RawEMReader event) =
      -(physicalN3PoleRawEMPoleObserver event leg poles) := by
    rw [physical_n3_pole_noether_observer_value]
    unfold physicalN3PoleRawEMPoleObserver
    ring
  have hscale : physicalN3PoleNoetherObserver event leg poles (physicalN3RawEMReader event) =
      -(Stage10.ActionNormalization.phaseMomentum : ℂ)⁻¹ *
        physicalN3PoleNoetherObserver event leg poles
          (noetherReader (emGaugeField 0) event.momentum event.frame 0) := by
    unfold physicalN3RawEMReader
    exact map_smul (physicalN3PoleNoetherObserver event leg poles) _ _
  have nonzero : (Stage10.ActionNormalization.phaseMomentum : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr Stage10.ActionNormalization.phaseMomentum_positive.ne'
  have hp : physicalN3PoleNoetherObserver event leg poles
      (noetherReader (emGaugeField 0) event.momentum event.frame 0) =
      (Stage10.ActionNormalization.phaseMomentum : ℂ) *
        physicalN3PoleRawEMPoleObserver event leg poles := by
    exact current_unit_normalization _ _ _ nonzero (hscale.symm.trans hnormal)
  have projection : (emCurrent (physicalN3PoleCurrent event leg poles)) 0 =
      ∑ i : Fin 289, ((emGaugeField 0) i : ℂ) * physicalN3PoleCurrent event leg poles i := rfl
  exact projection.trans (hsource.symm.trans hp)

/-- The corrected field owner receives all actual source-current components. -/
def physicalN3PoleCorrectedField (event : DressedEvent) (leg : CompositeLeg)
    (poles : N3SourceEnergyPoleSection event.momentum leg) (eps s sigma : ℝ)
    (n : PhysicalMomentum) : Fin 289→ℂ :=
  correctedResponse event eps s sigma n (physicalN3PoleCurrent event leg poles)

theorem physical_n3_pole_maxwell_generated (event : DressedEvent) (leg : CompositeLeg)
    (poles : N3SourceEnergyPoleSection event.momentum leg) (eps s sigma : ℝ)
    (n : PhysicalMomentum) (positive : 0<sigma)
    (regular : correctedDet event eps s sigma n≠0) :
    let p := frequencyRay eps s n
    let Q := frequencyQuantumCorrection event ((eps^2:ℝ) • n) p
      (dampedFourierClock (sourceFrequency eps s) sigma)
    nativeMomentumDivergence p (sourceEMExcitation p
        (physicalN3PoleCorrectedField event leg poles eps s sigma n)) =
      sourceEMExternalCurrent p (physicalN3PoleCurrent event leg poles) +
        sourceEMInducedCurrent p Q (physicalN3PoleCorrectedField event leg poles eps s sigma n) ∧
    sourceEMContinuity p
      (sourceEMExternalCurrent p (physicalN3PoleCurrent event leg poles) +
        sourceEMInducedCurrent p Q (physicalN3PoleCorrectedField event leg poles eps s sigma n)) = 0 :=
  actual_corrected_maxwell_generated event eps s sigma n positive regular
    (physicalN3PoleCurrent event leg poles)

end LowEnergy.GaussComposite.PhysicalN3SourceEnergy
