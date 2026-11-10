import H0mework.Versions.R9c73a630.Physics.LowEnergy.AlphaSource.CanonicalPreparationMovingNoetherPreparedContact
import H0mework.Versions.R9c73a630.Physics.LowEnergy.AlphaSource.CanonicalPreparationMovingNoetherDensityTransport
import H0mework.Versions.R9c73a630.Physics.LowEnergy.AlphaSource.CanonicalPreparationRawJointReaderCompression
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedEMNativeAuxiliaryPencil

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualPreparedMatterAuxiliary
open SaturationMonoid.PhysicsCore Stage9C.Material.SpinPair
open GaussCoreHilbert GaussHistoryHilbert GaussQuantumMultiplier GaussUnitaryHistory
open SourceQuantumFockGauge SourceQuantumGaugeSliceCoordinates SourceQuantumConfigurationHilbert
open CanonicalGradedSpatialSource PreparationVacuumMixedFieldReturn PreparationVacuumGaugeSourceInjection
open PreparationVacuumActionFieldLift PreparationVacuumSourceFieldFamily
open GaussCoreDifferential
open PreparationVacuumNoetherChart PreparationVacuumRawJointFeedback PreparationVacuumFullFieldRiesz
open PreparationVacuumSourceActionJets PreparationVacuumJointFieldResponse
open PreparationVacuumNonlinearFieldCurve PreparationVacuumActualFieldQuantization
open PreparationVacuumGradedTransport PreparationVacuumHalfDensityFiber
open PreparationVacuumFieldConstraintResponse PreparationVacuumSourcePreparedResponse
open PreparationVacuumSpatialDensityTransport PreparationVacuumOriginalDensity
open ActualDressedEMNativeAuxiliary
open Filter Set MeasureTheory
open scoped Matrix BigOperators Topology ContDiff InnerProductSpace

/-- Every original FieldData channel of the auxiliary-B unit vanishes: the
gaugeBSlot 217+12p+a is disjoint from the scalar, gauge, coframe and lorentz
extractors. The gaugeB component itself stays 1, so the native auxiliary row
is not identically zero. -/
private theorem aux_ne_scalar_slot (pair : Fin 6 × Fin 12) (j : Fin 9) :
    scalarSlot j ≠ gaugeAuxiliaryIndex pair := by
  intro same
  have val := congrArg Fin.val same
  change j.val = 217 + 12 * pair.1.val + pair.2.val at val
  omega

private theorem aux_ne_gauge_slot (pair : Fin 6 × Fin 12) (mu : Fin 4) (a : Fin 12) :
    gaugeSlot mu a ≠ gaugeAuxiliaryIndex pair := by
  intro same
  have val := congrArg Fin.val same
  change 9 + 12 * mu.val + a.val = 217 + 12 * pair.1.val + pair.2.val at val
  omega

private theorem aux_ne_coframe_slot (pair : Fin 6 × Fin 12) (a mu : Fin 4) :
    coframeSlot a mu ≠ gaugeAuxiliaryIndex pair := by
  intro same
  have val := congrArg Fin.val same
  change 57 + 4 * a.val + mu.val = 217 + 12 * pair.1.val + pair.2.val at val
  omega

private theorem aux_ne_lorentz_slot (pair : Fin 6 × Fin 12) (mu : Fin 4) (a : Fin 6) :
    lorentzSlot mu a ≠ gaugeAuxiliaryIndex pair := by
  intro same
  have val := congrArg Fin.val same
  change 121 + 6 * mu.val + a.val = 217 + 12 * pair.1.val + pair.2.val at val
  omega

private theorem aux_source_scalar (pair : Fin 6 × Fin 12) :
    fieldScalar (fieldUnit (gaugeAuxiliaryIndex pair)) = 0 := by
  unfold fieldScalar fieldUnit
  apply Finset.sum_eq_zero
  intro j _
  rw [Pi.single_apply, if_neg (aux_ne_scalar_slot pair j), zero_smul]

private theorem aux_source_gauge (pair : Fin 6 × Fin 12) :
    fieldGauge (fieldUnit (gaugeAuxiliaryIndex pair)) = 0 := by
  unfold fieldGauge fieldUnit
  funext mu
  apply Finset.sum_eq_zero
  intro a _
  rw [Pi.single_apply, if_neg (aux_ne_gauge_slot pair mu a), zero_smul]

private theorem aux_source_coframe (pair : Fin 6 × Fin 12) :
    fieldCoframe (fieldUnit (gaugeAuxiliaryIndex pair)) = 0 := by
  unfold fieldCoframe fieldUnit
  funext a mu
  rw [Pi.single_apply, if_neg (aux_ne_coframe_slot pair a mu)]
  rfl

private theorem aux_source_lorentz (pair : Fin 6 × Fin 12) :
    fieldLorentz (fieldUnit (gaugeAuxiliaryIndex pair)) = 0 := by
  unfold fieldLorentz fieldUnit
  funext mu a
  rw [Pi.single_apply, if_neg (aux_ne_lorentz_slot pair mu a)]
  rfl

/-- The gaugeB unit retains its own component: the auxiliary block is real. -/
theorem auxiliary_gaugeB_control (pair : Fin 6 × Fin 12) :
    fieldGaugeB (fieldUnit (gaugeAuxiliaryIndex pair)) pair.1 pair.2 = 1 := by
  unfold fieldGaugeB fieldUnit gaugeAuxiliaryIndex
  rw [Pi.single_apply, if_pos rfl]

/-- The generated ActionState direction of an auxiliary-B unit is zero: the
original source-data extraction never touches gaugeB slots. -/
theorem auxiliary_field_direction (pair : Fin 6 × Fin 12) :
    fieldDirection (fieldUnit (gaugeAuxiliaryIndex pair)) = 0 := by
  have data : sourceData (fieldUnit (gaugeAuxiliaryIndex pair)) = 0 := by
    unfold sourceData
    apply Prod.ext
    · exact aux_source_scalar pair
    apply Prod.ext
    · exact aux_source_gauge pair
    apply Prod.ext
    · exact aux_source_coframe pair
    · exact aux_source_lorentz pair
  rw [← stateDirection_source, data, map_zero]

private theorem aux_principal_variation (pair : Fin 6 × Fin 12) (mu : Fin 4)
    (s : ActionState) :
    principalVariation (fieldUnit (gaugeAuxiliaryIndex pair)) mu s = 0 := by
  unfold principalVariation
  rw [auxiliary_field_direction, map_zero]

private theorem aux_lower_variation (pair : Fin 6 × Fin 12) (s : ActionState) :
    lowerVariation (fieldUnit (gaugeAuxiliaryIndex pair)) s = 0 := by
  unfold lowerVariation
  rw [auxiliary_field_direction, map_zero]

private theorem aux_density_variation (pair : Fin 6 × Fin 12) (s : ActionState)
    (i : Fin 4) :
    densityVariation (fieldUnit (gaugeAuxiliaryIndex pair)) s i = 0 := by
  unfold densityVariation
  simp only [aux_principal_variation pair, aux_lower_variation, smul_zero, zero_mul]
  cases i using Fin.cases <;> simp

private theorem aux_transported_density (pair : Fin 6 × Fin 12)
    (base candidate : ActionState) (i : Fin 4) :
    transportedDensity (fieldUnit (gaugeAuxiliaryIndex pair)) base candidate i = 0 := by
  unfold transportedDensity
  rw [aux_density_variation, mul_zero]

private theorem aux_transported_symbol (pair : Fin 6 × Fin 12)
    (base candidate : ActionState) (p : PhysicalMomentum) :
    transportedRawSymbol (fieldUnit (gaugeAuxiliaryIndex pair)) base candidate p = 0 := by
  unfold transportedRawSymbol
  have density : transportedDensity (fieldUnit (gaugeAuxiliaryIndex pair)) base candidate =
      fun _ => 0 := funext (aux_transported_density pair base candidate)
  rw [density]
  exact map_zero _

private theorem aux_raw_action_symbol (pair : Fin 6 × Fin 12)
    (p : PhysicalMomentum) (s : ActionState) :
    rawActionSymbol (fieldUnit (gaugeAuxiliaryIndex pair)) p s = 0 := by
  unfold rawActionSymbol
  have density : (fun i => densityActionMatrix *
      densityVariation (fieldUnit (gaugeAuxiliaryIndex pair)) s i) = fun _ => 0 := by
    funext i
    rw [aux_density_variation, mul_zero]
  rw [density]
  exact map_zero _

private theorem aux_noether_fiber (pair : Fin 6 × Fin 12) (p : PhysicalMomentum)
    (u : JointParameter) :
    noetherFiber (fieldUnit (gaugeAuxiliaryIndex pair)) p u = 0 := by
  unfold noetherFiber
  rw [aux_transported_symbol, map_zero]

private theorem aux_raw_fiber (pair : Fin 6 × Fin 12) (p : PhysicalMomentum)
    (u : JointParameter) :
    rawFiber (fieldUnit (gaugeAuxiliaryIndex pair)) p u = 0 := by
  unfold rawFiber
  rw [aux_raw_action_symbol, map_zero]

private theorem pair_sample_zero_right (x : SourceCoordinateSlice) (u : FockFiber) :
    pairSample x u 0 = 0 := by
  simp only [pairSample, PiLp.zero_apply, mul_zero, Finset.sum_const_zero]

private theorem aux_noether_sample (pair : Fin 6 × Fin 12) (p : PhysicalMomentum)
    (a b : QuantumTest) (u : JointParameter) :
    noetherSample (fieldUnit (gaugeAuxiliaryIndex pair)) p a b u = 0 := by
  unfold noetherSample
  rw [aux_noether_fiber]
  simp only [zero_apply, pair_sample_zero_right]

private theorem aux_raw_sample (pair : Fin 6 × Fin 12) (p : PhysicalMomentum)
    (a b : QuantumTest) (u : JointParameter) :
    rawSample (fieldUnit (gaugeAuxiliaryIndex pair)) p a b u = 0 := by
  unfold rawSample
  rw [aux_raw_fiber]
  simp only [zero_apply, pair_sample_zero_right]

private theorem aux_noether_form (pair : Fin 6 × Fin 12) (p : PhysicalMomentum)
    (a b : QuantumTest) (h : Field289) :
    noetherForm (fieldUnit (gaugeAuxiliaryIndex pair)) p a b h = 0 := by
  unfold noetherForm
  simp only [aux_noether_sample pair, MeasureTheory.integral_zero]

private theorem aux_raw_form (pair : Fin 6 × Fin 12) (p : PhysicalMomentum)
    (a b : QuantumTest) (h : Field289) :
    rawForm (fieldUnit (gaugeAuxiliaryIndex pair)) p a b h = 0 := by
  unfold rawForm
  simp only [aux_raw_sample pair, MeasureTheory.integral_zero]

private theorem finite_riesz_zero (F : GaussUnitaryHistory.Index)
    (entries : FrameIndex F → FrameIndex F → ℂ) (zero : ∀ i j, entries i j = 0) :
    finiteRiesz F entries = 0 := by
  have bound := finiteRiesz_price F entries
  have price : finitePrice F entries = 0 := by
    unfold finitePrice
    simp only [zero, norm_zero, zero_mul, Finset.sum_const_zero]
  rw [price] at bound
  exact norm_eq_zero.mp (le_antisymm bound (norm_nonneg _))

/-- The original Noether reader vanishes on every generated auxiliary-B unit,
at every h. -/
theorem actual_auxiliary_noether_reader_zero (pair : Fin 6 × Fin 12)
    (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) (h : Field289) :
    noetherReader (fieldUnit (gaugeAuxiliaryIndex pair)) p F h = 0 := by
  unfold noetherReader
  exact finite_riesz_zero F _ (fun i j => aux_noether_form pair p _ _ h)

/-- The original raw reader vanishes on every generated auxiliary-B unit. -/
theorem actual_auxiliary_raw_reader_zero (pair : Fin 6 × Fin 12)
    (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) (h : Field289) :
    PreparationVacuumRawJointFeedback.rawReader (fieldUnit (gaugeAuxiliaryIndex pair)) p F h = 0 := by
  unfold PreparationVacuumRawJointFeedback.rawReader
  exact finite_riesz_zero F _ (fun i j => aux_raw_form pair p _ _ h)

/-- The Noether reader contact vanishes: the constant-zero reader has a
constant-zero ray. -/
theorem actual_auxiliary_noether_contact_zero (pair : Fin 6 × Fin 12)
    (force : Field289) (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) :
    noetherReaderContact (fieldUnit (gaugeAuxiliaryIndex pair)) force p F = 0 := by
  have eq : (fun _ : ℝ => (0 : PreparationVacuumNoetherChart.Operator)) =ᶠ[𝓝 0]
      fun r => noetherReader (fieldUnit (gaugeAuxiliaryIndex pair)) p F (r • force) :=
    Filter.Eventually.of_forall (fun r => (actual_auxiliary_noether_reader_zero pair p F _).symm)
  have generated := (noetherReader_generated (fieldUnit (gaugeAuxiliaryIndex pair)) force p F)
      |>.congr_of_eventuallyEq eq
  exact generated.unique (hasDerivAt_const (0 : ℝ) (0 : PreparationVacuumNoetherChart.Operator))

/-- The raw reader contact vanishes by the same uniqueness argument. -/
theorem actual_auxiliary_raw_contact_zero (pair : Fin 6 × Fin 12)
    (force : Field289) (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) :
    rawReaderContact (fieldUnit (gaugeAuxiliaryIndex pair)) force p F = 0 := by
  have eq : (fun _ : ℝ => (0 : H →L[ℂ] H)) =ᶠ[𝓝 0]
      fun r => PreparationVacuumRawJointFeedback.rawReader
        (fieldUnit (gaugeAuxiliaryIndex pair)) p F (r • force) :=
    Filter.Eventually.of_forall (fun r => (actual_auxiliary_raw_reader_zero pair p F _).symm)
  have generated := (rawReader_direction (fieldUnit (gaugeAuxiliaryIndex pair)) force p F)
      |>.congr_of_eventuallyEq eq
  exact generated.unique (hasDerivAt_const (0 : ℝ) (0 : H →L[ℂ] H))


end LowEnergy.GaussComposite.ActualPreparedMatterAuxiliary
