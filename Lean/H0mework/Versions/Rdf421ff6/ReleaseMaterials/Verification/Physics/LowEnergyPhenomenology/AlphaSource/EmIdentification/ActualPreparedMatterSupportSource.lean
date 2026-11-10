import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualPreparedMatterAuxiliarySource
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceActionReaderNull

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualPreparedMatterSupport
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
open PreparationPhysicalActionSeedReduction PreparationVacuumPropagationPencil
open PreparationVacuumPhysicalFeedback
open Filter Set MeasureTheory
open scoped Matrix BigOperators Topology ContDiff InnerProductSpace
attribute [local irreducible] noetherReader finiteRiesz noetherForm noetherSample noetherFiber
  transportedRawSymbol transportedDensity PreparationVacuumRawJointFeedback.rawReader

/-- Each primal basis component survives as independent original field data:
the slot is real, only its action direction vanishes. -/
theorem inactive_primal_survives (part : Fin 2) (spin : Fin 4) (color : Fin 3) :
    fieldPrimal (fieldUnit (primalSlot part spin color)) part spin color = 1 := by
  unfold fieldPrimal fieldUnit
  rw [Pi.single_apply, if_pos rfl]

/-- Dual basis component survives likewise. -/
theorem inactive_dual_survives (part : Fin 2) (spin : Fin 4) (color : Fin 3) :
    fieldDual (fieldUnit (dualSlot part spin color)) part spin color = 1 := by
  unfold fieldDual fieldUnit
  rw [Pi.single_apply, if_pos rfl]

/-- Gravity-B basis component survives likewise. -/
theorem inactive_gravityB_survives (pair a : Fin 6) :
    fieldGravityB (fieldUnit (gravitySlot pair a)) pair a = 1 := by
  unfold fieldGravityB fieldUnit
  rw [Pi.single_apply, if_pos rfl]

/-- Multiplier basis component survives likewise. -/
theorem inactive_multiplier_survives (pair a : Fin 6) :
    fieldMultiplier (fieldUnit (multiplierSlot pair a)) pair a = 1 := by
  unfold fieldMultiplier fieldUnit
  rw [Pi.single_apply, if_pos rfl]

/-- A gauge-B basis component survives likewise. -/
theorem inactive_gaugeB_survives (pair : Fin 6) (a : Fin 12) :
    fieldGaugeB (fieldUnit (gaugeBSlot pair a)) pair a = 1 := by
  unfold fieldGaugeB fieldUnit
  rw [Pi.single_apply, if_pos rfl]

/-- Generic original Noether transport vanishing for any field with zero
generated action direction: both variations apply that direction, so every
density, symbol, fiber, sample and form is zero before any sum is unfolded. -/
private theorem inactive_density_variation (f : Field289) (zero : fieldDirection f = 0)
    (s : ActionState) (i : Fin 4) : densityVariation f s i = 0 := by
  simp only [densityVariation, lowerVariation, principalVariation, zero, map_zero,
    zero_mul, smul_zero]
  refine Fin.cases ?_ (fun j => ?_) i <;>
    simp only [Fin.cases_zero, Fin.cases_succ, zero_sub, neg_zero]

private theorem inactive_transported_density (f : Field289) (zero : fieldDirection f = 0)
    (base candidate : ActionState) (i : Fin 4) :
    transportedDensity f base candidate i = 0 := by
  unfold transportedDensity
  rw [inactive_density_variation f zero, mul_zero]

private theorem inactive_transported_symbol (f : Field289) (zero : fieldDirection f = 0)
    (base candidate : ActionState) (p : PhysicalMomentum) :
    transportedRawSymbol f base candidate p = 0 := by
  unfold transportedRawSymbol
  have density : transportedDensity f base candidate = fun _ => 0 :=
    funext (inactive_transported_density f zero base candidate)
  rw [density]
  exact map_zero _

private theorem inactive_noether_fiber (f : Field289) (zero : fieldDirection f = 0)
    (p : PhysicalMomentum) (u : JointParameter) : noetherFiber f p u = 0 := by
  unfold noetherFiber
  rw [inactive_transported_symbol f zero, map_zero]

private theorem pair_sample_zero_right (x : SourceCoordinateSlice) (u : FockFiber) :
    pairSample x u 0 = 0 := by
  simp only [pairSample, PiLp.zero_apply, mul_zero, Finset.sum_const_zero]

private theorem inactive_noether_sample (f : Field289) (zero : fieldDirection f = 0)
    (p : PhysicalMomentum) (a b : QuantumTest) (u : JointParameter) :
    noetherSample f p a b u = 0 := by
  unfold noetherSample
  rw [inactive_noether_fiber f zero]
  simp only [zero_apply, pair_sample_zero_right]

private theorem inactive_noether_form (f : Field289) (zero : fieldDirection f = 0)
    (p : PhysicalMomentum) (a b : QuantumTest) (h : Field289) :
    noetherForm f p a b h = 0 := by
  unfold noetherForm
  simp only [inactive_noether_sample f zero, MeasureTheory.integral_zero]

private theorem finite_riesz_zero (F : GaussUnitaryHistory.Index)
    (entries : FrameIndex F → FrameIndex F → ℂ) (zero : ∀ i j, entries i j = 0) :
    finiteRiesz F entries = 0 := by
  have bound := finiteRiesz_price F entries
  have price : finitePrice F entries = 0 := by
    unfold finitePrice
    simp only [zero, norm_zero, zero_mul, Finset.sum_const_zero]
  rw [price] at bound
  exact norm_eq_zero.mp (le_antisymm bound (norm_nonneg _))

/-- The original Noether reader vanishes at every field point on each of the
192 source-inactive units, by the already generated action-direction kernel. -/
theorem actual_inactive_noether_reader_zero (i : Fin 289) (outside : (73 ≤ i.val ∧ i.val < 121) ∨ 145 ≤ i.val)
    (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) (h : Field289) :
    noetherReader (fieldUnit i) p F h = 0 := by
  unfold noetherReader
  exact finite_riesz_zero F _ (fun a b =>
    inactive_noether_form _ (sourceActionDirection_unseen i outside) p
      (frameTest F a) (frameTest F b) h)

/-- The original raw reader vanishes on each source-inactive unit, reusing the
already generated raw-reader direction kernel. -/
theorem actual_inactive_raw_reader_zero (i : Fin 289) (outside : (73 ≤ i.val ∧ i.val < 121) ∨ 145 ≤ i.val)
    (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) (h : Field289) :
    PreparationVacuumRawJointFeedback.rawReader (fieldUnit i) p F h = 0 :=
  sourceRawReader_direction_zero _ (sourceActionDirection_unseen i outside) p F h

/-- The original raw initial operator vanishes on each source-inactive unit. -/
theorem actual_inactive_raw_initial_zero (q : PhysicalResponsePoint) (i : Fin 289)
    (outside : (73 ≤ i.val ∧ i.val < 121) ∨ 145 ≤ i.val) : rawInitial q (fieldUnit i) = 0 :=
  sourceRawInitial_direction_zero q _ (sourceActionDirection_unseen i outside)

/-- The Noether reader contact vanishes on each source-inactive unit: the
generated ray derivative has a constant-zero ray, so uniqueness gives zero. -/
theorem actual_inactive_noether_contact_zero (i : Fin 289) (outside : (73 ≤ i.val ∧ i.val < 121) ∨ 145 ≤ i.val)
    (force : Field289) (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) :
    noetherReaderContact (fieldUnit i) force p F = 0 := by
  have eq : (fun _ : ℝ => (0 : PreparationVacuumNoetherChart.Operator)) =ᶠ[𝓝 0]
      fun r => noetherReader (fieldUnit i) p F (r • force) :=
    Filter.Eventually.of_forall
      (fun r => (actual_inactive_noether_reader_zero i outside p F _).symm)
  have generated := (noetherReader_generated (fieldUnit i) force p F).congr_of_eventuallyEq eq
  exact generated.unique (hasDerivAt_const (0 : ℝ) (0 : PreparationVacuumNoetherChart.Operator))

/-- The raw reader contact vanishes on each source-inactive unit by the same
uniqueness argument. -/
theorem actual_inactive_raw_contact_zero (i : Fin 289) (outside : (73 ≤ i.val ∧ i.val < 121) ∨ 145 ≤ i.val)
    (force : Field289) (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) :
    PreparationVacuumRawJointFeedback.rawReaderContact (fieldUnit i) force p F = 0 := by
  have eq : (fun _ : ℝ => (0 : H →L[ℂ] H)) =ᶠ[𝓝 0]
      fun r => PreparationVacuumRawJointFeedback.rawReader (fieldUnit i) p F (r • force) :=
    Filter.Eventually.of_forall
      (fun r => (actual_inactive_raw_reader_zero i outside p F _).symm)
  have generated := (rawReader_direction (fieldUnit i) force p F).congr_of_eventuallyEq eq
  exact generated.unique (hasDerivAt_const (0 : ℝ) (0 : H →L[ℂ] H))

end LowEnergy.GaussComposite.ActualPreparedMatterSupport
