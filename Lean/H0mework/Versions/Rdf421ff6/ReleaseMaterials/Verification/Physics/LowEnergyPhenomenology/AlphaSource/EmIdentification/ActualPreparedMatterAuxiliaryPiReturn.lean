import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualPreparedMatterAuxiliarySource
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualSourcePreparedTemporalQuantumIR
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedStaticPolarization
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualSourcePreparedNoetherPi
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedEMQuantumAuxiliarySchur

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualPreparedMatterAuxiliary
open SaturationMonoid.PhysicsCore Stage9C.Material.SpinPair
open GaussCoreHilbert GaussHistoryHilbert GaussQuantumMultiplier GaussUnitaryHistory
open CanonicalGradedSpatialSource PreparationVacuumMixedFieldReturn PreparationVacuumGaugeSourceInjection
open PreparationVacuumActionFieldLift PreparationVacuumSourceFieldFamily
open PreparationVacuumNoetherChart PreparationVacuumRawJointFeedback
open PreparationVacuumJointFieldResponse PreparationVacuumPropagationPencil
open PreparationVacuumPhysicalFeedback PreparationVacuumPhysicalCharacteristic
open SourcePropagationResolvent SourcePropagationNoetherTime
open ActualDressedSylvester ActualDressedPencil ActualDressedSignal
open ActualDressedNoether ActualDressedFullCoulomb
open ActualSourcePreparedNoetherPi ActualSourcePreparedN3MovingResponse
open ActualSourcePreparedTemporalQuantumWard ActualSourcePreparedTemporalQuantumIR
open ActualSourcePreparedTemporalEMConstraint
open ActualDressedEMNativeAuxiliary
open Filter Set MeasureTheory
open scoped Matrix BigOperators Topology ContDiff
attribute [local irreducible] sourceInverse jointResolvent jointCurrent jointGenerator twoTimeMap
attribute [local irreducible] slopeInitial rawInitial leftCurrent rightCurrent leftGenerator rightGenerator
attribute [local irreducible] noetherStaticInitial noetherStaticContact noetherStaticHalf
attribute [local irreducible] dressedEulerObserver dressedStaticPolarization dressedKinematicPoint
attribute [local irreducible] sourcePreparedPiEntry sourcePreparedClockQuantumMatrix
attribute [local irreducible] sourceTemporalActualQuantumDriver sourceTemporalCorrectedField
attribute [local irreducible] emAuxiliarySlice
attribute [local irreducible] noetherReader noetherReaderContact
attribute [local irreducible] PreparationVacuumRawJointFeedback.rawReader
    PreparationVacuumRawJointFeedback.rawReaderContact

private theorem aux_noether_initial_zero (q : PhysicalResponsePoint)
    (pair : Fin 6 × Fin 12) (force : Field289) :
    noetherStaticInitial q (fieldUnit (gaugeAuxiliaryIndex pair)) force = 0 := by
  unfold noetherStaticInitial noetherStaticContact slopeInitial
  simp only [actual_auxiliary_noether_contact_zero, actual_auxiliary_raw_contact_zero,
    actual_auxiliary_raw_reader_zero, mul_zero, zero_mul, sub_self, add_zero]

private theorem aux_raw_initial_zero (q : PhysicalResponsePoint) (pair : Fin 6 × Fin 12) :
    rawInitial q (fieldUnit (gaugeAuxiliaryIndex pair)) = 0 := by
  unfold rawInitial
  simp only [actual_auxiliary_raw_reader_zero, mul_zero, zero_mul]

/-- Every original prepared Pi entry in an auxiliary-B row is zero: the whole
Noether initial and raw initial operators vanish on the auxiliary-B reader. -/
theorem actual_prepared_auxiliary_pi_row (event : DressedEvent) (transfer : PhysicalMomentum)
    (lambda : ℂ) (positive : 0 < lambda.re) (pair : Fin 6 × Fin 12) (j : Fin 289) :
    sourcePreparedPiEntry event transfer lambda (gaugeAuxiliaryIndex pair) j = 0 := by
  let q := dressedKinematicPoint event transfer
  have inner :
      noetherStaticInitial q (fieldUnit (gaugeAuxiliaryIndex pair)) (fieldUnit j) -
        leftCurrent q (fieldUnit j) *
          (sourceInverse q lambda)
            (rawInitial q (fieldUnit (gaugeAuxiliaryIndex pair))) +
      (sourceInverse q lambda)
          (rawInitial q (fieldUnit (gaugeAuxiliaryIndex pair))) *
        rightCurrent q (fieldUnit j) = 0 := by
    have init : noetherStaticInitial q (fieldUnit (gaugeAuxiliaryIndex pair)) (fieldUnit j) =
        0 := aux_noether_initial_zero q pair (fieldUnit j)
    have rawI : rawInitial q (fieldUnit (gaugeAuxiliaryIndex pair)) = 0 :=
      aux_raw_initial_zero q pair
    have SIzero : (sourceInverse q lambda) 0 = 0 := map_zero _
    have eq_ab : (noetherStaticInitial q (fieldUnit (gaugeAuxiliaryIndex pair)) (fieldUnit j),
        rawInitial q (fieldUnit (gaugeAuxiliaryIndex pair))) =
        ((0 : H →L[ℂ] H), (0 : H →L[ℂ] H)) := by
      apply Prod.ext
      · exact init
      · exact rawI
    have subst := congrArg (fun p : (H →L[ℂ] H) × (H →L[ℂ] H) =>
        p.1 - leftCurrent q (fieldUnit j) * (sourceInverse q lambda) p.2 +
        (sourceInverse q lambda) p.2 * rightCurrent q (fieldUnit j)) eq_ab
    have eval := congrArg (fun x : (H →L[ℂ] H) =>
        (0 : H →L[ℂ] H) - leftCurrent q (fieldUnit j) * x +
        x * rightCurrent q (fieldUnit j)) SIzero
    refine subst.trans (eval.trans ?_)
    simp only [mul_zero, zero_mul, sub_self, add_zero]
  have chain : sourcePreparedPiEntry event transfer lambda (gaugeAuxiliaryIndex pair) j =
      dressedEulerObserver event ((sourceInverse q lambda)
        (noetherStaticInitial q (fieldUnit (gaugeAuxiliaryIndex pair)) (fieldUnit j) -
          leftCurrent q (fieldUnit j) *
            (sourceInverse q lambda)
              (rawInitial q (fieldUnit (gaugeAuxiliaryIndex pair))) +
        (sourceInverse q lambda)
            (rawInitial q (fieldUnit (gaugeAuxiliaryIndex pair))) *
          rightCurrent q (fieldUnit j))) :=
    (source_prepared_pi_actual event transfer lambda positive _ _).trans
      (dressed_static_polarization_inverse event transfer lambda positive _ _)
  have obs : dressedEulerObserver event ((sourceInverse q lambda)
        (noetherStaticInitial q (fieldUnit (gaugeAuxiliaryIndex pair)) (fieldUnit j) -
          leftCurrent q (fieldUnit j) *
            (sourceInverse q lambda)
              (rawInitial q (fieldUnit (gaugeAuxiliaryIndex pair))) +
        (sourceInverse q lambda)
            (rawInitial q (fieldUnit (gaugeAuxiliaryIndex pair))) *
          rightCurrent q (fieldUnit j))) =
      dressedEulerObserver event ((sourceInverse q lambda) 0) :=
    congrArg (dressedEulerObserver event) (congrArg (sourceInverse q lambda) inner)
  have obs0 : dressedEulerObserver event ((sourceInverse q lambda) 0) =
      dressedEulerObserver event 0 :=
    congrArg (dressedEulerObserver event) (map_zero (sourceInverse q lambda))
  have obs1 : dressedEulerObserver event 0 = 0 := map_zero _
  exact chain.trans (obs.trans (obs0.trans obs1))

/-- The actual generated quantum driver has zero auxiliary slice: the
sigma-scaled original Pi annihilates every auxiliary-B row. All actual GE0
force columns retain their e/sigma/n dependence. -/
theorem actual_quantum_driver_auxiliary_zero (event : DressedEvent) (e : scaleDomain)
    (sigma : ℝ) (n : PhysicalMomentum) (positiveSigma : 0 < sigma) :
    emAuxiliarySlice (sourceTemporalActualQuantumDriver event e sigma n) = 0 := by
  have pos : 0 < (sigma : ℂ).re := by simpa only [Complex.ofReal_re] using positiveSigma
  funext pair
  unfold emAuxiliarySlice sourceTemporalActualQuantumDriver sourcePreparedClockQuantumMatrix
  simp only [Matrix.mulVec, dotProduct, Matrix.smul_apply, smul_eq_mul, Matrix.of_apply]
  apply Finset.sum_eq_zero
  intro j _
  rw [actual_prepared_auxiliary_pi_row event ((e.val^2 : ℝ) • n) (sigma : ℂ) pos pair j]
  simp


end LowEnergy.GaussComposite.ActualPreparedMatterAuxiliary
