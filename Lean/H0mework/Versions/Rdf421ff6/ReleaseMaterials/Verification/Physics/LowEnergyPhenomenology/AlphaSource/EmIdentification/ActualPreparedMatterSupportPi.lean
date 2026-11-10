import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualPreparedMatterSupportSource
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualSourcePreparedTemporalQuantumIR
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedStaticPolarization
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualSourcePreparedNoetherPi

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualPreparedMatterSupport
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
open PreparationVacuumPhysicalConstraint114 PreparationPhysicalActionSeedReduction
open Filter Set MeasureTheory
open scoped Matrix BigOperators Topology ContDiff
attribute [local irreducible] sourceInverse jointResolvent jointCurrent jointGenerator twoTimeMap
attribute [local irreducible] slopeInitial rawInitial leftCurrent rightCurrent leftGenerator rightGenerator
attribute [local irreducible] noetherStaticInitial noetherStaticContact noetherStaticHalf
attribute [local irreducible] dressedEulerObserver dressedStaticPolarization dressedKinematicPoint
attribute [local irreducible] sourcePreparedPiEntry sourcePreparedClockQuantumMatrix
attribute [local irreducible] sourceTemporalActualQuantumDriver sourceTemporalCorrectedField
attribute [local irreducible] noetherReader noetherReaderContact
attribute [local irreducible] PreparationVacuumRawJointFeedback.rawReader
    PreparationVacuumRawJointFeedback.rawReaderContact

/-- The original Noether static initial operator vanishes on each
source-inactive unit: the reader, contact and raw parts are all zero. -/
private theorem inactive_noether_initial_zero (q : PhysicalResponsePoint) (i : Fin 289)
    (outside : (73 ≤ i.val ∧ i.val < 121) ∨ 145 ≤ i.val) (force : Field289) :
    noetherStaticInitial q (fieldUnit i) force = 0 := by
  unfold noetherStaticInitial noetherStaticContact slopeInitial
  simp only [actual_inactive_noether_contact_zero i outside,
    actual_inactive_raw_contact_zero i outside,
    actual_inactive_raw_reader_zero i outside, mul_zero, zero_mul, sub_self, add_zero]

/-- Every original prepared Pi entry in a source-inactive row is zero: the whole
Noether initial and raw initial operators vanish on the inactive reader, while
the original inverses, currents, contacts and all 289 force columns remain. -/
theorem actual_prepared_inactive_pi_row (event : DressedEvent) (transfer : PhysicalMomentum)
    (lambda : ℂ) (positive : 0 < lambda.re) (i : Fin 289)
    (outside : (73 ≤ i.val ∧ i.val < 121) ∨ 145 ≤ i.val) (j : Fin 289) :
    sourcePreparedPiEntry event transfer lambda i j = 0 := by
  let q := dressedKinematicPoint event transfer
  have inner :
      noetherStaticInitial q (fieldUnit i) (fieldUnit j) -
        leftCurrent q (fieldUnit j) *
          (sourceInverse q lambda)
            (rawInitial q (fieldUnit i)) +
      (sourceInverse q lambda)
          (rawInitial q (fieldUnit i)) *
        rightCurrent q (fieldUnit j) = 0 := by
    have init : noetherStaticInitial q (fieldUnit i) (fieldUnit j) = 0 :=
      inactive_noether_initial_zero q i outside (fieldUnit j)
    have rawI : rawInitial q (fieldUnit i) = 0 := actual_inactive_raw_initial_zero q i outside
    have SIzero : (sourceInverse q lambda) 0 = 0 := map_zero _
    have eq_ab : (noetherStaticInitial q (fieldUnit i) (fieldUnit j),
        rawInitial q (fieldUnit i)) =
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
  have chain : sourcePreparedPiEntry event transfer lambda i j =
      dressedEulerObserver event ((sourceInverse q lambda)
        (noetherStaticInitial q (fieldUnit i) (fieldUnit j) -
          leftCurrent q (fieldUnit j) *
            (sourceInverse q lambda)
              (rawInitial q (fieldUnit i)) +
        (sourceInverse q lambda)
            (rawInitial q (fieldUnit i)) *
          rightCurrent q (fieldUnit j))) :=
    (source_prepared_pi_actual event transfer lambda positive _ _).trans
      (dressed_static_polarization_inverse event transfer lambda positive _ _)
  have obs : dressedEulerObserver event ((sourceInverse q lambda)
        (noetherStaticInitial q (fieldUnit i) (fieldUnit j) -
          leftCurrent q (fieldUnit j) *
            (sourceInverse q lambda)
              (rawInitial q (fieldUnit i)) +
        (sourceInverse q lambda)
            (rawInitial q (fieldUnit i)) *
          rightCurrent q (fieldUnit j))) =
      dressedEulerObserver event ((sourceInverse q lambda) 0) :=
    congrArg (dressedEulerObserver event) (congrArg (sourceInverse q lambda) inner)
  have obs0 : dressedEulerObserver event ((sourceInverse q lambda) 0) =
      dressedEulerObserver event 0 :=
    congrArg (dressedEulerObserver event) (map_zero (sourceInverse q lambda))
  have obs1 : dressedEulerObserver event 0 = 0 := map_zero _
  exact chain.trans (obs.trans (obs0.trans obs1))

/-- The actual generated quantum driver vanishes on each source-inactive
coordinate: the sigma-scaled original Pi annihilates that row, while all actual
GE0 force columns retain their e/sigma/n dependence. -/
theorem actual_quantum_driver_inactive_zero (event : DressedEvent) (e : scaleDomain)
    (sigma : ℝ) (n : PhysicalMomentum) (positiveSigma : 0 < sigma) (i : Fin 289)
    (outside : (73 ≤ i.val ∧ i.val < 121) ∨ 145 ≤ i.val) :
    sourceTemporalActualQuantumDriver event e sigma n i = 0 := by
  have pos : 0 < (sigma : ℂ).re := by simpa only [Complex.ofReal_re] using positiveSigma
  unfold sourceTemporalActualQuantumDriver sourcePreparedClockQuantumMatrix
  simp only [Matrix.mulVec, dotProduct, Matrix.smul_apply, smul_eq_mul, Matrix.of_apply]
  apply Finset.sum_eq_zero
  intro j _
  rw [actual_prepared_inactive_pi_row event ((e.val^2 : ℝ) • n) (sigma : ℂ) pos i outside j]
  simp

end LowEnergy.GaussComposite.ActualPreparedMatterSupport
