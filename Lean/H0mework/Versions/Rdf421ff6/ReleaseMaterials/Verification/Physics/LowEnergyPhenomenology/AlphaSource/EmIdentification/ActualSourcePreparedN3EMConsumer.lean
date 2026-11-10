import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualSourcePreparedEMEnclosure
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.PhysicalN3PoleCoulombRead

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualSourcePreparedN3EMConsumer
open CanonicalGradedSpatialSource PreparationVacuumMixedFieldReturn
open ActualDressedFullCoulomb ActualDressedCorrectedGreen ActualDressedNoetherCoulombUnit
open ActualCompositeFieldCurrent ActualEMResponseSplit PhysicalN3SourceEnergy
open ActualSourcePreparedEMEnclosure
open LowEnergy.ActualSourceQuantumCoefficientErrorOwn
open scoped Matrix BigOperators

/-- The two independent physical pole currents consume the complete generated
prepared response, including every field component. -/
def sourcePreparedN3Read (fieldEvent detector source : DressedEvent) (epsilon sigma : ℝ)
    (n : PhysicalMomentum) (dLeg sLeg : CompositeLeg)
    (dPoles : N3SourceEnergyPoleSection detector.momentum dLeg)
    (sPoles : N3SourceEnergyPoleSection source.momentum sLeg) : ℂ :=
  emCurrentObservation (sourcePreparedFullGreenRead fieldEvent epsilon sigma n)
    (physicalN3PoleCurrent detector dLeg dPoles) (physicalN3PoleCurrent source sLeg sPoles)

theorem source_prepared_n3_four_parts (fieldEvent detector source : DressedEvent) (epsilon sigma : ℝ)
    (n : PhysicalMomentum) (dLeg sLeg : CompositeLeg)
    (dPoles : N3SourceEnergyPoleSection detector.momentum dLeg)
    (sPoles : N3SourceEnergyPoleSection source.momentum sLeg)
    (positive : 0 < sigma) (regular : correctedDet fieldEvent epsilon 0 sigma n ≠ 0) :
    sourcePreparedN3Read fieldEvent detector source epsilon sigma n dLeg sLeg dPoles sPoles =
      dotProduct (physicalN3PoleNoetherCurrent detector dLeg dPoles)
        ((noetherPairScale^2 • sourcePreparedEMTensorRead fieldEvent epsilon sigma n) *ᵥ
          physicalN3PoleNoetherCurrent source sLeg sPoles) +
        physicalN3PoleNonPureRead fieldEvent detector source dLeg sLeg dPoles sPoles epsilon 0 sigma n := by
  unfold sourcePreparedN3Read
  rw [source_prepared_full_green_original fieldEvent epsilon sigma n positive regular,
    source_prepared_em_tensor_original fieldEvent epsilon sigma n positive regular]
  exact physical_n3_pole_corrected_four_parts fieldEvent detector source dLeg sLeg dPoles sPoles epsilon 0 sigma n

def sourcePreparedN3BinaryRead (fieldEvent detector source : DressedEvent) (epsilon sigma : ℝ)
    (n : PhysicalMomentum) (bits : ℕ) (dLeg sLeg : CompositeLeg)
    (dPoles : N3SourceEnergyPoleSection detector.momentum dLeg)
    (sPoles : N3SourceEnergyPoleSection source.momentum sLeg) : ℂ :=
  emCurrentObservation (sourceFullGreenBinaryRead fieldEvent epsilon sigma n bits)
    (physicalN3PoleCurrent detector dLeg dPoles) (physicalN3PoleCurrent source sLeg sPoles)

def sourceN3CurrentPairMass (detector source : DressedEvent) (dLeg sLeg : CompositeLeg)
    (dPoles : N3SourceEnergyPoleSection detector.momentum dLeg)
    (sPoles : N3SourceEnergyPoleSection source.momentum sLeg) : ℝ :=
  ∑i, ∑j, ‖physicalN3PoleCurrent detector dLeg dPoles i‖ * ‖physicalN3PoleCurrent source sLeg sPoles j‖

theorem source_n3_current_pair_mass_nonnegative (detector source : DressedEvent) (dLeg sLeg : CompositeLeg)
    (dPoles : N3SourceEnergyPoleSection detector.momentum dLeg)
    (sPoles : N3SourceEnergyPoleSection source.momentum sLeg) :
    0 ≤ sourceN3CurrentPairMass detector source dLeg sLeg dPoles sPoles := by
  exact Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => mul_nonneg (norm_nonneg _) (norm_nonneg _)))

private theorem current_matrix_error (G W : Matrix (Fin 289) (Fin 289) ℂ)
    (fd fs : Fin 289 → ℂ) (tolerance : ℝ) (paid : ∀i j, ‖G i j-W i j‖ ≤ tolerance) :
    ‖emCurrentObservation G fd fs-emCurrentObservation W fd fs‖ ≤
      tolerance * ∑i, ∑j, ‖fd i‖ * ‖fs j‖ := by
  have difference : emCurrentObservation G fd fs-emCurrentObservation W fd fs =
      ∑i, ∑j, fd i * (G i j-W i j) * fs j := by
    unfold emCurrentObservation
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [difference, Finset.mul_sum]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro i _
  rw [Finset.mul_sum]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro j _
  rw [norm_mul, norm_mul]
  calc
    _ ≤ ‖fd i‖ * tolerance * ‖fs j‖ :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (paid i j) (norm_nonneg _)) (norm_nonneg _)
    _ = _ := by ring

/-- The requested physical-read tolerance is paid by a source-generated matrix
precision, not by dropping mixed/residual terms or assuming a unit current. -/
theorem source_prepared_n3_generated_enclosure (fieldEvent detector source : DressedEvent) (epsilon sigma : ℝ)
    (n : PhysicalMomentum) (dLeg sLeg : CompositeLeg)
    (dPoles : N3SourceEnergyPoleSection detector.momentum dLeg)
    (sPoles : N3SourceEnergyPoleSection source.momentum sLeg)
    (positive : 0 < sigma) (small : sigma ≤ 2)
    (regular : correctedDet fieldEvent epsilon 0 sigma n ≠ 0) (tolerance : ℝ) (accurate : 0 < tolerance) :
    ∃bits, 0 < sourceCommonDeterminantMargin fieldEvent epsilon sigma n bits ∧
      ‖sourcePreparedN3Read fieldEvent detector source epsilon sigma n dLeg sLeg dPoles sPoles-
        sourcePreparedN3BinaryRead fieldEvent detector source epsilon sigma n bits dLeg sLeg dPoles sPoles‖ ≤ tolerance := by
  let mass := sourceN3CurrentPairMass detector source dLeg sLeg dPoles sPoles
  have nonnegative : 0 ≤ mass := source_n3_current_pair_mass_nonnegative detector source dLeg sLeg dPoles sPoles
  have scale : 0 < 1 + mass := by linarith
  let entryTolerance := tolerance / (1 + mass)
  have entryPositive : 0 < entryTolerance := div_pos accurate scale
  let bits := sourcePreparedBinaryBits fieldEvent epsilon sigma n positive small regular entryTolerance entryPositive
  have margin := (source_binary_generated_precision fieldEvent epsilon sigma n positive small regular entryTolerance entryPositive).1
  have entries := (source_prepared_generated_enclosure fieldEvent epsilon sigma n positive small regular entryTolerance entryPositive).1
  refine ⟨bits, margin, ?_⟩
  have paid := current_matrix_error (sourcePreparedFullGreenRead fieldEvent epsilon sigma n)
    (sourceFullGreenBinaryRead fieldEvent epsilon sigma n bits)
    (physicalN3PoleCurrent detector dLeg dPoles) (physicalN3PoleCurrent source sLeg sPoles)
    entryTolerance (fun i j => (entries i j).le)
  apply paid.trans
  change tolerance / (1 + mass) * mass ≤ tolerance
  have fraction : mass / (1 + mass) ≤ 1 := (div_le_one scale).mpr (by linarith)
  calc
    _ = tolerance * (mass / (1 + mass)) := by ring
    _ ≤ tolerance * 1 := mul_le_mul_of_nonneg_left fraction accurate.le
    _ = _ := mul_one _

end LowEnergy.GaussComposite.ActualSourcePreparedN3EMConsumer
