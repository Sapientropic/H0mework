import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualSourcePreparedN3IRNumerator

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency true
noncomputable section
namespace LowEnergy.GaussComposite.ActualSourcePreparedN3EMIRSplit
open CanonicalGradedSpatialSource ActualDressedFullCoulomb ActualDressedCorrectedGreen
open ActualDressedUniformMaterialCoefficients ActualDressedPhysicalRayNumerator
open LowEnergy.GaussComposite.ActualDressedVisiblePole
open ActualSourcePreparedEMEnclosure ActualSourcePreparedN3EMConsumer ActualSourcePreparedN3IRNumerator
open ActualCompositeFieldCurrent ActualEMCurrentSplit ActualEMResponseSplit PhysicalN3SourceEnergy
open ActualDressedNoetherCoulombUnit ActualDressedZeroDamping ActualDressedEMTensorClock
open LowEnergy.ActualDressedVisiblePole Polynomial Filter Set
open scoped Matrix BigOperators Topology
attribute [local irreducible] commonClearedPencil commonDenominator correctedGreen

def sourceN3ArmCurrent (event : DressedEvent) (leg : CompositeLeg)
    (poles : N3SourceEnergyPoleSection event.momentum leg) (electromagnetic : Bool) : Fin 289 → ℂ :=
  if electromagnetic then emCurrentForce (physicalN3PoleCurrent event leg poles)
  else emCurrentResidual (physicalN3PoleCurrent event leg poles)

/-- All four arms contract the same source cofactor before reduction; their
clock pole orders need not agree. -/
def sourceN3ArmNumerator (fieldEvent detector source : DressedEvent) (n : PhysicalMomentum)
    (dLeg sLeg : CompositeLeg) (dPoles : N3SourceEnergyPoleSection detector.momentum dLeg)
    (sPoles : N3SourceEnergyPoleSection source.momentum sLeg) (dEM sEM : Bool) : Parameters :=
  commonDenominator fieldEvent n *
    dotProduct (fun i => MvPolynomial.C (sourceN3ArmCurrent detector dLeg dPoles dEM i))
      ((commonClearedPencil fieldEvent n).adjugate *ᵥ
        (fun j => MvPolynomial.C (sourceN3ArmCurrent source sLeg sPoles sEM j)))

def sourceN3ArmRead (fieldEvent detector source : DressedEvent) (epsilon sigma : ℝ)
    (n : PhysicalMomentum) (dLeg sLeg : CompositeLeg)
    (dPoles : N3SourceEnergyPoleSection detector.momentum dLeg)
    (sPoles : N3SourceEnergyPoleSection source.momentum sLeg) (dEM sEM : Bool) : ℂ :=
  emCurrentObservation (sourcePreparedFullGreenRead fieldEvent epsilon sigma n)
    (sourceN3ArmCurrent detector dLeg dPoles dEM) (sourceN3ArmCurrent source sLeg sPoles sEM)

private theorem constant_current_split (f : Fin 289 → ℂ) :
    (fun i => MvPolynomial.C (f i) : Fin 289 → Parameters) =
      (fun i => MvPolynomial.C (emCurrentForce f i)) +
        (fun i => MvPolynomial.C (emCurrentResidual f i)) := by
  funext i
  rw [congrFun (em_current_complete f) i]
  exact map_add _ _ _

theorem source_n3_numerator_four_arms (fieldEvent detector source : DressedEvent)
    (n : PhysicalMomentum) (dLeg sLeg : CompositeLeg)
    (dPoles : N3SourceEnergyPoleSection detector.momentum dLeg)
    (sPoles : N3SourceEnergyPoleSection source.momentum sLeg) :
    sourceN3CurrentNumerator fieldEvent detector source n dLeg sLeg dPoles sPoles =
      sourceN3ArmNumerator fieldEvent detector source n dLeg sLeg dPoles sPoles true true +
      sourceN3ArmNumerator fieldEvent detector source n dLeg sLeg dPoles sPoles true false +
      sourceN3ArmNumerator fieldEvent detector source n dLeg sLeg dPoles sPoles false true +
      sourceN3ArmNumerator fieldEvent detector source n dLeg sLeg dPoles sPoles false false := by
  unfold sourceN3CurrentNumerator
  rw [constant_current_split (physicalN3PoleCurrent detector dLeg dPoles),
    constant_current_split (physicalN3PoleCurrent source sLeg sPoles), Matrix.mulVec_add,
    add_dotProduct, dotProduct_add, dotProduct_add]
  simp only [sourceN3ArmNumerator, sourceN3ArmCurrent, Bool.false_eq_true, ↓reduceIte]
  ring

private theorem evaluate_constant_read (H : Matrix (Fin 289) (Fin 289) Parameters)
    (v : Fin 3 → ℂ) (fd fs : Fin 289 → ℂ) :
    MvPolynomial.eval v (dotProduct (fun i => MvPolynomial.C (fd i))
      (H *ᵥ (fun j => MvPolynomial.C (fs j)))) =
      dotProduct fd ((H.map (MvPolynomial.eval v)) *ᵥ fs) := by
  simp only [dotProduct, Matrix.mulVec, map_sum, map_mul, MvPolynomial.eval_C, Matrix.map_apply]

theorem source_n3_arm_numerator_eval (fieldEvent detector source : DressedEvent)
    (epsilon sigma : ℝ) (n : PhysicalMomentum) (dLeg sLeg : CompositeLeg)
    (dPoles : N3SourceEnergyPoleSection detector.momentum dLeg)
    (sPoles : N3SourceEnergyPoleSection source.momentum sLeg) (dEM sEM : Bool) :
    MvPolynomial.eval (irValues epsilon sigma 0)
      (sourceN3ArmNumerator fieldEvent detector source n dLeg sLeg dPoles sPoles dEM sEM) =
      MvPolynomial.eval (irValues epsilon sigma 0) (commonDenominator fieldEvent n) *
        emCurrentObservation
          (((commonClearedPencil fieldEvent n).map (MvPolynomial.eval (irValues epsilon sigma 0))).adjugate)
          (sourceN3ArmCurrent detector dLeg dPoles dEM) (sourceN3ArmCurrent source sLeg sPoles sEM) := by
  unfold sourceN3ArmNumerator
  rw [map_mul, evaluate_constant_read]
  have mapped := (MvPolynomial.eval (irValues epsilon sigma 0)).map_adjugate (commonClearedPencil fieldEvent n)
  have matrix_map (H : Matrix (Fin 289) (Fin 289) Parameters) :
      (MvPolynomial.eval (irValues epsilon sigma 0)).mapMatrix H =
        H.map (MvPolynomial.eval (irValues epsilon sigma 0)) := by
    ext i j
    rfl
  rw [matrix_map, matrix_map] at mapped
  rw [mapped]
  rfl

theorem source_n3_arm_read_fraction (fieldEvent detector source : DressedEvent)
    (epsilon sigma : ℝ) (n : PhysicalMomentum) (dLeg sLeg : CompositeLeg)
    (dPoles : N3SourceEnergyPoleSection detector.momentum dLeg)
    (sPoles : N3SourceEnergyPoleSection source.momentum sLeg) (dEM sEM : Bool)
    (positive : 0 < sigma) (regular : correctedDet fieldEvent epsilon 0 sigma n ≠ 0) :
    sourceN3ArmRead fieldEvent detector source epsilon sigma n dLeg sLeg dPoles sPoles dEM sEM =
      MvPolynomial.eval (irValues epsilon sigma 0)
        (sourceN3ArmNumerator fieldEvent detector source n dLeg sLeg dPoles sPoles dEM sEM) /
      MvPolynomial.eval (irValues epsilon sigma 0) (commonDeterminant fieldEvent n) := by
  apply (eq_div_iff (actual_common_determinant_nonzero fieldEvent epsilon sigma 0 n positive regular)).mpr
  rw [mul_comm, source_n3_arm_numerator_eval]
  have green := actual_common_green_adjugate fieldEvent epsilon sigma 0 n positive regular
  rw [← source_prepared_full_green_original fieldEvent epsilon sigma n positive regular] at green
  have read := congrArg (fun G : Matrix (Fin 289) (Fin 289) ℂ =>
    emCurrentObservation G (sourceN3ArmCurrent detector dLeg dPoles dEM)
      (sourceN3ArmCurrent source sLeg sPoles sEM)) green
  simpa only [sourceN3ArmRead, emCurrentObservation, Matrix.smul_mulVec,
    dotProduct_smul, smul_eq_mul] using read

/-- The EM arm consumes the original Noether charge unit and coordinate Gram
once, while its cofactor still contains every mixing direction. -/
theorem source_n3_em_arm_noether_read (fieldEvent detector source : DressedEvent)
    (epsilon sigma : ℝ) (n : PhysicalMomentum) (dLeg sLeg : CompositeLeg)
    (dPoles : N3SourceEnergyPoleSection detector.momentum dLeg)
    (sPoles : N3SourceEnergyPoleSection source.momentum sLeg) (positive : 0 < sigma)
    (regular : correctedDet fieldEvent epsilon 0 sigma n ≠ 0) :
    sourceN3ArmRead fieldEvent detector source epsilon sigma n dLeg sLeg dPoles sPoles true true =
      dotProduct (physicalN3PoleNoetherCurrent detector dLeg dPoles)
        ((noetherPairScale^2 • sourcePreparedEMTensorRead fieldEvent epsilon sigma n) *ᵥ
          physicalN3PoleNoetherCurrent source sLeg sPoles) := by
  unfold sourceN3ArmRead
  rw [source_prepared_full_green_original fieldEvent epsilon sigma n positive regular,
    source_prepared_em_tensor_original fieldEvent epsilon sigma n positive regular]
  simp only [sourceN3ArmCurrent, ↓reduceIte]
  rw [em_pure_response_tensor]
  unfold emPureObservation
  rw [physical_n3_pole_coordinate_noether_unit, physical_n3_pole_coordinate_noether_unit]
  rw [correctedEMTensor.eq_def]
  simp only [Matrix.mulVec_smul, Matrix.smul_mulVec, smul_dotProduct, dotProduct_smul, smul_eq_mul]
  ring

end LowEnergy.GaussComposite.ActualSourcePreparedN3EMIRSplit
