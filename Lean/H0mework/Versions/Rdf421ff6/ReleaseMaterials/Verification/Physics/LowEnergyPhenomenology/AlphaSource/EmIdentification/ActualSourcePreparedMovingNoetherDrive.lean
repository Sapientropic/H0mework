import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualSourcePreparedMovingNoetherResolvent
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedCommonIRResponse

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency true
noncomputable section
namespace LowEnergy.GaussComposite.ActualSourcePreparedMovingNoetherDrive
open CanonicalGradedSpatialSource GaussCoreHilbert PreparationVacuumMixedFieldReturn
open PreparationVacuumPhysicalFeedback PreparationVacuumJointFieldResponse PreparationVacuumPropagationPencil
open SourcePropagationResolvent ActualDressedUniformMaterialCoefficients
open PreparationVacuumActionFieldLift PreparationVacuumPhysicalCharacteristic
open ActualDressedFullCoulomb ActualDressedNoether ActualDressedSylvester ActualDressedStaticResponse
open ActualSourcePreparedNoetherPi ActualSourcePreparedN3MovingResponse ActualSourcePreparedTemporalQuantumWard
open ActualSourcePreparedTemporalQuantumIR ActualSourcePreparedMovingNoetherResolvent ActualEMJointCurrentMomentum
open scoped Matrix BigOperators
private abbrev SourceOp := SourcePropagationResolvent.Op
local instance : NormedAlgebra ℝ SourceOp := NormedAlgebra.restrictScalars ℝ ℂ _
attribute [local irreducible] sourceInverse jointCurrent jointCurrentMomentum dressedStaticPolarization

private theorem left_change {E : Type*} [AddCommGroup E] [Module ℂ E]
    (B U : E) (eps : ℝ) :
    (-Complex.I) • (B-((eps^2:ℝ):ℂ) • U)-(-Complex.I) • B =
      -((-Complex.I*(eps:ℂ)^2) • U) := by
  simp only [smul_sub, smul_smul, Complex.ofReal_pow]
  module

def sourceMovingCurrentInsertion (event : DressedEvent) (n : PhysicalMomentum) (force : Field289) : SourceOp :=
  jointCurrent n event.frame 0 0 force-jointCurrent 0 event.frame 0 0 force

theorem source_moving_left_current_update (event : DressedEvent) (eps : ℝ)
    (n : PhysicalMomentum) (force : Field289) :
    leftCurrent (dressedKinematicPoint event (eps^2 • n)) force-
      leftCurrent (dressedKinematicPoint event 0) force =
        -((-Complex.I*(eps:ℂ)^2) • sourceMovingCurrentInsertion event n force) := by
  have momentum := actual_moving_current_affine event.momentum n event.frame 0 (eps^2) force
  have original : leftCurrent (dressedKinematicPoint event (eps^2 • n)) force-
      leftCurrent (dressedKinematicPoint event 0) force =
        (-Complex.I) • (jointCurrent event.momentum event.frame 0 0 force-
          ((eps^2:ℝ):ℂ) • sourceMovingCurrentInsertion event n force)-
          (-Complex.I) • jointCurrent event.momentum event.frame 0 0 force := by
    change (-Complex.I) • jointCurrent (event.momentum+ -(eps^2 • n)) event.frame 0 0 force-
      (-Complex.I) • jointCurrent (event.momentum+ -0) event.frame 0 0 force = _
    simp only [neg_zero, add_zero, ←sub_eq_add_neg]
    exact congrArg (fun B : SourceOp => (-Complex.I) • B-
      (-Complex.I) • jointCurrent event.momentum event.frame 0 0 force) momentum
  exact original.trans (left_change _ _ eps)

theorem source_moving_right_current_fixed (event : DressedEvent) (eps : ℝ)
    (n : PhysicalMomentum) (force : Field289) :
    rightCurrent (dressedKinematicPoint event (eps^2 • n)) force =
      rightCurrent (dressedKinematicPoint event 0) force := rfl

def sourceMovingDriveInsertion (event : DressedEvent) (n : PhysicalMomentum) (force : Field289) :
    SourceOp →L[ℂ] SourceOp := ContinuousLinearMap.mul ℂ SourceOp (sourceMovingCurrentInsertion event n force)

private theorem drive_change {R : Type*} [Ring R] [Algebra ℂ R]
    (L B T U A : R) (z : ℂ) (left : L=B+ -(z • U)) :
    -(L*A)+A*T=-(B*A)+A*T+z • (U*A) := by
  rw [left]
  simp only [add_mul, neg_mul, neg_add_rev, neg_neg, smul_mul_assoc]
  abel

theorem source_moving_drive_update (event : DressedEvent) (eps : ℝ)
    (n : PhysicalMomentum) (force : Field289) :
    driveOperator (dressedKinematicPoint event (eps^2 • n)) force =
      driveOperator (dressedKinematicPoint event 0) force+
        (-Complex.I*(eps:ℂ)^2) • sourceMovingDriveInsertion event n force := by
  apply ContinuousLinearMap.ext
  intro A
  have left := sub_eq_iff_eq_add'.mp (source_moving_left_current_update event eps n force)
  simp only [driveOperator_apply, source_moving_right_current_fixed,
    add_apply, smul_apply, sourceMovingDriveInsertion, ContinuousLinearMap.mul_apply']
  exact drive_change _ _ _ _ _ _ left

private theorem cubic_update {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (R S K D F L : E →L[ℂ] E) (M A : E) (z : ℂ)
    (propagation : R=S+z • K) (drive : D=F+z • L) :
    R (M+D (R A)) = S M+S (F (S A))+
      z • (K M+K (F (S A))+S (F (K A))+S (L (S A)))+
      z^2 • (K (F (K A))+K (L (S A))+S (L (K A)))+z^3 • K (L (K A)) := by
  rw [propagation, drive]
  simp only [add_apply, smul_apply, map_add, map_smul, smul_add, smul_smul, pow_two,
    show z^3=z*z*z by ring]
  module

def sourceMovingFullNoetherCoefficients (event : DressedEvent) (eps : ℝ) (n : PhysicalMomentum)
    (lambda : ℂ) (reader force : Field289) : Fin 4 → ResponseOp :=
  let q := dressedKinematicPoint event (eps^2 • n)
  let R := sourceInverse (dressedKinematicPoint event 0) lambda
  let K := sourceMovingResolventCorrection event eps n lambda
  let D := driveOperator (dressedKinematicPoint event 0) force
  let L := sourceMovingDriveInsertion event n force
  let A := rawInitial q reader
  let M := noetherStaticInitial q reader force
  ![R M+R (D (R A)), K M+K (D (R A))+R (D (K A))+R (L (R A)),
    K (D (K A))+K (L (R A))+R (L (K A)), K (L (K A))]

/-- Both resolvent changes and the actual drive insertion enter the complete
Noether word. Material/contact and raw compression retain their moving values. -/
theorem source_moving_full_noether_update (event : DressedEvent) (eps : ℝ) (n : PhysicalMomentum)
    (lambda : ℂ) (positive : 0 < lambda.re) (reader force : Field289) :
    let q := dressedKinematicPoint event (eps^2 • n)
    let C := sourceMovingFullNoetherCoefficients event eps n lambda reader force
    let z := -Complex.I*(eps:ℂ)^2
    sourceInverse q lambda (noetherStaticInitial q reader force+
      driveOperator q force (sourceInverse q lambda (rawInitial q reader))) =
        C 0+z • C 1+z^2 • C 2+z^3 • C 3 :=
  cubic_update _ _ _ _ _ _ _ _ _ (source_moving_resolvent_update event eps n lambda positive)
    (source_moving_drive_update event eps n force)

def sourceMovingFullPolarizationCoefficients (event : DressedEvent) (eps : ℝ) (n : PhysicalMomentum)
    (lambda : ℂ) (k : Fin 4) : Matrix (Fin 289) (Fin 289) ℂ :=
  fun i j => dressedEulerObserver event
    (sourceMovingFullNoetherCoefficients event eps n lambda (fieldUnit i) (fieldUnit j) k)

theorem source_moving_full_polarization_update (event : DressedEvent) (eps : ℝ) (n : PhysicalMomentum)
    (lambda : ℂ) (positive : 0 < lambda.re) :
    let C := sourceMovingFullPolarizationCoefficients event eps n lambda
    let z := -Complex.I*(eps:ℂ)^2
    dressedStaticPolarization event (eps^2 • n) lambda = C 0+z • C 1+z^2 • C 2+z^3 • C 3 := by
  ext i j
  rw [dressed_static_polarization_inverse event (eps^2 • n) lambda positive i j]
  have original : noetherStaticInitial (dressedKinematicPoint event (eps^2 • n)) (fieldUnit i) (fieldUnit j)-
      leftCurrent (dressedKinematicPoint event (eps^2 • n)) (fieldUnit j)*
        sourceInverse (dressedKinematicPoint event (eps^2 • n)) lambda
          (rawInitial (dressedKinematicPoint event (eps^2 • n)) (fieldUnit i))+
      sourceInverse (dressedKinematicPoint event (eps^2 • n)) lambda
          (rawInitial (dressedKinematicPoint event (eps^2 • n)) (fieldUnit i))*
            rightCurrent (dressedKinematicPoint event (eps^2 • n)) (fieldUnit j) =
      noetherStaticInitial (dressedKinematicPoint event (eps^2 • n)) (fieldUnit i) (fieldUnit j)+
        driveOperator (dressedKinematicPoint event (eps^2 • n)) (fieldUnit j)
          (sourceInverse (dressedKinematicPoint event (eps^2 • n)) lambda
            (rawInitial (dressedKinematicPoint event (eps^2 • n)) (fieldUnit i))) := by
    rw [driveOperator_apply]; abel
  rw [original, source_moving_full_noether_update event eps n lambda positive]
  simp only [map_add, map_smul, smul_eq_mul, Matrix.add_apply, Matrix.smul_apply,
    sourceMovingFullPolarizationCoefficients]

theorem source_moving_full_actual_driver_update (event : DressedEvent) (e : scaleDomain)
    (sigma : ℝ) (positive : 0 < sigma) (n : PhysicalMomentum) :
    let C := sourceMovingFullPolarizationCoefficients event e.val n (sigma:ℂ)
    let a := sourceTemporalCorrectedField event e.val sigma n
    let z := -Complex.I*(e.val:ℂ)^2
    sourceTemporalActualQuantumDriver event e sigma n = (sigma:ℂ) •
      (C 0*ᵥa+z • (C 1*ᵥa)+z^2 • (C 2*ᵥa)+z^3 • (C 3*ᵥa)) := by
  have clock : 0 < (sigma:ℂ).re := by simpa only [Complex.ofReal_re] using positive
  have same : Matrix.of (fun i j => sourcePreparedPiEntry event (e.val^2 • n) (sigma:ℂ) i j) =
      dressedStaticPolarization event (e.val^2 • n) (sigma:ℂ) := by
    ext i j; exact source_prepared_pi_actual event _ _ clock i j
  simp only [sourceTemporalActualQuantumDriver, sourcePreparedClockQuantumMatrix, same,
    source_moving_full_polarization_update event e.val n (sigma:ℂ) clock,
    Matrix.smul_mulVec, Matrix.add_mulVec]

end LowEnergy.GaussComposite.ActualSourcePreparedMovingNoetherDrive
