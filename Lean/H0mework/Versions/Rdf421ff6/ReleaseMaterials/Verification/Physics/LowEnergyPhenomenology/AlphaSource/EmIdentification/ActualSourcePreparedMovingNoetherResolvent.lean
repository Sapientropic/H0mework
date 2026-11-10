import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualSourcePreparedQuantumDriverCofactor
import H0mework.Versions.R9c73a630.Physics.LowEnergy.AlphaSource.CanonicalSourcePropagationActualMomentumPencil

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency true
noncomputable section
namespace LowEnergy.GaussComposite.ActualSourcePreparedMovingNoetherResolvent
open CanonicalGradedSpatialSource GaussCoreHilbert PreparationVacuumMixedFieldReturn
open PreparationVacuumPhysicalFeedback PreparationVacuumRawJointFeedback PreparationVacuumJointFieldResponse
open PreparationVacuumActionFieldLift (fieldUnit)
open PreparationVacuumPhysicalCharacteristic (scaleDomain)
open PreparationVacuumPropagationPencil SourcePropagationResolvent
open SourcePropagationCommonMomentum
private abbrev SourceOp := SourcePropagationResolvent.Op
private abbrev SourceTransferOp := SourcePropagationResolvent.TransferOp
local instance : AddCommGroup SourceTransferOp := ContinuousLinearMap.addCommGroup
local instance : NormedAlgebra ℝ SourceOp := NormedAlgebra.restrictScalars ℝ ℂ _
local instance : IsScalarTower ℝ SourceOp SourceOp := ⟨by
  intro c A B
  apply ContinuousLinearMap.ext
  intro x
  rfl⟩
open ActualDressedFullCoulomb ActualDressedNoether ActualDressedSylvester ActualDressedStaticResponse
open ActualSourcePreparedNoetherPi ActualSourcePreparedN3MovingResponse
open ActualSourcePreparedTemporalQuantumWard ActualSourcePreparedTemporalQuantumIR
open scoped Matrix BigOperators
attribute [local irreducible] sourceInverse evolutionGenerator jointGenerator dressedStaticPolarization

private theorem point_transfer (event : DressedEvent) (eps : ℝ) (n : PhysicalMomentum) :
    dressedKinematicPoint event (eps^2 • n) =
      {dressedKinematicPoint event 0 with k := -(eps^2 • n)} := by
  rfl

private theorem generator_difference {R : Type*} [Ring R] [Module ℂ R] [IsScalarTower ℂ R R]
    (L M B A : R) :
    -((-Complex.I) • L)*A+A*((-Complex.I) • B)-
      (-((-Complex.I) • M)*A+A*((-Complex.I) • B)) = Complex.I • ((L-M)*A) := by
  simp only [neg_smul, neg_neg, smul_mul_assoc, sub_mul, smul_sub]
  module

private theorem complex_scale {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E] (e : ℝ) (v : E) :
    Complex.I • (-(e^2 • v)) = (-Complex.I*(e:ℂ)^2) • v := by
  rw [RCLike.real_smul_eq_coe_smul (K:=ℂ), smul_neg, smul_smul, ←neg_smul]
  apply congrArg (fun c : ℂ => c • v)
  change -(Complex.I * (Complex.ofReal (e^2))) = -Complex.I*(Complex.ofReal e)^2
  rw [Complex.ofReal_pow, neg_mul]

private theorem transfer_evolution_difference (q : PhysicalResponsePoint) (k : PhysicalMomentum) :
    evolutionGenerator {q with k := k}-evolutionGenerator {q with k := 0} =
      Complex.I • ContinuousLinearMap.mul ℂ SourceOp (momentumCompressionMap q.F k) := by
  apply ContinuousLinearMap.ext
  intro A
  have left := evolutionGenerator_apply {q with k := k} A
  have right := evolutionGenerator_apply {q with k := 0} A
  refine (congrArg₂ (fun X Y : SourceOp => X-Y) left right).trans ?_
  have at_zero := congrArg (fun p : PhysicalMomentum => jointGenerator p q.F 0 0) (add_zero q.p)
  have momentum := (congrArg (fun M : SourceOp => jointGenerator (q.p+k) q.F 0 0-M) at_zero).trans
    (jointGenerator_momentum_difference q.p k q.F 0)
  exact (generator_difference (jointGenerator (q.p+k) q.F 0 0)
    (jointGenerator (q.p+0) q.F 0 0) (jointGenerator q.p q.F 0 0) A).trans
      (congrArg (fun M : SourceOp => Complex.I • (M*A)) momentum)

/-- The whole propagation carrier changes by the original source momentum
action. No identity substitution or invariant finite-frame premise is used. -/
theorem source_moving_evolution_update (event : DressedEvent) (eps : ℝ) (n : PhysicalMomentum) :
    evolutionGenerator (dressedKinematicPoint event (eps^2 • n)) -
      evolutionGenerator (dressedKinematicPoint event 0) =
        (-Complex.I*(eps:ℂ)^2) • ContinuousLinearMap.mul ℂ SourceOp (momentumCompressionMap event.frame n) := by
  have actual := transfer_evolution_difference (dressedKinematicPoint event 0) (-(eps^2 • n))
  have base : {dressedKinematicPoint event 0 with k := 0} = dressedKinematicPoint event 0 := by
    simp only [dressedKinematicPoint, neg_zero]
  have alignment := congrArg₂ (fun P Q : PhysicalResponsePoint => evolutionGenerator P-evolutionGenerator Q)
    (point_transfer event eps n) base.symm
  refine (alignment.trans actual).trans ?_
  have moved := (map_neg (momentumCompressionMap event.frame) (eps^2 • n)).trans
    (congrArg (fun M : SourceOp => -M) (map_smul (momentumCompressionMap event.frame) (eps^2) n))
  have operators := congrArg (fun M : SourceOp => Complex.I • ContinuousLinearMap.mul ℂ SourceOp M) moved
  refine operators.trans ?_
  apply ContinuousLinearMap.ext
  intro A
  change Complex.I • ((-(eps^2 • momentumCompressionMap event.frame n))*A) =
    (-Complex.I*(eps:ℂ)^2) • (momentumCompressionMap event.frame n*A)
  have product : (-(eps^2 • momentumCompressionMap event.frame n))*A =
      -(eps^2 • (momentumCompressionMap event.frame n*A)) :=
    (neg_mul _ A).trans (congrArg (fun M : SourceOp => -M) (smul_mul_assoc (eps^2) _ A))
  exact (congrArg (fun M : SourceOp => Complex.I • M) product).trans (complex_scale eps _)

def sourceMovingResolventCorrection (event : DressedEvent) (eps : ℝ) (n : PhysicalMomentum)
    (lambda : ℂ) : SourceTransferOp :=
  sourceInverse (dressedKinematicPoint event (eps^2 • n)) lambda *
    ContinuousLinearMap.mul ℂ SourceOp (momentumCompressionMap event.frame n) *
      sourceInverse (dressedKinematicPoint event 0) lambda

private theorem inverse_difference {R : Type*} [Ring R] (P Q A B : R)
    (right : A*P=1) (left : Q*B=1) : A-B=A*(Q-P)*B := by
  calc
    _ = A*(Q*B)-(A*P)*B := by rw [right, left, mul_one, one_mul]
    _ = _ := by simp only [mul_sub, sub_mul, mul_assoc]

theorem source_moving_resolvent_update (event : DressedEvent) (eps : ℝ) (n : PhysicalMomentum)
    (lambda : ℂ) (positive : 0 < lambda.re) :
    sourceInverse (dressedKinematicPoint event (eps^2 • n)) lambda =
      sourceInverse (dressedKinematicPoint event 0) lambda +
        (-Complex.I*(eps:ℂ)^2) • sourceMovingResolventCorrection event eps n lambda := by
  have difference := inverse_difference
    (propagationPencil (dressedKinematicPoint event (eps^2 • n)) lambda)
    (propagationPencil (dressedKinematicPoint event 0) lambda)
    (sourceInverse (dressedKinematicPoint event (eps^2 • n)) lambda)
    (sourceInverse (dressedKinematicPoint event 0) lambda)
    (sourceInverse_right _ _ positive) (sourceInverse_left _ _ positive)
  have pencil : propagationPencil (dressedKinematicPoint event 0) lambda -
      propagationPencil (dressedKinematicPoint event (eps^2 • n)) lambda =
    evolutionGenerator (dressedKinematicPoint event (eps^2 • n)) -
      evolutionGenerator (dressedKinematicPoint event 0) := by
    unfold propagationPencil
    abel
  have aligned := congrArg (fun P : SourceTransferOp =>
    sourceInverse (dressedKinematicPoint event (eps^2 • n)) lambda * P *
      sourceInverse (dressedKinematicPoint event 0) lambda)
    (pencil.trans (source_moving_evolution_update event eps n))
  have scaled : sourceInverse (dressedKinematicPoint event (eps^2 • n)) lambda *
      ((-Complex.I*(eps:ℂ)^2) • ContinuousLinearMap.mul ℂ SourceOp (momentumCompressionMap event.frame n)) *
      sourceInverse (dressedKinematicPoint event 0) lambda =
        (-Complex.I*(eps:ℂ)^2) • sourceMovingResolventCorrection event eps n lambda := by
    apply ContinuousLinearMap.ext
    intro A
    simp only [sourceMovingResolventCorrection, mul_apply_eq_comp, smul_apply, map_smul]
  with_reducible_and_instances
    exact sub_eq_iff_eq_add'.mp ((difference.trans aligned).trans scaled)

def sourceMovingNoetherCoefficients (event : DressedEvent) (eps : ℝ) (n : PhysicalMomentum)
    (lambda : ℂ) (reader force : Field289) : Fin 3 → ResponseOp :=
  let q := dressedKinematicPoint event (eps^2 • n)
  let R := sourceInverse (dressedKinematicPoint event 0) lambda
  let K := sourceMovingResolventCorrection event eps n lambda
  let D := driveOperator q force
  let A := rawInitial q reader
  let M := noetherStaticInitial q reader force
  ![R M+R (D (R A)), K M+K (D (R A))+R (D (K A)), K (D (K A))]

private theorem noether_update {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (R S K D : E →L[ℂ] E) (M A : E) (z : ℂ) (update : R=S+z • K) :
    R (M+D (R A)) = S M+S (D (S A))+
      z • (K M+K (D (S A))+S (D (K A)))+z^2 • K (D (K A)) := by
  rw [update]
  simp only [add_apply, smul_apply, map_add, map_smul, smul_add, smul_smul, pow_two]
  module

/-- Complete moving material/contact and both drive insertions consume the
same propagation update. Their kinematic dependence remains in the coefficients. -/
theorem source_moving_noether_inverse_update (event : DressedEvent) (eps : ℝ) (n : PhysicalMomentum)
    (lambda : ℂ) (positive : 0 < lambda.re) (reader force : Field289) :
    let q := dressedKinematicPoint event (eps^2 • n)
    let A := sourceMovingNoetherCoefficients event eps n lambda reader force
    sourceInverse q lambda (noetherStaticInitial q reader force+
      driveOperator q force (sourceInverse q lambda (rawInitial q reader))) =
        A 0+(-Complex.I*(eps:ℂ)^2) • A 1+(-Complex.I*(eps:ℂ)^2)^2 • A 2 := by
  exact noether_update _ _ _ _ _ _ _ (source_moving_resolvent_update event eps n lambda positive)

def sourceMovingPolarizationCoefficients (event : DressedEvent) (eps : ℝ) (n : PhysicalMomentum)
    (lambda : ℂ) (k : Fin 3) : Matrix (Fin 289) (Fin 289) ℂ :=
  fun i j => dressedEulerObserver event
    (sourceMovingNoetherCoefficients event eps n lambda (fieldUnit i) (fieldUnit j) k)

theorem source_moving_polarization_update (event : DressedEvent) (eps : ℝ) (n : PhysicalMomentum)
    (lambda : ℂ) (positive : 0 < lambda.re) :
    dressedStaticPolarization event (eps^2 • n) lambda =
      sourceMovingPolarizationCoefficients event eps n lambda 0+
        (-Complex.I*(eps:ℂ)^2) • sourceMovingPolarizationCoefficients event eps n lambda 1+
          (-Complex.I*(eps:ℂ)^2)^2 • sourceMovingPolarizationCoefficients event eps n lambda 2 := by
  ext i j
  rw [dressed_static_polarization_inverse event (eps^2 • n) lambda positive i j]
  have original :
      noetherStaticInitial (dressedKinematicPoint event (eps^2 • n)) (fieldUnit i) (fieldUnit j) -
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
    rw [driveOperator_apply]
    abel
  rw [original, source_moving_noether_inverse_update event eps n lambda positive]
  simp only [map_add, map_smul, smul_eq_mul, Matrix.add_apply, Matrix.smul_apply,
    sourceMovingPolarizationCoefficients]

theorem source_moving_actual_quantum_driver_update (event : DressedEvent) (e : scaleDomain)
    (sigma : ℝ) (positive : 0 < sigma) (n : PhysicalMomentum) :
    let a := sourceTemporalCorrectedField event e.val sigma n
    let z := -Complex.I*(e.val:ℂ)^2
    sourceTemporalActualQuantumDriver event e sigma n = (sigma:ℂ) •
      (sourceMovingPolarizationCoefficients event e.val n (sigma:ℂ) 0*ᵥa+
        z • (sourceMovingPolarizationCoefficients event e.val n (sigma:ℂ) 1*ᵥa)+
          z^2 • (sourceMovingPolarizationCoefficients event e.val n (sigma:ℂ) 2*ᵥa)) := by
  have clock_positive : 0 < (sigma:ℂ).re := by simpa only [Complex.ofReal_re] using positive
  have same : Matrix.of (fun i j => sourcePreparedPiEntry event (e.val^2 • n) (sigma:ℂ) i j) =
      dressedStaticPolarization event (e.val^2 • n) (sigma:ℂ) := by
    ext i j
    exact source_prepared_pi_actual event _ _ clock_positive i j
  simp only [sourceTemporalActualQuantumDriver, sourcePreparedClockQuantumMatrix, same,
    source_moving_polarization_update event e.val n (sigma:ℂ) clock_positive,
    Matrix.smul_mulVec, Matrix.add_mulVec]

end LowEnergy.GaussComposite.ActualSourcePreparedMovingNoetherResolvent
