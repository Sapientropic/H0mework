import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualSourcePreparedMovingNoetherResolvent
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedCommonIRResponse

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualSourcePreparedMovingMaterialCarrier
open GaussCoreHilbert CanonicalGradedSpatialSource PreparationVacuumMixedFieldReturn
open PreparationVacuumPhysicalFeedback PreparationVacuumJointFieldResponse PreparationVacuumRawJointFeedback
open PreparationVacuumNoetherChart PreparationVacuumCurrentSignalOperator PreparationVacuumPropagationPencil
open SourcePropagationResolvent SourcePropagationAlgebraicResponse PreparationVacuumPhysicalPoleSheet
open ActualDressedFullCoulomb ActualDressedNoether ActualDressedSylvester ActualDressedStaticResponse
open ActualDressedUniformMaterialCoefficients ActualDressedPhysicalRayNumerator
open scoped Matrix BigOperators
private abbrev SourceOp := SourcePropagationResolvent.Op
local instance : NormedAlgebra ℝ SourceOp := NormedAlgebra.restrictScalars ℝ ℂ _
@[instance_reducible] private def coefficientRing {A : Type*} [Ring A] [Algebra ℂ A] :
    Ring (CoefficientAlgebra A) := inferInstance
local instance : Ring ParameterOp := coefficientRing (A:=ActualDressedUniformMaterialCoefficients.Op)
local instance : AddCommGroup ParameterOp := (inferInstance : Ring ParameterOp).toAddCommGroup
local instance : AddGroup ParameterOp := (inferInstance : AddCommGroup ParameterOp).toAddGroup
attribute [local irreducible] jointResolvent jointCurrent rawReader sourceInverse

private theorem initial_join {R : Type*} [Ring R] (L V JL JR B C D : R) :
    -(L*JL*L)*B*V+L*C*V+L*B*(-(V*JR*V))+L*(D-C)*V =
      (-L)*JL*(L*B*V)+(L*B*V)*JR*(-V)+L*D*V := by noncomm_ring

/-- The raw contact in the original slope cancels its original subtraction,
leaving the actual Noether Frechet contact beside both material current legs. -/
theorem source_moving_noether_initial_join (q : PhysicalResponsePoint) (reader force : Field289) :
    noetherStaticInitial q reader force=sourceMaterialMap q reader force+sourceContactMap q reader force := by
  change -(jointResolvent (q.p+q.k) q.F q.z 0*jointCurrent (q.p+q.k) q.F q.z 0 force*
      jointResolvent (q.p+q.k) q.F q.z 0)*rawReader reader q.p q.F 0*jointResolvent q.p q.F q.w 0+
    jointResolvent (q.p+q.k) q.F q.z 0*rawReaderContact reader force q.p q.F*jointResolvent q.p q.F q.w 0+
    jointResolvent (q.p+q.k) q.F q.z 0*rawReader reader q.p q.F 0*
      (-(jointResolvent q.p q.F q.w 0*jointCurrent q.p q.F q.w 0 force*jointResolvent q.p q.F q.w 0))+
    jointResolvent (q.p+q.k) q.F q.z 0*
      (fderiv ℝ (noetherReader reader q.p q.F) 0 force-rawReaderContact reader force q.p q.F)*
        jointResolvent q.p q.F q.w 0 = _
  exact initial_join _ _ _ _ _ _ _

private theorem clear_raw {A : Type*} [Ring A] [Algebra ℂ A]
    (L R KL KR J : A) (dl dr : ℂ) (left : dl • L=KL) (right : dr • R=KR) :
    (dl^2*dr^2) • (L*J*R)=(dl*dr) • (KL*J*KR) := by
  rw [←left,←right]
  simp only [smul_mul_assoc,mul_smul_comm,smul_smul,pow_two]
  congr 1; ring

private theorem clear_material {A : Type*} [Ring A] [Algebra ℂ A]
    (L R KL KR J JL JR : A) (dl dr : ℂ) (left : dl • L=KL) (right : dr • R=KR) :
    (dl^2*dr^2) • ((-L)*JL*(L*J*R)+(L*J*R)*JR*(-R))=
      -dr • (KL*JL*KL*J*KR)-dl • (KL*J*KR*JR*KR) := by
  rw [←left,←right]
  simp only [smul_mul_assoc,mul_smul_comm,smul_smul,smul_add,smul_neg,neg_mul,mul_neg,mul_assoc,pow_two]
  module

private theorem material_data (event : DressedEvent) (n : PhysicalMomentum) (eps sigma s : ℝ)
    (reader force : Field289) :
    coefficientEval (irValues eps sigma s) (materialFullNumerator event n reader force)=
      MvPolynomial.eval (irValues eps sigma s) (materialDenominator event n) •
        sourceMaterialMap (dressedKinematicPoint event (eps^2 • n)) reader force ∧
    coefficientEval (irValues eps sigma s) (materialContactNumerator event n reader force)=
      MvPolynomial.eval (irValues eps sigma s) (materialDenominator event n) •
        sourceContactMap (dressedKinematicPoint event (eps^2 • n)) reader force ∧
    coefficientEval (irValues eps sigma s) (materialRawNumerator event n reader)=
      MvPolynomial.eval (irValues eps sigma s) (materialDenominator event n) •
        rawInitial (dressedKinematicPoint event (eps^2 • n)) reader := by
  let p:=event.momentum-eps^2 • n
  let L:=jointResolvent p event.frame event.energy 0
  let R:=jointResolvent event.momentum event.frame event.energy 0
  let KL:=materialJointNumerator p event.frame event.energy
  let KR:=materialJointNumerator event.momentum event.frame event.energy
  let dl:=(jointPolynomial p event.frame).eval event.energy
  let dr:=(jointPolynomial event.momentum event.frame).eval event.energy
  have left : dl • L=KL:=actual_material_joint_inverse_clear p event.frame event.energy event.nonreal
  have right : dr • R=KR:=actual_material_joint_inverse_clear event.momentum event.frame event.energy event.nonreal
  have material : sourceMaterialMap (dressedKinematicPoint event (eps^2 • n)) reader force=
      (-L)*jointCurrent p event.frame event.energy 0 force*(L*rawReader reader event.momentum event.frame 0*R)+
        (L*rawReader reader event.momentum event.frame 0*R)*jointCurrent event.momentum event.frame event.energy 0 force*(-R) := by
    unfold sourceMaterialMap dressedKinematicPoint; rfl
  have contact : sourceContactMap (dressedKinematicPoint event (eps^2 • n)) reader force=
      L*fderiv ℝ (noetherReader reader event.momentum event.frame) 0 force*R := by
    unfold sourceContactMap dressedKinematicPoint; rfl
  have initial : rawInitial (dressedKinematicPoint event (eps^2 • n)) reader=L*rawReader reader event.momentum event.frame 0*R := by
    unfold rawInitial dressedKinematicPoint; rfl
  simp only [materialFullNumerator,materialContactNumerator,materialRawNumerator,map_sub,map_neg,map_mul,
    coefficient_eval_smul,left_material_denominator_eval,rightMaterialDenominator,MvPolynomial.eval_C,
    common_material_left_eval,common_left_current_eval,constantOp,coefficient_eval_constant,rightMaterialNumerator,
    materialDenominator,map_pow,material,contact,initial]
  constructor
  · exact (clear_material L R KL KR _ _ _ dl dr left right).symm
  exact ⟨(clear_raw L R KL KR _ dl dr left right).symm,(clear_raw L R KL KR _ dl dr left right).symm⟩

theorem source_moving_material_initial_clear (event : DressedEvent) (eps sigma s : ℝ)
    (n : PhysicalMomentum) (reader force : Field289) :
    coefficientEval (irValues eps sigma s)
      (materialFullNumerator event n reader force+materialContactNumerator event n reader force) =
        MvPolynomial.eval (irValues eps sigma s) (materialDenominator event n) •
          noetherStaticInitial (dressedKinematicPoint event (eps^2 • n)) reader force := by
  have data := material_data event n eps sigma s reader force
  rw [map_add, data.1, data.2.1, source_moving_noether_initial_join]
  with_reducible_and_instances exact (smul_add _ _ _).symm

theorem source_moving_material_raw_clear (event : DressedEvent) (eps sigma s : ℝ)
    (n : PhysicalMomentum) (reader force : Field289) :
    coefficientEval (irValues eps sigma s) (materialRawNumerator event n reader) =
      MvPolynomial.eval (irValues eps sigma s) (materialDenominator event n) •
        rawInitial (dressedKinematicPoint event (eps^2 • n)) reader :=
  (material_data event n eps sigma s reader force).2.2

private theorem cleared_return {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (R D : E →L[ℂ] E) (M A N B : E) (d : ℂ) (positive : d≠0)
    (material : N=d • M) (raw : B=d • A) :
    R (M+D (R A)) = d⁻¹ • R (N+D (R B)) := by
  rw [material, raw]
  simp only [map_smul, ←smul_add, smul_smul, inv_mul_cancel₀ positive, one_smul]

/-- The same original full Noether word consumes the finite material/contact
and raw numerators, with the actual nonreal-energy denominator paid by source. -/
theorem source_moving_noether_material_return (event : DressedEvent) (eps sigma s : ℝ)
    (n : PhysicalMomentum) (lambda : ℂ) (reader force : Field289) :
    let q := dressedKinematicPoint event (eps^2 • n)
    let v := irValues eps sigma s
    let d := MvPolynomial.eval v (materialDenominator event n)
    sourceInverse q lambda (noetherStaticInitial q reader force+driveOperator q force
      (sourceInverse q lambda (rawInitial q reader))) =
        d⁻¹ • sourceInverse q lambda
          (coefficientEval v (materialFullNumerator event n reader force+materialContactNumerator event n reader force)+
            driveOperator q force (sourceInverse q lambda (coefficientEval v (materialRawNumerator event n reader)))) := by
  exact cleared_return _ _ _ _ _ _ _ (material_denominator_nonzero event n eps sigma s)
    (source_moving_material_initial_clear event eps sigma s n reader force)
    (source_moving_material_raw_clear event eps sigma s n reader force)


private theorem original_noether_join (q : PhysicalResponsePoint) (lambda : ℂ) (reader force : Field289) :
    noetherStaticInitial q reader force-leftCurrent q force*sourceInverse q lambda (rawInitial q reader)+
      sourceInverse q lambda (rawInitial q reader)*rightCurrent q force =
        noetherStaticInitial q reader force+driveOperator q force (sourceInverse q lambda (rawInitial q reader)) := by
  rw [driveOperator_apply]
  abel

set_option backward.isDefEq.respectTransparency true in
/-- The original full polarization directly consumes the same finite material,
contact and raw carrier; the source observer is applied after their joined return. -/
theorem source_moving_polarization_material_return (event : DressedEvent) (eps sigma s : ℝ)
    (n : PhysicalMomentum) (lambda : ℂ) (positive : 0 < lambda.re) (i j : Fin 289) :
    let q := dressedKinematicPoint event (eps^2 • n)
    let v := irValues eps sigma s
    let d := MvPolynomial.eval v (materialDenominator event n)
    dressedStaticPolarization event (eps^2 • n) lambda i j =
      d⁻¹*dressedEulerObserver event (sourceInverse q lambda
        (coefficientEval v (materialFullNumerator event n (PreparationVacuumActionFieldLift.fieldUnit i)
          (PreparationVacuumActionFieldLift.fieldUnit j)+materialContactNumerator event n
            (PreparationVacuumActionFieldLift.fieldUnit i) (PreparationVacuumActionFieldLift.fieldUnit j))+
          driveOperator q (PreparationVacuumActionFieldLift.fieldUnit j) (sourceInverse q lambda
            (coefficientEval v (materialRawNumerator event n (PreparationVacuumActionFieldLift.fieldUnit i)))))) := by
  have original := dressed_static_polarization_inverse event (eps^2 • n) lambda positive i j
  have joined := congrArg (fun A : SourceOp => dressedEulerObserver event
    (sourceInverse (dressedKinematicPoint event (eps^2 • n)) lambda A))
      (original_noether_join (dressedKinematicPoint event (eps^2 • n)) lambda
        (PreparationVacuumActionFieldLift.fieldUnit i) (PreparationVacuumActionFieldLift.fieldUnit j))
  have cleared := congrArg (dressedEulerObserver event)
    (source_moving_noether_material_return event eps sigma s n lambda
      (PreparationVacuumActionFieldLift.fieldUnit i) (PreparationVacuumActionFieldLift.fieldUnit j))
  refine (original.trans (joined.trans cleared)).trans ?_
  exact (dressedEulerObserver event).map_smul _ _

end LowEnergy.GaussComposite.ActualSourcePreparedMovingMaterialCarrier
