import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationSourceMaterialPoleAmputation

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumPhysicalPoleAmputation
open SaturationMonoid.PhysicsCore ProofFreeRicherAnholonomicSource
open CanonicalGradedSpatialSource PreparationVacuumElectromagneticIdentity
open PreparationVacuumPhysicalPoleLegDynamics PreparationVacuumPhysicalPoleHalfResponse
open PreparationVacuumMovingPoleGaussReturn PreparationVacuumPhysicalFeedback
open PreparationVacuumPhysicalCurrentLaplaceReturn PreparationVacuumFixedMomentumActionReturn
open PreparationVacuumJointFieldResponse PreparationVacuumIndependentMomentumReturn
open PreparationVacuumRawJointFeedback PreparationVacuumMixedFieldReturn PreparationVacuumActionFieldLift
open PreparationVacuumFieldConstraintResponse SourcePropagationNativeActionHessian
open SourceFiniteUnitary GaussCoreHilbert GaussFockLift GaussQuantumMultiplier
open Stage9C.Material.SpinPair SU7MotherLieAlgebra StageNineHolonomicField
open Stage10 PreparationCoordinates PreparationVacuumLowerClassical
open SaturationMonoid.PhysicsCore.LowEnergy Electromagnetic.ExternalState
open scoped Topology InnerProductSpace BigOperators Matrix
attribute [local irreducible] jointGenerator jointResolvent sourcePolePrepared sourcePoleDual
  sourcePoleColumnDefect sourcePoleDualDefect sourceMovingIndependentReader sourcePoleGaugeRead
  sourcePhysicalCurrentAmplitude sourcePoleEulerInitial

def sourceBarePoleVertex (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (left right : RestStateIndex) (reader : Field289) : ℂ:=
  sourcePoleDual q.epsilon q.precision pL left
    (sourceMovingIndependentReader reader pR q.F 0 (sourcePolePrepared q.epsilon q.precision pR right))

theorem sourceBarePoleVertex_action (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (left right : RestStateIndex) (reader : Field289) :
    sourceBarePoleVertex q pL pR left right reader=
      sourcePoleDual q.epsilon q.precision pL left
        ((fderiv ℝ (sourceMatterActionOperator pR q.F) 0 reader) (sourcePolePrepared q.epsilon q.precision pR right)) :=by
  rw [sourceMatterActionOperator_gradient,sourceBarePoleVertex,sourceMovingIndependentReader_source]

def sourceAmputatedPoleVertex (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (left right : RestStateIndex) (reader : Field289) : ℂ:=
  sourcePoleAmputatedDual q.epsilon q.precision pL left q.F q.z
    (sourceMovingIndependentReader reader pR q.F 0
      (sourcePoleAmputatedPrimal q.epsilon q.precision pR right q.F q.w))

def sourcePoleVertexLegCorrection (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (left right : RestStateIndex) (reader : Field289) : ℂ:=
  let primalError:=jointResolvent pR q.F q.w 0 (sourcePoleColumnDefect q.epsilon q.precision pR right q.F)
  let dualError:=(sourcePoleDualDefect q.epsilon q.precision pL left q.F).comp (jointResolvent pL q.F q.z 0)
  let J:=sourceMovingIndependentReader reader pR q.F 0;
  -(sourcePoleDual q.epsilon q.precision pL left (J primalError))-
    dualError (J (sourcePolePrepared q.epsilon q.precision pR right))+
      dualError (J primalError)

theorem sourceAmputatedPoleVertex_generated (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (left right : RestStateIndex) (reader : Field289) :
    sourceAmputatedPoleVertex q pL pR left right reader=
      sourceBarePoleVertex q pL pR left right reader+sourcePoleVertexLegCorrection q pL pR left right reader :=by
  simp only [sourceAmputatedPoleVertex,sourcePoleAmputatedDual,sourcePoleAmputatedPrimal,
    sourceBarePoleVertex,sourcePoleVertexLegCorrection,sub_apply,map_sub,ContinuousLinearMap.comp_apply]
  ring

theorem sourcePoleInitial_material_return (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (left right : RestStateIndex) (i : Fin 289) :
    sourcePoleEulerInitial q pL pR left right i=
      -((sourcePoleDual q.epsilon q.precision pL left).comp (jointResolvent pL q.F q.z 0))
        (sourceMovingIndependentReader (fieldUnit i) pR q.F 0
          (jointResolvent pR q.F q.w 0 (sourcePolePrepared q.epsilon q.precision pR right))) :=by
  have initial : sourcePoleActionInsertion q pL pR left right (fieldUnit i) 0 0=
      sourcePolePreparedDensity q.epsilon q.precision pL pR left right
        (sourcePhysicalMaterialPoint q pL pR) (fieldUnit i) 0 0 :=
    (sourcePoleActionInsertion_near q pL pR left right (fieldUnit i) 0).self_of_nhds
  rw [sourcePoleEulerInitial,sourcePoleActionEuler,initial,sourcePolePreparedDensity,
    sourcePoleIndependentDual,sourcePolePreparedPrimal,sourcePhysicalMaterialPoint_left]
  simp only [sourcePhysicalMaterialPoint,physicalTime,neg_zero,time_zero,one_apply_eq_self,
    ContinuousLinearMap.comp_apply]
  rw [sourcePoleDual]

def sourcePoleMaterialPairGap (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (left right : RestStateIndex) : ℂ:=
  ((sourceMovingPoleEnergy pL left:ℂ)-q.z)*((sourceMovingPoleEnergy pR right:ℂ)-q.w)

theorem sourcePoleInitial_amputated (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (left right : RestStateIndex) (nonrealL : q.z.im≠0) (nonrealR : q.w.im≠0) (i : Fin 289) :
    sourcePoleEulerInitial q pL pR left right i=
      -(sourcePoleMaterialPairGap q pL pR left right)⁻¹*
        sourceAmputatedPoleVertex q pL pR left right (fieldUnit i) :=by
  rw [sourcePoleInitial_material_return,
    sourcePoleDual_resolvent_return q.epsilon q.precision pL left q.F q.z nonrealL,
    sourcePolePrimal_resolvent_return q.epsilon q.precision pR right q.F q.w nonrealR]
  simp only [sourceAmputatedPoleVertex,smul_apply,map_smul,smul_eq_mul,
    sourcePoleMaterialPairGap,mul_inv_rev]
  ring

/-- The original normalized full504 gauge reader, on the same original raw gauge direction. -/
def sourceCanonicalGaugeOperator (mu : Fin 4) (a : Fin 12) : H→L[ℂ] H:=
  (4*(spinScale:ℂ)) • lift (quantized (sourcePoleGaugeMatrix mu (p286CoordinateEquiv.symm (originalUnit a))))

theorem sourceCanonicalGaugeVertex_wave (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (left right : RestStateIndex) (mu : Fin 4) (a : Fin 12) :
    sourcePoleDual q.epsilon q.precision pL left
        (sourceCanonicalGaugeOperator mu a (sourcePolePrepared q.epsilon q.precision pR right))=
      sourcePhysicalCurrentAmplitude pL pR left right (gaugeSlot mu a) :=by
  have canonical:=sourcePoleGaugeRead_vertex q.epsilon q.precision pL pR left right mu
    (p286CoordinateEquiv.symm (originalUnit a))
  have original : sourcePhysicalCurrentAmplitude pL pR left right (gaugeSlot mu a)=
      (ActionNormalization.phaseMomentum:ℂ)*sourceMovingGaugeVertex mu
        (p286CoordinateEquiv.symm (originalUnit a)) pL pR left right :=by
    unfold sourcePhysicalCurrentAmplitude
    exact actualMovingNativeForcing_slot 0 pL pR left right mu a
  rw [sourcePoleDual,sourceCanonicalGaugeOperator,smul_apply,innerSL_apply_apply,inner_smul_right]
  rw [sourcePoleGaugeRead] at canonical
  exact canonical.trans original.symm

/-- Source weighted weak-action/Riesz remainder; the actual gauge slot is fixed at both ends. -/
def sourceGaugeReaderRemainder (q : PhysicalResponsePoint) (pR : PhysicalMomentum)
    (mu : Fin 4) (a : Fin 12) : H→L[ℂ] H:=
  sourceMovingIndependentReader (fieldUnit (gaugeSlot mu a)) pR q.F 0-sourceCanonicalGaugeOperator mu a

def sourceGaugeVertexRemainder (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (left right : RestStateIndex) (mu : Fin 4) (a : Fin 12) : ℂ:=
  sourcePoleDual q.epsilon q.precision pL left
    (sourceGaugeReaderRemainder q pR mu a (sourcePolePrepared q.epsilon q.precision pR right))

theorem sourceBareGaugeVertex_generated (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (left right : RestStateIndex) (mu : Fin 4) (a : Fin 12) :
    sourceBarePoleVertex q pL pR left right (fieldUnit (gaugeSlot mu a))=
      sourcePhysicalCurrentAmplitude pL pR left right (gaugeSlot mu a)+
        sourceGaugeVertexRemainder q pL pR left right mu a :=by
  rw [←sourceCanonicalGaugeVertex_wave q pL pR left right mu a]
  simp only [sourceBarePoleVertex,sourceGaugeVertexRemainder,sourceGaugeReaderRemainder,sub_apply,map_sub]
  ring

theorem sourceAmputatedGaugeVertex_generated (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (left right : RestStateIndex) (mu : Fin 4) (a : Fin 12) :
    sourceAmputatedPoleVertex q pL pR left right (fieldUnit (gaugeSlot mu a))=
      sourcePhysicalCurrentAmplitude pL pR left right (gaugeSlot mu a)+
        sourceGaugeVertexRemainder q pL pR left right mu a+
          sourcePoleVertexLegCorrection q pL pR left right (fieldUnit (gaugeSlot mu a)) :=by
  rw [sourceAmputatedPoleVertex_generated,sourceBareGaugeVertex_generated]

private theorem unitPairPrice {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (dual : E→L[ℂ] ℂ) (primal : E) (A : E→L[ℂ] E) (dualUnit : ‖dual‖=1) (primalUnit : ‖primal‖=1) :
    ‖dual (A primal)‖ ≤ ‖A‖ :=by
  have middle : ‖A primal‖ ≤ ‖A‖:=by simpa only [primalUnit,mul_one] using A.le_opNorm primal
  have first : ‖dual (A primal)‖ ≤ ‖A primal‖ :=by
    simpa only [dualUnit,one_mul] using dual.le_opNorm (A primal)
  exact first.trans middle

theorem sourceGaugeVertexRemainder_price (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (left right : RestStateIndex) (mu : Fin 4) (a : Fin 12) :
    ‖sourceGaugeVertexRemainder q pL pR left right mu a‖ ≤ ‖sourceGaugeReaderRemainder q pR mu a‖ :=by
  have dualUnit : ‖sourcePoleDual q.epsilon q.precision pL left‖=1 :=by
    rw [sourcePoleDual,innerSL_apply_norm,sourcePolePrepared_unit]
  exact unitPairPrice _ _ _ dualUnit (sourcePolePrepared_unit q.epsilon q.precision pR right)

theorem sourceGaugeReaderRemainder_action (q : PhysicalResponsePoint) (pR : PhysicalMomentum)
    (mu : Fin 4) (a : Fin 12) :
    sourceGaugeReaderRemainder q pR mu a=
      fderiv ℝ (sourceMatterActionOperator pR q.F) 0 (fieldUnit (gaugeSlot mu a))-sourceCanonicalGaugeOperator mu a :=by
  rw [sourceGaugeReaderRemainder,sourceMovingIndependentReader_source,sourceMatterActionOperator_gradient]

theorem sourceInitialGaugeEuler_normalized (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (left right : RestStateIndex) (nonrealL : q.z.im≠0) (nonrealR : q.w.im≠0) (mu : Fin 4) (a : Fin 12) :
    sourcePoleEulerInitial q pL pR left right (gaugeSlot mu a)=
      -(sourcePoleMaterialPairGap q pL pR left right)⁻¹*
        (sourcePhysicalCurrentAmplitude pL pR left right (gaugeSlot mu a)+
          sourceGaugeVertexRemainder q pL pR left right mu a+
            sourcePoleVertexLegCorrection q pL pR left right (fieldUnit (gaugeSlot mu a))) :=by
  rw [sourcePoleInitial_amputated q pL pR left right nonrealL nonrealR,sourceAmputatedGaugeVertex_generated]

private theorem threeDefectPrice {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (dual dualError : E→L[ℂ] ℂ) (primal primalError : E) (middle : E→L[ℂ] E)
    (D P : ℝ) (dualUnit : ‖dual‖=1) (primalUnit : ‖primal‖=1)
    (boundD : ‖dualError‖ ≤ D) (boundP : ‖primalError‖ ≤ P) :
    ‖-dual (middle primalError)-dualError (middle primal)+dualError (middle primalError)‖ ≤
      ‖middle‖*(P+D+D*P) :=by
  have pmiddle : ‖middle primal‖ ≤ ‖middle‖ :=by
    simpa only [primalUnit,mul_one] using middle.le_opNorm primal
  have error : ‖middle primalError‖ ≤ ‖middle‖*P:=
    (middle.le_opNorm primalError).trans (mul_le_mul_of_nonneg_left boundP (norm_nonneg _))
  have first : ‖dual (middle primalError)‖ ≤ ‖middle‖*P :=by
    have native:=dual.le_opNorm (middle primalError)
    rw [dualUnit,one_mul] at native
    exact native.trans error
  have second : ‖dualError (middle primal)‖ ≤ D*‖middle‖:=
    (dualError.le_opNorm _).trans (mul_le_mul boundD pmiddle (norm_nonneg _) ((norm_nonneg _).trans boundD))
  have third : ‖dualError (middle primalError)‖ ≤ D*(‖middle‖*P):=
    (dualError.le_opNorm _).trans (mul_le_mul boundD error (norm_nonneg _) ((norm_nonneg _).trans boundD))
  have price:=((norm_add_le (-dual (middle primalError)-dualError (middle primal))
    (dualError (middle primalError))).trans
      (add_le_add (norm_sub_le _ _) (le_refl _)))
  simp only [norm_neg] at price
  exact price.trans ((add_le_add (add_le_add first second) third).trans_eq (by ring))

def sourcePoleVertexLegPrice (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (left right : RestStateIndex) (reader : Field289) : ℝ:=
  let P:=‖jointResolvent pR q.F q.w 0‖*‖sourcePoleColumnDefect q.epsilon q.precision pR right q.F‖
  let D:=‖sourcePoleDualDefect q.epsilon q.precision pL left q.F‖*‖jointResolvent pL q.F q.z 0‖
  ‖sourceMovingIndependentReader reader pR q.F 0‖*(P+D+D*P)

theorem sourcePoleVertexLegCorrection_price (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (left right : RestStateIndex) (reader : Field289) :
    ‖sourcePoleVertexLegCorrection q pL pR left right reader‖ ≤ sourcePoleVertexLegPrice q pL pR left right reader :=by
  have dualUnit : ‖sourcePoleDual q.epsilon q.precision pL left‖=1 :=by
    rw [sourcePoleDual,innerSL_apply_norm,sourcePolePrepared_unit]
  exact threeDefectPrice _ _ _ _ _ _ _ dualUnit (sourcePolePrepared_unit q.epsilon q.precision pR right)
    (ContinuousLinearMap.opNorm_comp_le _ _) ((jointResolvent pR q.F q.w 0).le_opNorm _)

theorem sourceAmputatedGaugeVertex_price (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (left right : RestStateIndex) (mu : Fin 4) (a : Fin 12) :
    ‖sourceAmputatedPoleVertex q pL pR left right (fieldUnit (gaugeSlot mu a))-
        sourcePhysicalCurrentAmplitude pL pR left right (gaugeSlot mu a)‖ ≤
      ‖sourceGaugeReaderRemainder q pR mu a‖+
        sourcePoleVertexLegPrice q pL pR left right (fieldUnit (gaugeSlot mu a)) :=by
  rw [sourceAmputatedGaugeVertex_generated]
  have actual : sourcePhysicalCurrentAmplitude pL pR left right (gaugeSlot mu a)+
      sourceGaugeVertexRemainder q pL pR left right mu a+
      sourcePoleVertexLegCorrection q pL pR left right (fieldUnit (gaugeSlot mu a))-
      sourcePhysicalCurrentAmplitude pL pR left right (gaugeSlot mu a)=
        sourceGaugeVertexRemainder q pL pR left right mu a+
          sourcePoleVertexLegCorrection q pL pR left right (fieldUnit (gaugeSlot mu a)) :=by ring
  rw [actual]
  exact (norm_add_le _ _).trans (add_le_add (sourceGaugeVertexRemainder_price q pL pR left right mu a)
    (sourcePoleVertexLegCorrection_price q pL pR left right _))

end LowEnergy.PreparationVacuumPhysicalPoleAmputation
