import H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.CanonicalSourcePropagationMovingTimeLegendre
import H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.CanonicalSourcePropagationPreparedHistoryResponse

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
noncomputable section
namespace LowEnergy.SourcePropagationNoetherTime
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open GaussCoreHilbert CanonicalGradedSpatialSource PreparationVacuumMixedFieldReturn
open PreparationVacuumPhysicalFeedback PreparationVacuumRawJointFeedback
open PreparationVacuumJointFieldResponse PreparationVacuumPropagationPencil
open PreparationVacuumNoetherChart PreparationVacuumOriginalDensity PreparationVacuumActionFieldLift
open PreparationVacuumGaugeSourceInjection PreparationVacuumSourceFieldFamily
open SourcePropagationTimeDependentFeedback
open Filter MeasureTheory
open scoped Topology BigOperators Matrix InnerProductSpace
abbrev Op:=SourcePropagationTimeDependentFeedback.Op
local instance : NormedAlgebra ℝ Op:=NormedAlgebra.restrictScalars ℝ ℂ _
attribute [local irreducible] jointResolvent rawReaderContact noetherReaderContact noetherReader physicalTime sourceRead
  preparedDual preparedPrimal noetherPreparedSlope densitySlope rawMomentumConnection

/-- The correction uses the same raw action, at fixed source canonical momentum. -/
theorem noetherCorrection_coefficient (reader force : Field289) (s : ActionState) (i : Fin 4) :
    noetherContactCoefficient reader force s i-
      densityActionMatrix*(densitySecond reader force s i+shellSecond reader force s i)=
      -rawTimeConnection s force*(densityActionMatrix*densityVariation reader s i):=by
  rw [rawTimeConnection_original]
  unfold noetherContactCoefficient
  simp only [sub_sub_cancel_left,neg_mul]

private def noetherCorrectionMap (reader : Field289) (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) :
    Field289→L[ℝ] Op:=fderiv ℝ (noetherReader reader p F) 0-fderiv ℝ (rawReader reader p F) 0

theorem noetherCorrectionMap_actual (reader force : Field289) (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) :
    noetherCorrectionMap reader p F force=noetherReaderContact reader force p F-rawReaderContact reader force p F:=by
  have differential:=(rawReader_C2 reader p F).differentiableAt (by norm_num) |>.hasFDerivAt
  have generated:=differential.comp_hasDerivAt_of_eq 0 (fieldRay_derivative force 0) (by simp)
  have raw:=generated.unique (rawReader_direction reader force p F)
  unfold noetherCorrectionMap noetherReaderContact
  rw [sub_apply,raw]

private def correctionJet (reader : Field289) (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index)
    (signal : SourceJet Field289) : SourceJet Op:=
  ⟨noetherCorrectionMap reader p F signal.value,noetherCorrectionMap reader p F signal.first,
    noetherCorrectionMap reader p F signal.second⟩

private theorem correctionJet_generated (reader : Field289) (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index)
    (signal : ℝ→SourceJet Field289) (t : ℝ) (paid : HasSourceJets signal t) :
    HasSourceJets (fun s=>correctionJet reader p F (signal s)) t:=
  ⟨(noetherCorrectionMap reader p F).hasFDerivAt.comp_hasDerivAt t paid.1,
    (noetherCorrectionMap reader p F).hasFDerivAt.comp_hasDerivAt t paid.2⟩

private theorem correctionJet_continuous (reader : Field289) (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index)
    (signal : ℝ→SourceJet Field289) (paid : ContinuousJets signal) :
    ContinuousJets (fun t=>correctionJet reader p F (signal t)):=
  ⟨(noetherCorrectionMap reader p F).continuous.comp paid.1,
    (noetherCorrectionMap reader p F).continuous.comp paid.2.1,
    (noetherCorrectionMap reader p F).continuous.comp paid.2.2⟩

def noetherHistoryOperatorJet (q : PhysicalResponsePoint) (reader : Field289)
    (signal : ℝ→SourceJet Field289) (t : ℝ) : SourceJet Op:=
  addJet (historyOperatorJet q reader signal t)
    (jetMul (jetMul (jetMul (jetMul (physicalTimeJet (q.p+q.k) q.F 0 (-1) 0 t)
      (jetConst (jointResolvent (q.p+q.k) q.F q.z 0)))
        (correctionJet reader q.p q.F (signal t)))
          (jetConst (jointResolvent q.p q.F q.w 0))) (physicalTimeJet q.p q.F 0 1 0 t))

theorem noetherHistoryOperatorJet_generated (q : PhysicalResponsePoint) (reader : Field289)
    (signal : ℝ→SourceJet Field289) (continuousSignal : Continuous (fun t=>(signal t).value))
    (t : ℝ) (paid : HasSourceJets signal t) :
    HasSourceJets (noetherHistoryOperatorJet q reader signal) t:=
  sumJets _ _ t (historyOperatorJet_generated q reader signal continuousSignal t paid)
    (productJets _ _ t (productJets _ _ t (productJets _ _ t (productJets _ _ t
      (physicalTimeJet_generated _ _ _ _ _ _) (constantJets _ _))
        (correctionJet_generated reader q.p q.F signal t paid)) (constantJets _ _))
          (physicalTimeJet_generated _ _ _ _ _ _))

theorem noetherHistoryOperatorJet_continuous (q : PhysicalResponsePoint) (reader : Field289)
    (signal : ℝ→SourceJet Field289) (paid : ContinuousJets signal) :
    ContinuousJets (noetherHistoryOperatorJet q reader signal):=
  sumJets_continuous _ _ (historyOperatorJet_continuous q reader signal paid)
    (productJets_continuous _ _ (productJets_continuous _ _ (productJets_continuous _ _ (productJets_continuous _ _
      (physicalTimeJets_continuous _ _ _ _ _) (constantJets_continuous _))
        (correctionJet_continuous reader q.p q.F signal paid)) (constantJets_continuous _))
          (physicalTimeJets_continuous _ _ _ _ _))

def noetherHistorySourceJet (q : PhysicalResponsePoint) (signal : ℝ→SourceJet Field289) (t : ℝ) (i : Fin 289) : SourceJet ℂ:=
  negativeJet (pairJet (responseLeft q) (responseRight q) (noetherHistoryOperatorJet q (fieldUnit i) signal t))

theorem noetherHistorySourceJet_generated (q : PhysicalResponsePoint) (signal : ℝ→SourceJet Field289)
    (continuousSignal : Continuous (fun t=>(signal t).value)) (t : ℝ) (paid : HasSourceJets signal t) (i : Fin 289) :
    HasSourceJets (fun s=>noetherHistorySourceJet q signal s i) t:=
  negativeJets_generated _ t (pairJets_generated (responseLeft q) (responseRight q) _ t
    (noetherHistoryOperatorJet_generated q (fieldUnit i) signal continuousSignal t paid))

theorem noetherHistorySourceJet_continuous (q : PhysicalResponsePoint) (signal : ℝ→SourceJet Field289)
    (paid : ContinuousJets signal) (i : Fin 289) : ContinuousJets (fun t=>noetherHistorySourceJet q signal t i):=
  let actual:=pairJets_continuous q _ (noetherHistoryOperatorJet_continuous q (fieldUnit i) signal paid)
  ⟨actual.1.neg,actual.2.1.neg,actual.2.2.neg⟩

theorem noetherHistoryOperatorJet_value (q : PhysicalResponsePoint) (reader : Field289)
    (signal : ℝ→SourceJet Field289) (t : ℝ) :
    (noetherHistoryOperatorJet q reader signal t).value=
      historyOperator q reader (fun s=>(signal s).value) t+
      physicalTime (q.p+q.k) q.F (-t) 0*jointResolvent (q.p+q.k) q.F q.z 0*
        (noetherReaderContact reader (signal t).value q.p q.F-rawReaderContact reader (signal t).value q.p q.F)*
          jointResolvent q.p q.F q.w 0*physicalTime q.p q.F t 0:=by
  dsimp only [noetherHistoryOperatorJet,addJet,jetMul,jetConst,correctionJet]
  rw [historyOperatorJet_value,noetherCorrectionMap_actual]
  unfold physicalTimeJet timeJet physicalTime
  simp only [one_mul,neg_one_mul,add_zero]

theorem noetherHistorySourceJet_constant (q : PhysicalResponsePoint) (force : Field289) (t : ℝ) (i : Fin 289) :
    (noetherHistorySourceJet q (fun _=>⟨force,0,0⟩) t i).value=
      -noetherPreparedSlope q (fieldUnit i) force t:=by
  unfold noetherHistorySourceJet negativeJet pairJet
  rw [noetherHistoryOperatorJet_value,historyOperator_constant]
  unfold noetherPreparedSlope densitySlope dualSlope preparedDual independentDual preparedPrimal primalSlope
  simp only [ContinuousLinearMap.comp_apply,innerSL_apply_apply,mul_apply_eq_comp,
    inner_add_right,inner_sub_right,map_add,map_sub,add_apply,sub_apply,
    fiveDerivative,mul_add,add_mul,mul_sub,sub_mul]
  abel

end LowEnergy.SourcePropagationNoetherTime
