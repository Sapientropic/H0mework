import H0mework.Versions.AE.Physics.LowEnergy.AlphaSource.CanonicalPreparationSourceCurrentFieldSquare

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumCurrentVisibleFeedback
open PreparationVacuumMatterEulerFeedback PreparationVacuumNoetherResponsePrice
open PreparationVacuumOriginalGreenFeedback PreparationVacuumGaugeSourceInjection
open PreparationVacuumPhysicalFeedback PreparationVacuumNoetherOrdinaryWard
open PreparationVacuumFieldConstraintResponse PreparationVacuumMixedFieldReturn
open PreparationVacuumActionFieldLift PreparationVacuumOrderedRealSignal
open PreparationVacuumOriginalDensity PreparationVacuumFixedMomentumActionReturn
open SourcePropagationNativeActionHessian SourcePropagationMotherResidualDirections
open CanonicalGradedSpatialSource
open Filter Set MeasureTheory
open scoped Topology ContDiff BigOperators Matrix Interval ComplexConjugate
local instance : DecidableEq PhysicalMomentum:=Classical.decEq _
attribute [local irreducible] sourceGreen originalJacobi sourceCompatibility originalRowLift
  nativeHessian sourceMatterEulerPrepared

private def pairedCoefficients (key : PhysicalMomentum) (a : ℂ) : MomentumCoefficients:=
  Finsupp.single key a+Finsupp.single (-key) (star a)

private theorem pairedCoefficients_reality (key wave : PhysicalMomentum) (a : ℂ) :
    pairedCoefficients key a (-wave)=star (pairedCoefficients key a wave) :=by
  have reverse : (key= -wave)↔(-key=wave):=by
    constructor <;> intro same
    · rw [same,neg_neg]
    · rw [←same,neg_neg]
  simp only [pairedCoefficients,Finsupp.add_apply,Finsupp.single_apply]
  simp only [reverse,neg_inj,apply_ite,star_add,star_zero,star_star]
  split_ifs <;> simp_all only [add_zero,zero_add,add_comm]

private theorem half_pair_star (a b : ℂ) :
    star ((1/2:ℂ)*(a+star b))=(1/2:ℂ)*(b+star a) :=by
  simp only [star_mul,star_add,star_star]
  norm_num
  ring

theorem actionRealCoefficients_paired (q : PhysicalResponsePoint) (reader h : Field289) (t : ℝ) :
    actionRealCoefficients q reader h t=
      pairedCoefficients (-q.k) ((1/2:ℂ)*(sourceMatterEulerPrepared q reader h t+
        star (sourceMatterEulerPrepared (oppositeCoordinates q) reader h t)))+
      pairedCoefficients (2 • q.p+q.k) ((1/2:ℂ)*
        (sourceMatterEulerPrepared (crossRightCoordinates q) reader h t+
          star (sourceMatterEulerPrepared (crossLeftCoordinates q) reader h t))) :=by
  simp only [actionRealCoefficients,pairedCoefficients,neg_neg,half_pair_star]
  abel

theorem actionRealCoefficients_reality (q : PhysicalResponsePoint) (reader h : Field289)
    (t : ℝ) (wave : PhysicalMomentum) :
    actionRealCoefficients q reader h t (-wave)=star (actionRealCoefficients q reader h t wave) :=by
  rw [actionRealCoefficients_paired]
  simp only [Finsupp.add_apply,star_add,pairedCoefficients_reality]

theorem sourceModeJoint_reality (q : PhysicalResponsePoint) (wave : PhysicalMomentum) (u : Field289×ℝ) :
    sourceModeJoint q (-wave) u=fun i=>star (sourceModeJoint q wave u i) :=by
  funext i
  change -actionRealCoefficients q (fieldUnit i) u.1 u.2 (-(-wave))=
    star (-actionRealCoefficients q (fieldUnit i) u.1 u.2 (-wave))
  rw [actionRealCoefficients_reality q (fieldUnit i) u.1 u.2 (-wave),star_neg]

theorem sourceModeJacobian_reality (q : PhysicalResponsePoint) (wave : PhysicalMomentum)
    (force : Field289) (hz : q.z.im≠0) (hw : q.w.im≠0) (t : ℝ) :
    sourceModeJacobian q (-wave) t force=fun i=>star (sourceModeJacobian q wave t force i) :=by
  have original:=(actionRealEulerSource_generated q t wave force hz hw)
  have reverse:=actionRealEulerSource_generated q t (-wave) force hz hw
  funext i
  have actual:=(Complex.conjCLE.toContinuousLinearMap.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt
    0 ((hasDerivAt_pi.mp original) i)
  have derivative:=(hasDerivAt_pi.mp reverse) i
  have same : (fun r : ℝ=>actionRealEulerSource q t (-wave) (r • force) i)=
      (fun r : ℝ=>star (actionRealEulerSource q t wave (r • force) i)) :=by
    funext r
    exact congrFun (sourceModeJoint_reality q wave (r • force,t)) i
  rw [same] at derivative
  have result:=derivative.unique actual
  rw [sourceModeJacobian_generated q (-wave) force hz hw t,
    sourceModeJacobian_generated q wave force hz hw t]
  exact result

theorem sourceLaplaceWeight_reality (lambda : ℂ) (t : ℝ) :
    laplaceWeight (star lambda) t=star (laplaceWeight lambda t) :=by
  unfold laplaceWeight
  simp only [map_neg,map_mul,Complex.conj_ofReal,←Complex.exp_conj,Complex.star_def]

theorem sourceModeForcing_reality (q : PhysicalResponsePoint) (wave : PhysicalMomentum)
    (lambda : ℂ) (force : Field289) (hz : q.z.im≠0) (hw : q.w.im≠0) (T : ℝ) :
    modeForcing q force true (-wave) (star lambda) T=
      fun i=>star (modeForcing q force true wave lambda T i) :=by
  funext i
  unfold modeForcing
  have conjugate:=intervalIntegral.intervalIntegral_conj
    (f:=fun t : ℝ=>laplaceWeight lambda t*(modeJet q force true wave t i).value)
    (a:=0) (b:=T) (μ:=volume)
  simp only [starRingEnd_apply] at conjugate
  rw [←conjugate]
  apply intervalIntegral.integral_congr
  intro t _
  simp only [sourceLaplaceWeight_reality,modeJet,realEulerTimeJet_value,ite_true,star_mul]
  have same:=congrFun (sourceModeJacobian_reality q wave force hz hw t) i
  rw [sourceModeJacobian_generated q (-wave) force hz hw t,
    sourceModeJacobian_generated q wave force hz hw t] at same
  rw [same]
  exact mul_comm _ _

theorem sourceWindowJacobian_reality (q : PhysicalResponsePoint) (wave : PhysicalMomentum)
    (lambda : ℂ) (force : Field289) (hz : q.z.im≠0) (hw : q.w.im≠0) (T : ℝ) :
    sourceWindowJacobian q (-wave) (star lambda) T force=
      fun i=>star (sourceWindowJacobian q wave lambda T force i) :=by
  rw [sourceWindowJacobian_generated q (-wave) (star lambda) force hz hw T,
    sourceWindowJacobian_generated q wave lambda force hz hw T]
  exact sourceModeForcing_reality q wave lambda force hz hw T

theorem sourcePhysicalMomentum_reality (wave : PhysicalMomentum) (lambda : ℂ) :
    fullMomentum (PreparationVacuumPhysicalFeedback.physicalSpatial (-wave)) (star lambda)=
      fun mu=>star (fullMomentum (PreparationVacuumPhysicalFeedback.physicalSpatial wave) lambda mu) :=by
  funext mu
  cases mu using Fin.cases with
  | zero=>rfl
  | succ i=>
    simp only [fullMomentum,Fin.cases_succ,PreparationVacuumPhysicalFeedback.physicalSpatial,
      Pi.neg_apply,Complex.ofReal_neg,map_mul,Complex.star_def,Complex.conj_I,Complex.conj_ofReal]
    ring

theorem sourceNativeHessian_reality (p : Fin 4→ℂ) :
    nativeFourierHessian nativeHessian (fun mu=>star (p mu))=
      fun i j=>star (nativeFourierHessian nativeHessian p i j) :=by
  funext i j
  simp only [nativeFourierHessian,map_sum,map_mul,Complex.star_def,Complex.conj_ofReal]
  apply Finset.sum_congr rfl
  intro left _
  apply Finset.sum_congr rfl
  intro right _
  cases left <;> cases right <;> simp [jetSymbol]

theorem sourceOriginalJacobi_reality (p : Fin 4→ℂ) :
    originalJacobi (fun mu=>star (p mu))=fun i j=>star (originalJacobi p i j) :=by
  rw [←nativeActionFourierHessian_original,sourceNativeHessian_reality,nativeActionFourierHessian_original]

private theorem matrixVec_reality {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℂ) (v : Fin n→ℂ) :
    (fun i j=>star (A i j))*ᵥ(fun j=>star (v j))=fun i=>star ((A*ᵥv) i) :=by
  funext i
  simp only [Matrix.mulVec,dotProduct,star_sum,star_mul,mul_comm]

private theorem constantRec {A E : Sort*} {a b : A} (value : E) (equal : a=b) :
    Eq.rec (motive:=fun _ _=>E) value equal=value :=by
  cases equal
  rfl


theorem sourceOriginalReader36_reality (p : Fin 4→ℂ) :
    originalReader36 (fun mu=>star (p mu))=fun i j=>star (originalReader36 p i j) :=by
  funext i j
  run_tac
    let env←Lean.getEnv
    let source:=`LowEnergy.PreparationVacuumFieldConstraintResponse.originalReader36
    let some (.defnInfo definition):=env.find? source | throwError "Expected original reader definition"
    let body:=definition.value.getLambdaBody.getLambdaBody.getLambdaBody
    let .const matcher _:=body.getAppFn | throwError "Expected source reader matcher"
    Lean.Elab.Tactic.evalTactic (← `(tactic| delta $(Lean.mkIdent source) $(Lean.mkIdent matcher)))
  simp only [constantRec]
  conv_rhs =>
    simp only [apply_dite,constantRec,star_mul,star_div₀,star_neg,star_ofNat,star_one,star_zero,
      Complex.star_def,Complex.conj_ofReal,mul_comm]
  simp only [Complex.star_def]


theorem sourceCurvatureJacobian_mate (q : PhysicalResponsePoint) (wave : PhysicalMomentum)
    (lambda : physicalSpectralDomain wave) (force : Field289) (hz : q.z.im≠0) (hw : q.w.im≠0) (T : ℝ) :
    originalReader36 (fullMomentum (PreparationVacuumPhysicalFeedback.physicalSpatial (-wave)) (star lambda.val))*ᵥ
      (fun i=>star (sourceFieldJacobian q wave lambda T force i))=
        fun row=>star (sourceCurvatureJacobian q wave lambda T force row) :=by
  rw [sourcePhysicalMomentum_reality,sourceOriginalReader36_reality,matrixVec_reality,
    sourceFieldJacobian_generated q wave lambda force hz hw T,
    sourceCurvatureJacobian_generated q wave lambda force hz hw T]

theorem sourceFourierWindowJacobian_mate (q : PhysicalResponsePoint) (wave : PhysicalMomentum)
    (lambda : physicalSpectralDomain wave) (force : Field289) (hz : q.z.im≠0) (hw : q.w.im≠0) (T : ℝ) :
    sourceNativeFourierReal
        (fullMomentum (PreparationVacuumPhysicalFeedback.physicalSpatial (-wave)) (star lambda.val)) force-
      sourceWindowJacobian q (-wave) (star lambda.val) T force=
        fun i=>star (sourceFourierWindowJacobian q wave lambda T force i) :=by
  rw [sourcePhysicalMomentum_reality,sourceNativeFourierReal_original,
    sourceOriginalJacobi_reality,sourceWindowJacobian_reality q wave lambda.val force hz hw T,
    sourceFourierWindowJacobian_original q wave lambda force hz hw T,
    sourceWindowJacobian_generated q wave lambda.val force hz hw T]
  have input : (fun i=>Complex.ofReal (force i))=fun i=>star (sourceRealEmbedding force i) :=by
    simp only [sourceRealEmbedding_apply,Complex.star_def,Complex.conj_ofReal]
  rw [input,matrixVec_reality]
  funext i
  simp only [Pi.sub_apply,star_sub]

/-- The mate is generated by conjugating the entire returned field, including the original nine residuals. -/
theorem sourceFieldJacobian_mate (q : PhysicalResponsePoint) (wave : PhysicalMomentum)
    (lambda : physicalSpectralDomain wave) (force : Field289) (hz : q.z.im≠0) (hw : q.w.im≠0) (T : ℝ) :
    originalJacobi (fullMomentum (PreparationVacuumPhysicalFeedback.physicalSpatial (-wave)) (star lambda.val))*ᵥ
      (fun i=>star (sourceFieldJacobian q wave lambda T force i))=
        modeForcing q force true (-wave) (star lambda.val) T-
          (fun i=>star ((originalRowLift (fullMomentum (physicalSpatial wave) lambda.val)*ᵥ
            sourceCompatibility (fullMomentum (physicalSpatial wave) lambda.val)
              (modeForcing q force true wave lambda.val T)) i)) :=by
  rw [sourcePhysicalMomentum_reality,sourceOriginalJacobi_reality,matrixVec_reality]
  have original:=sourceFieldJacobian_native q wave lambda force hz hw T
  rw [nativeActionFourierHessian_original,
    sourceWindowJacobian_generated q wave lambda.val force hz hw T] at original
  rw [original,sourceModeForcing_reality q wave lambda.val force hz hw T]
  funext i
  simp only [Pi.sub_apply,star_sub]

end LowEnergy.PreparationVacuumCurrentVisibleFeedback
