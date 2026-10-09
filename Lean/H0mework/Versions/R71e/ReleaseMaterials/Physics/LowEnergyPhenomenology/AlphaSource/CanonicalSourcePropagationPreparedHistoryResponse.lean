import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalSourcePropagationActualOrderedTimeDrive

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
noncomputable section
namespace LowEnergy.SourcePropagationTimeDependentFeedback
open GaussCoreHilbert CanonicalGradedSpatialSource PreparationVacuumMixedFieldReturn
open PreparationVacuumPhysicalFeedback PreparationVacuumRawJointFeedback
open PreparationVacuumJointFieldResponse PreparationVacuumPropagationPencil
open PreparationVacuumActionFieldLift PreparationVacuumFieldPerturbation
open CanonicalGradedVariation SourceFiniteUnitary
open Filter MeasureTheory PreparationVacuumGaugeSourceInjection
open scoped Topology BigOperators Matrix InnerProductSpace
local instance : NormedAlgebra ℝ Op:=NormedAlgebra.restrictScalars ℝ ℂ _
local instance : NormedAlgebra ℚ Op:=NormedAlgebra.restrictScalars ℚ ℂ _
attribute [local irreducible] jointGenerator jointCurrent jointResolvent rawReader rawReaderContact
  timeSlope physicalTime sourceRead rawInitial slopeInitial leftGenerator rightGenerator leftCurrent rightCurrent

private theorem reverse_zero_algebra {R : Type*} [Ring R] (F G C U : R) (commutes : C*U=U*C) :
    (F*(-C)-G*(-C))*U+(F-G)*(U*C)=0:=by
  rw [←commutes]
  noncomm_ring

private theorem reverse_derivative_algebra {R : Type*} [Ring R] (V U G D : R) :
    -(V*G+U*D)=V*(-G)+U*(-D):=by
  rw [mul_neg,mul_neg,neg_add]

section Uniqueness
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
local instance : NormedAlgebra ℝ (E→L[ℂ] E):=NormedAlgebra.restrictScalars ℝ ℂ _
local instance : NormedAlgebra ℚ (E→L[ℂ] E):=NormedAlgebra.restrictScalars ℚ ℂ _

private theorem reverse_ode_unique (C : E→L[ℂ] E) (f g : ℝ→E→L[ℂ] E)
    (D : ℝ→E→L[ℂ] E)
    (hf : ∀t,HasDerivAt f (f t*(-((-Complex.I) • C))+D t) t)
    (hg : ∀t,HasDerivAt g (g t*(-((-Complex.I) • C))+D t) t)
    (initial : f 0=g 0) (t : ℝ) : f t=g t:=by
  let W:=fun s : ℝ=>(f s-g s)*time C s
  have zero (s : ℝ) : HasDerivAt W 0 s:=by
    have h:=((hf s).sub (hg s)).mul (time_operator_derivative C s)
    have commutes:=((time_commutes C C (Commute.refl C) s).smul_left (-Complex.I)).eq
    apply h.congr_deriv
    simp only [add_sub_add_right_eq_sub,Pi.sub_apply]
    exact reverse_zero_algebra (R:=E→L[ℂ] E) (f s) (g s) ((-Complex.I) • C) (time C s) commutes

  have same:=is_const_of_deriv_eq_zero (fun s=>(zero s).differentiableAt)
    (fun s=>(zero s).deriv) t 0
  have vanish : W t=0:=by simpa only [W,initial,sub_self,zero_mul] using same
  have paid:=congrArg (fun A : E→L[ℂ] E=>A*time C (-t)) vanish
  simp only [W,mul_assoc,←time_add,add_neg_cancel,time_zero,mul_one,zero_mul] at paid
  exact sub_eq_zero.mp paid

private theorem forward_ode_unique (C : E→L[ℂ] E) (f g : ℝ→E→L[ℂ] E)
    (D : ℝ→E→L[ℂ] E)
    (hf : ∀t,HasDerivAt f (((-Complex.I) • C)*f t+D t) t)
    (hg : ∀t,HasDerivAt g (((-Complex.I) • C)*g t+D t) t)
    (initial : f 0=g 0) (t : ℝ) : f t=g t:=by
  let W:=fun s : ℝ=>time C (-s)*(f s-g s)
  have zero (s : ℝ) : HasDerivAt W 0 s:=by
    have reverse:=(time_operator_derivative C (-s)).scomp s ((hasDerivAt_id s).neg)
    have h:=reverse.mul ((hf s).sub (hg s))
    apply h.congr_deriv
    simp only [Function.comp_apply,neg_one_smul,neg_mul,add_sub_add_right_eq_sub,
      ←mul_sub,mul_assoc]
    exact neg_add_cancel _
  have same:=is_const_of_deriv_eq_zero (fun s=>(zero s).differentiableAt)
    (fun s=>(zero s).deriv) t 0
  have vanish : W t=0:=by simpa only [W,initial,sub_self,mul_zero] using same
  have paid:=congrArg (fun A : E→L[ℂ] E=>time C t*A) vanish
  simp only [W,←mul_assoc,←time_add,add_neg_cancel,time_zero,one_mul,mul_zero] at paid
  exact sub_eq_zero.mp paid
end Uniqueness

private theorem legacy_forward_ode (C B : Op) (t : ℝ) :
    HasDerivAt (variation C B) (((-Complex.I) • C)*variation C B t+
      ((-Complex.I) • B)*time C t) t:=by
  run_tac
    let name:=(Lean.Name.num `_private.H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationPropagationPencilDynamics 0) ++
      `LowEnergy.PreparationVacuumPropagationPencil.variation_left_ode
    Lean.Elab.Tactic.evalTactic (← `(tactic| exact $(Lean.mkIdent name) $(Lean.mkIdent `C) $(Lean.mkIdent `B) $(Lean.mkIdent `t)))

theorem orderedPrimal_constant (q : PhysicalResponsePoint) (force : Field289) (t : ℝ) :
    orderedPrimal q (fun _=>force) t=timeSlope force q.p q.F t:=by
  apply forward_ode_unique (jointGenerator q.p q.F 0 0) (orderedPrimal q (fun _=>force))
    (fun s=>timeSlope force q.p q.F s) (fun s=>rightCurrent q force*physicalTime q.p q.F s 0)
  · intro s
    have actual:=orderedPrimal_derivative q (fun _=>force) continuous_const s
    unfold rightGenerator at actual
    exact actual
  · intro s
    unfold timeSlope physicalTime rightCurrent
    exact legacy_forward_ode _ _ s
  · rw [orderedPrimal_initial,timeSlope_initial]

theorem orderedDual_constant (q : PhysicalResponsePoint) (force : Field289) (t : ℝ) :
    orderedDual q (fun _=>force) t=timeSlope force (q.p+q.k) q.F (-t):=by
  apply reverse_ode_unique (jointGenerator (q.p+q.k) q.F 0 0) (orderedDual q (fun _=>force))
    (fun s=>timeSlope force (q.p+q.k) q.F (-s))
    (fun s=>physicalTime (q.p+q.k) q.F (-s) 0*(-leftCurrent q force))
  · intro s
    have actual:=orderedDual_derivative q (fun _=>force) continuous_const s
    unfold leftGenerator at actual
    exact actual
  · intro s
    have actual:=(variation_ode (jointGenerator (q.p+q.k) q.F 0 0)
      (jointCurrent (q.p+q.k) q.F 0 0 force) (-s)).scomp s ((hasDerivAt_id s).neg)
    have simplified : HasDerivAt (fun r : ℝ=>variation (jointGenerator (q.p+q.k) q.F 0 0)
        (jointCurrent (q.p+q.k) q.F 0 0 force) (-r))
      (-(variation (jointGenerator (q.p+q.k) q.F 0 0) (jointCurrent (q.p+q.k) q.F 0 0 force) (-s)*
          ((-Complex.I) • jointGenerator (q.p+q.k) q.F 0 0)+
        time (jointGenerator (q.p+q.k) q.F 0 0) (-s)*
          ((-Complex.I) • jointCurrent (q.p+q.k) q.F 0 0 force))) s:=by
      convert! actual using 1
      simp only [neg_one_smul]
    unfold timeSlope physicalTime leftCurrent
    exact simplified.congr_deriv (reverse_derivative_algebra (R:=Op) _ _ _ _)

  · rw [orderedDual_initial,neg_zero,timeSlope_initial]

/-- The material legs vary at the preparation time; the current contact varies at the reading time. -/
def historyMiddle (q : PhysicalResponsePoint) (reader : Field289) (history : ℝ→Field289) (t : ℝ) : Op:=
  (-(jointResolvent (q.p+q.k) q.F q.z 0*jointCurrent (q.p+q.k) q.F q.z 0 (history 0)*jointResolvent (q.p+q.k) q.F q.z 0))*
    rawReader reader q.p q.F 0*jointResolvent q.p q.F q.w 0+
  jointResolvent (q.p+q.k) q.F q.z 0*rawReaderContact reader (history t) q.p q.F*jointResolvent q.p q.F q.w 0+
  jointResolvent (q.p+q.k) q.F q.z 0*rawReader reader q.p q.F 0*
    (-(jointResolvent q.p q.F q.w 0*jointCurrent q.p q.F q.w 0 (history 0)*jointResolvent q.p q.F q.w 0))

theorem historyMiddle_initial (q : PhysicalResponsePoint) (reader : Field289) (history : ℝ→Field289) :
    historyMiddle q reader history 0=slopeInitial q reader (history 0):=by
  unfold historyMiddle slopeInitial
  rfl

def historyOperator (q : PhysicalResponsePoint) (reader : Field289) (history : ℝ→Field289) (t : ℝ) : Op:=
  orderedDual q history t*rawInitial q reader*physicalTime q.p q.F t 0+
  physicalTime (q.p+q.k) q.F (-t) 0*historyMiddle q reader history t*physicalTime q.p q.F t 0+
  physicalTime (q.p+q.k) q.F (-t) 0*rawInitial q reader*orderedPrimal q history t

theorem historyOperator_initial (q : PhysicalResponsePoint) (reader : Field289) (history : ℝ→Field289) :
    historyOperator q reader history 0=slopeInitial q reader (history 0):=by
  simp only [historyOperator,orderedDual_initial,orderedPrimal_initial,physicalTime_initial,
    neg_zero,zero_mul,mul_zero,one_mul,mul_one,zero_add,add_zero,historyMiddle_initial]

theorem historyOperator_constant (q : PhysicalResponsePoint) (reader force : Field289) (t : ℝ) :
    historyOperator q reader (fun _=>force) t=fiveDerivative reader force q.p q.k q.F q.z q.w t:=by
  unfold historyOperator
  rw [orderedDual_constant,orderedPrimal_constant]
  unfold historyMiddle rawInitial fiveDerivative
  simp only [mul_add,add_mul,mul_assoc]
  abel

def historySource (q : PhysicalResponsePoint) (history : ℝ→Field289) (t : ℝ) : Fin 289→ℂ:=
  fun i=>-sourceRead q (historyOperator q (fieldUnit i) history t)

theorem historySource_initial (q : PhysicalResponsePoint) (history : ℝ→Field289) (hz : q.z.im≠0) (hw : q.w.im≠0) :
    historySource q history 0=PreparationVacuumRealReaction.sourceJacobian q 0 (history 0):=by
  ext i
  rw [PreparationVacuumRealReaction.sourceJacobian_actual q 0 (history 0) hz hw]
  dsimp only
  rw [sourceSlopeJet_value]
  unfold historySource eulerCovectorSlope rawPreparedSlope
  rw [historyOperator_initial,←slopeKernel_initial]
  simp only [sourceRead,ContinuousLinearMap.comp_apply,ContinuousLinearMap.apply_apply,innerSL_apply_apply,responseLeft,responseRight]

theorem historySource_constant (q : PhysicalResponsePoint) (force : Field289) (t : ℝ) :
    historySource q (fun _=>force) t=(fun i=>(sourceSlopeJet q force t i).value):=by
  ext i
  rw [sourceSlopeJet_value]
  unfold historySource eulerCovectorSlope rawPreparedSlope
  rw [historyOperator_constant]
  simp only [sourceRead,ContinuousLinearMap.comp_apply,ContinuousLinearMap.apply_apply,innerSL_apply_apply,responseLeft,responseRight]

private def readerDifferential (reader : Field289) (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) :
    Field289→L[ℝ] Op:=fderiv ℝ (rawReader reader p F) 0

attribute [local irreducible] readerDifferential

theorem readerDifferential_contact (reader force : Field289) (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) :
    readerDifferential reader p F force=rawReaderContact reader force p F:=by
  have differential:=(rawReader_C2 reader p F).differentiableAt (by norm_num) |>.hasFDerivAt
  have generated:=differential.comp_hasDerivAt_of_eq 0 (fieldRay_derivative force 0) (by simp)
  unfold readerDifferential
  exact generated.unique (rawReader_direction reader force p F)

private def currentSignalJet (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index)
    (signal : SourceJet Field289) : SourceJet Op:=
  ⟨(-Complex.I) • jointCurrent p F 0 0 signal.value,
    (-Complex.I) • jointCurrent p F 0 0 signal.first,
    (-Complex.I) • jointCurrent p F 0 0 signal.second⟩

private theorem currentSignalJet_generated (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index)
    (signal : ℝ→SourceJet Field289) (t : ℝ) (paid : HasSourceJets signal t) :
    HasSourceJets (fun s=>currentSignalJet p F (signal s)) t:=by
  exact ⟨(((jointCurrent p F 0 0).hasFDerivAt.comp_hasDerivAt t paid.1).const_smul (-Complex.I)),
    (((jointCurrent p F 0 0).hasFDerivAt.comp_hasDerivAt t paid.2).const_smul (-Complex.I))⟩

def orderedPrimalJet (q : PhysicalResponsePoint) (signal : ℝ→SourceJet Field289) (t : ℝ) : SourceJet Op:=
  let V:=orderedPrimal q (fun s=>(signal s).value) t
  let J:=currentSignalJet q.p q.F (signal t)
  let T:=physicalTimeJet q.p q.F 0 1 0 t
  let first:=rightGenerator q*V+J.value*T.value
  ⟨V,first,rightGenerator q*first+J.first*T.value+J.value*T.first⟩

theorem orderedPrimalJet_generated (q : PhysicalResponsePoint) (signal : ℝ→SourceJet Field289)
    (continuousSignal : Continuous (fun s=>(signal s).value)) (t : ℝ) (paid : HasSourceJets signal t) :
    HasSourceJets (orderedPrimalJet q signal) t:=by
  have hv:=orderedPrimal_derivative q (fun s=>(signal s).value) continuousSignal t
  have hj:=currentSignalJet_generated q.p q.F signal t paid
  have ht:=physicalTimeJet_generated q.p q.F 0 1 0 t
  have hfirst:=(hv.const_mul (rightGenerator q)).add (hj.1.mul ht.1)
  refine ⟨?_,?_⟩
  · convert! hv using 1
    unfold orderedPrimalJet currentSignalJet physicalTimeJet timeJet physicalTime rightCurrent
    simp only [one_mul,add_zero]
  · convert! hfirst using 1
    unfold orderedPrimalJet currentSignalJet physicalTimeJet timeJet physicalTime rightCurrent
    simp only [one_mul,add_zero,add_assoc]

def orderedDualJet (q : PhysicalResponsePoint) (signal : ℝ→SourceJet Field289) (t : ℝ) : SourceJet Op:=
  let V:=orderedDual q (fun s=>(signal s).value) t
  let J:=currentSignalJet (q.p+q.k) q.F (signal t)
  let T:=physicalTimeJet (q.p+q.k) q.F 0 (-1) 0 t
  let first:=V*(-leftGenerator q)+T.value*(-J.value)
  ⟨V,first,first*(-leftGenerator q)+T.first*(-J.value)+T.value*(-J.first)⟩

theorem orderedDualJet_generated (q : PhysicalResponsePoint) (signal : ℝ→SourceJet Field289)
    (continuousSignal : Continuous (fun s=>(signal s).value)) (t : ℝ) (paid : HasSourceJets signal t) :
    HasSourceJets (orderedDualJet q signal) t:=by
  have hv:=orderedDual_derivative q (fun s=>(signal s).value) continuousSignal t
  have hj:=currentSignalJet_generated (q.p+q.k) q.F signal t paid
  have ht:=physicalTimeJet_generated (q.p+q.k) q.F 0 (-1) 0 t
  have hfirst:=(hv.mul_const (-leftGenerator q)).add (ht.1.mul hj.1.neg)
  refine ⟨?_,?_⟩
  · convert! hv using 1
    unfold orderedDualJet currentSignalJet physicalTimeJet timeJet physicalTime leftCurrent
    simp only [neg_one_mul,add_zero]
  · convert! hfirst using 1
    unfold orderedDualJet currentSignalJet physicalTimeJet timeJet physicalTime leftCurrent
    simp only [neg_one_mul,add_zero,add_assoc,Pi.neg_apply]

private def preparationMiddle (q : PhysicalResponsePoint) (reader force : Field289) : Op:=
  (-(jointResolvent (q.p+q.k) q.F q.z 0*jointCurrent (q.p+q.k) q.F q.z 0 force*jointResolvent (q.p+q.k) q.F q.z 0))*
    rawReader reader q.p q.F 0*jointResolvent q.p q.F q.w 0+
  jointResolvent (q.p+q.k) q.F q.z 0*rawReader reader q.p q.F 0*
    (-(jointResolvent q.p q.F q.w 0*jointCurrent q.p q.F q.w 0 force*jointResolvent q.p q.F q.w 0))

private def readerSignalJet (reader : Field289) (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index)
    (signal : SourceJet Field289) : SourceJet Op:=
  ⟨readerDifferential reader p F signal.value,readerDifferential reader p F signal.first,
    readerDifferential reader p F signal.second⟩

private theorem readerSignalJet_generated (reader : Field289) (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index)
    (signal : ℝ→SourceJet Field289) (t : ℝ) (paid : HasSourceJets signal t) :
    HasSourceJets (fun s=>readerSignalJet reader p F (signal s)) t:=
  ⟨(readerDifferential reader p F).hasFDerivAt.comp_hasDerivAt t paid.1,
    (readerDifferential reader p F).hasFDerivAt.comp_hasDerivAt t paid.2⟩

def historyMiddleJet (q : PhysicalResponsePoint) (reader : Field289) (signal : ℝ→SourceJet Field289) (t : ℝ) : SourceJet Op:=
  addJet (jetConst (preparationMiddle q reader (signal 0).value))
    (jetMul (jetMul (jetConst (jointResolvent (q.p+q.k) q.F q.z 0))
      (readerSignalJet reader q.p q.F (signal t))) (jetConst (jointResolvent q.p q.F q.w 0)))

theorem historyMiddleJet_generated (q : PhysicalResponsePoint) (reader : Field289)
    (signal : ℝ→SourceJet Field289) (t : ℝ) (paid : HasSourceJets signal t) :
    HasSourceJets (historyMiddleJet q reader signal) t:=
  sumJets _ _ t (constantJets _ _) (productJets _ _ t (productJets _ _ t (constantJets _ _)
    (readerSignalJet_generated reader q.p q.F signal t paid)) (constantJets _ _))

theorem historyMiddleJet_value (q : PhysicalResponsePoint) (reader : Field289)
    (signal : ℝ→SourceJet Field289) (t : ℝ) :
    (historyMiddleJet q reader signal t).value=historyMiddle q reader (fun s=>(signal s).value) t:=by
  have contact : jointResolvent (q.p+q.k) q.F q.z 0*readerDifferential reader q.p q.F (signal t).value*
      jointResolvent q.p q.F q.w 0=
      jointResolvent (q.p+q.k) q.F q.z 0*rawReaderContact reader (signal t).value q.p q.F*
        jointResolvent q.p q.F q.w 0:=
    congrArg (fun A : Op=>jointResolvent (q.p+q.k) q.F q.z 0*A*jointResolvent q.p q.F q.w 0)
      (readerDifferential_contact reader (signal t).value q.p q.F)
  dsimp only [historyMiddleJet,addJet,jetConst,jetMul,readerSignalJet]
  rw [contact]
  unfold preparationMiddle historyMiddle
  abel

def historyOperatorJet (q : PhysicalResponsePoint) (reader : Field289) (signal : ℝ→SourceJet Field289) (t : ℝ) : SourceJet Op:=
  let L:=physicalTimeJet (q.p+q.k) q.F 0 (-1) 0 t
  let R:=physicalTimeJet q.p q.F 0 1 0 t
  let A:=jetConst (rawInitial q reader)
  addJet (addJet (jetMul (jetMul (orderedDualJet q signal t) A) R)
    (jetMul (jetMul L (historyMiddleJet q reader signal t)) R))
    (jetMul (jetMul L A) (orderedPrimalJet q signal t))

theorem historyOperatorJet_generated (q : PhysicalResponsePoint) (reader : Field289)
    (signal : ℝ→SourceJet Field289) (continuousSignal : Continuous (fun s=>(signal s).value))
    (t : ℝ) (paid : HasSourceJets signal t) :
    HasSourceJets (historyOperatorJet q reader signal) t:=by
  unfold historyOperatorJet
  apply sumJets
  · apply sumJets
    · exact productJets _ _ t (productJets _ _ t (orderedDualJet_generated q signal continuousSignal t paid)
        (constantJets _ _)) (physicalTimeJet_generated _ _ _ _ _ _)
    · exact productJets _ _ t (productJets _ _ t (physicalTimeJet_generated _ _ _ _ _ _)
        (historyMiddleJet_generated q reader signal t paid)) (physicalTimeJet_generated _ _ _ _ _ _)
  · exact productJets _ _ t (productJets _ _ t (physicalTimeJet_generated _ _ _ _ _ _) (constantJets _ _))
      (orderedPrimalJet_generated q signal continuousSignal t paid)

theorem historyOperatorJet_value (q : PhysicalResponsePoint) (reader : Field289)
    (signal : ℝ→SourceJet Field289) (t : ℝ) :
    (historyOperatorJet q reader signal t).value=historyOperator q reader (fun s=>(signal s).value) t:=by
  dsimp only [historyOperatorJet,addJet,jetMul,jetConst]
  rw [historyMiddleJet_value]
  dsimp only [orderedPrimalJet,orderedDualJet,physicalTimeJet,timeJet]
  unfold historyOperator physicalTime
  simp only [one_mul,neg_one_mul,add_zero]

def historySourceJet (q : PhysicalResponsePoint) (signal : ℝ→SourceJet Field289) (t : ℝ) (i : Fin 289) : SourceJet ℂ:=
  negativeJet (pairJet (responseLeft q) (responseRight q) (historyOperatorJet q (fieldUnit i) signal t))

theorem historySourceJet_generated (q : PhysicalResponsePoint) (signal : ℝ→SourceJet Field289)
    (continuousSignal : Continuous (fun s=>(signal s).value)) (t : ℝ) (paid : HasSourceJets signal t) (i : Fin 289) :
    HasSourceJets (fun s=>historySourceJet q signal s i) t:=
  negativeJets_generated _ t (pairJets_generated (responseLeft q) (responseRight q) _ t
    (historyOperatorJet_generated q (fieldUnit i) signal continuousSignal t paid))

theorem historySourceJet_value (q : PhysicalResponsePoint) (signal : ℝ→SourceJet Field289) (t : ℝ) (i : Fin 289) :
    (historySourceJet q signal t i).value=historySource q (fun s=>(signal s).value) t i:=by
  unfold historySourceJet negativeJet pairJet historySource
  rw [historyOperatorJet_value]
  simp only [sourceRead,ContinuousLinearMap.comp_apply,ContinuousLinearMap.apply_apply,innerSL_apply_apply]

private theorem currentSignalJet_continuous (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index)
    (signal : ℝ→SourceJet Field289) (paid : ContinuousJets signal) :
    ContinuousJets (fun t=>currentSignalJet p F (signal t)):=
  ⟨((jointCurrent p F 0 0).continuous.comp paid.1).const_smul (-Complex.I),
    ((jointCurrent p F 0 0).continuous.comp paid.2.1).const_smul (-Complex.I),
    ((jointCurrent p F 0 0).continuous.comp paid.2.2).const_smul (-Complex.I)⟩

private theorem orderedPrimalJet_continuous (q : PhysicalResponsePoint) (signal : ℝ→SourceJet Field289)
    (paid : ContinuousJets signal) : ContinuousJets (orderedPrimalJet q signal):=by
  have v : Continuous (orderedPrimal q (fun t=>(signal t).value)):=
    continuous_iff_continuousAt.mpr (fun t=>(orderedPrimal_derivative q _ paid.1 t).continuousAt)
  have j:=currentSignalJet_continuous q.p q.F signal paid
  have time:=physicalTimeJets_continuous q.p q.F 0 1 0
  have first:=(continuous_const (y:=rightGenerator q) |>.mul v).add (j.1.mul time.1)
  exact ⟨v,first,((continuous_const (y:=rightGenerator q) |>.mul first).add (j.2.1.mul time.1)).add (j.1.mul time.2.1)⟩

private theorem orderedDualJet_continuous (q : PhysicalResponsePoint) (signal : ℝ→SourceJet Field289)
    (paid : ContinuousJets signal) : ContinuousJets (orderedDualJet q signal):=by
  have v : Continuous (orderedDual q (fun t=>(signal t).value)):=
    continuous_iff_continuousAt.mpr (fun t=>(orderedDual_derivative q _ paid.1 t).continuousAt)
  have j:=currentSignalJet_continuous (q.p+q.k) q.F signal paid
  have time:=physicalTimeJets_continuous (q.p+q.k) q.F 0 (-1) 0
  have first:=(v.mul (continuous_const (y:= -leftGenerator q))).add (time.1.mul j.1.neg)
  exact ⟨v,first,((first.mul (continuous_const (y:= -leftGenerator q))).add (time.2.1.mul j.1.neg)).add (time.1.mul j.2.1.neg)⟩

private theorem readerSignalJet_continuous (reader : Field289) (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index)
    (signal : ℝ→SourceJet Field289) (paid : ContinuousJets signal) :
    ContinuousJets (fun t=>readerSignalJet reader p F (signal t)):=
  ⟨(readerDifferential reader p F).continuous.comp paid.1,
    (readerDifferential reader p F).continuous.comp paid.2.1,
    (readerDifferential reader p F).continuous.comp paid.2.2⟩

private theorem historyMiddleJet_continuous (q : PhysicalResponsePoint) (reader : Field289)
    (signal : ℝ→SourceJet Field289) (paid : ContinuousJets signal) :
    ContinuousJets (historyMiddleJet q reader signal):=
  sumJets_continuous _ _ (constantJets_continuous _) (productJets_continuous _ _
    (productJets_continuous _ _ (constantJets_continuous _) (readerSignalJet_continuous reader q.p q.F signal paid))
      (constantJets_continuous _))

theorem historyOperatorJet_continuous (q : PhysicalResponsePoint) (reader : Field289)
    (signal : ℝ→SourceJet Field289) (paid : ContinuousJets signal) :
    ContinuousJets (historyOperatorJet q reader signal):=by
  unfold historyOperatorJet
  apply sumJets_continuous
  · apply sumJets_continuous
    · exact productJets_continuous _ _ (productJets_continuous _ _ (orderedDualJet_continuous q signal paid)
        (constantJets_continuous _)) (physicalTimeJets_continuous _ _ _ _ _)
    · exact productJets_continuous _ _ (productJets_continuous _ _ (physicalTimeJets_continuous _ _ _ _ _)
        (historyMiddleJet_continuous q reader signal paid)) (physicalTimeJets_continuous _ _ _ _ _)
  · exact productJets_continuous _ _ (productJets_continuous _ _ (physicalTimeJets_continuous _ _ _ _ _) (constantJets_continuous _))
      (orderedPrimalJet_continuous q signal paid)

theorem historySourceJet_continuous (q : PhysicalResponsePoint) (signal : ℝ→SourceJet Field289)
    (paid : ContinuousJets signal) (i : Fin 289) : ContinuousJets (fun t=>historySourceJet q signal t i):=
  let actual:=pairJets_continuous q _ (historyOperatorJet_continuous q (fieldUnit i) signal paid)
  ⟨actual.1.neg,actual.2.1.neg,actual.2.2.neg⟩

end LowEnergy.SourcePropagationTimeDependentFeedback
