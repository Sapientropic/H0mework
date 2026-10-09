import H0mework.Versions.Rf13ed87d.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationPrincipalHistory
import H0mework.Versions.Rf13ed87d.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationSourceQuantumMixedRead

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency true
noncomputable section
namespace LowEnergy.PreparationVacuumPhysicalZeroRead
open GaussCoreHilbert CanonicalGradedSpatialSource PreparationVacuumElectromagneticIdentity
open PreparationVacuumJointFieldResponse PreparationVacuumPhysicalHalfAxis
open PreparationVacuumPhysicalPoleHalfResponse PreparationVacuumMovingPoleGaussReturn
open PreparationVacuumPhysicalPoleLegDynamics PreparationVacuumRawJointFeedback
open PreparationVacuumActionFieldLift PreparationVacuumPhysicalFeedback
open PreparationVacuumMixedFieldReturn PreparationVacuumPhysicalCurrentLaplaceReturn
open PreparationVacuumFieldConstraintResponse PreparationVacuumGaugeSourceInjection
open SourcePropagationNativeEulerHistory SourcePropagationNoetherTime SourcePropagationTimeDependentFeedback
open SourcePropagationNativeActionHessian SourcePropagationMotherEulerKernel SourcePropagationMotherResidualDirections
open PreparationVacuumOriginalGreenFeedback PreparationVacuumPropagationPencil
open PreparationVacuumCurrentSignalOperator SourcePropagationConstrainedPoleReturn
open Filter Set MeasureTheory
open scoped BigOperators Topology Matrix Interval InnerProductSpace
attribute [local irreducible] jointGenerator jointResolvent sourcePoleRead rawReader nativeHessian originalReadback

/-- Actual amplitude-zero action current; the source-created full504 Phi is fixed on both reads. -/
def sourceActualCurrentJet (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (left right : RestStateIndex) (t : ℝ) (i : Fin 289) : SourceJet ℂ:=
  negativeJet (pairJet (sourcePolePrepared q.epsilon q.precision pL left)
    (sourcePolePrepared q.epsilon q.precision pR right)
      (rawKernelJet (fieldUnit i) pR (pL-pR) q.F q.z q.w 0 t))

theorem sourceActualCurrentJet_generated (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (left right : RestStateIndex) (t : ℝ) (i : Fin 289) :
    HasSourceJets (fun s=>sourceActualCurrentJet q pL pR left right s i) t:=
  negativeJets_generated _ _ (pairJets_generated _ _ _ _ (rawKernelJet_generated _ _ _ _ _ _ _ _))

theorem sourceActualCurrentJet_value (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (left right : RestStateIndex) (t : ℝ) (i : Fin 289) :
    (sourceActualCurrentJet q pL pR left right t i).value=
      sourcePoleActionEuler q pL pR left right 0 t i:=by
  rw [sourcePoleActionEuler_source,sourcePoleRead_actual]
  simp only [sourceActualCurrentJet,negativeJet,pairJet,rawKernelJet_value]

private theorem actualCurrentJet_continuous (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (left right : RestStateIndex) (i : Fin 289) :
    ContinuousJets (fun t=>sourceActualCurrentJet q pL pR left right t i):=by
  have base:=rawKernelJets_continuous (fieldUnit i) pR (pL-pR) q.F q.z q.w 0
  have read (f : ℝ→ZeroReadOp) (hf : Continuous f) :
      Continuous (fun t=> -sourcePoleRead q.epsilon q.precision pL pR left right (f t)):=
    ((sourcePoleRead q.epsilon q.precision pL pR left right).continuous.comp hf).neg
  refine ⟨?_,?_,?_⟩
  · simpa only [sourceActualCurrentJet,negativeJet,pairJet,sourcePoleRead_actual] using
      read (fun t=>(rawKernelJet (fieldUnit i) pR (pL-pR) q.F q.z q.w 0 t).value) base.1
  · simpa only [sourceActualCurrentJet,negativeJet,pairJet,sourcePoleRead_actual] using
      read (fun t=>(rawKernelJet (fieldUnit i) pR (pL-pR) q.F q.z q.w 0 t).first) base.2.1
  · simpa only [sourceActualCurrentJet,negativeJet,pairJet,sourcePoleRead_actual] using
      read (fun t=>(rawKernelJet (fieldUnit i) pR (pL-pR) q.F q.z q.w 0 t).second) base.2.2

private theorem zero_weight_derivative (lambda : ℂ) (t : ℝ) :
    HasDerivAt (laplaceWeight lambda) (-lambda*laplaceWeight lambda t) t := by
  unfold laplaceWeight
  convert! (((Complex.ofRealCLM.hasFDerivAt).hasDerivAt.const_mul (-lambda)).cexp) using 1
  simp [Complex.ofRealCLM]
  ring

private theorem zero_weighted_boundary (j : ℝ→SourceJet ℂ) (lambda : ℂ)
    (t : ℝ) (paid : HasSourceJets j t) (n : Fin 3) :
    HasDerivAt (fun s=>laplaceWeight lambda s*initialCoSource lambda (j s) n)
      (laplaceWeight lambda t*(jetEntry (j t) n-lambda^n.val*(j t).value)) t := by
  fin_cases n
  · simpa [initialCoSource,jetEntry] using hasDerivAt_const t (0:ℂ)
  · have generated:=(zero_weight_derivative lambda t).mul paid.1
    change HasDerivAt (fun s=>laplaceWeight lambda s*(j s).value)
      (laplaceWeight lambda t*((j t).first-lambda^1*(j t).value)) t
    convert! generated using 1
    ring
  · have generated:=(zero_weight_derivative lambda t).mul ((paid.1.const_mul lambda).add paid.2)
    change HasDerivAt (fun s=>laplaceWeight lambda s*(lambda*(j s).value+(j s).first))
      (laplaceWeight lambda t*((j t).second-lambda^2*(j t).value)) t
    convert! generated using 1
    change _=(-lambda*laplaceWeight lambda t*(lambda*(j t).value+(j t).first)+
      laplaceWeight lambda t*(lambda*(j t).first+(j t).second))
    ring

private theorem zero_list_derivative {ι : Type*} (entries : List ι) (f df : ι→ℝ→ℂ) (t : ℝ)
    (paid : ∀x∈entries,HasDerivAt (f x) (df x t) t) :
    HasDerivAt (fun s=>(entries.map (fun x=>f x s)).sum) ((entries.map (fun x=>df x t)).sum) t := by
  induction entries with
  | nil=>exact hasDerivAt_const t 0
  | cons x rest ih=>simpa only [List.map_cons,List.sum_cons] using!
      (paid x (by simp)).add (ih (fun y member=>paid y (by simp [member])))

private theorem zero_list_continuous {ι : Type*} (entries : List ι) (f : ι→ℝ→ℂ)
    (paid : ∀x∈entries,Continuous (f x)) : Continuous (fun t=>(entries.map (fun x=>f x t)).sum) := by
  induction entries with
  | nil=>exact continuous_const
  | cons x rest ih=>simpa only [List.map_cons,List.sum_cons] using!
      (paid x (by simp)).add (ih (fun y member=>paid y (by simp [member])))

private def zero_forcing (j : ℝ→Fin 289→SourceJet ℂ) (lambda : ℂ) (T : ℝ) : Fin 289→ℂ :=
  fun field=>∫t in (0:ℝ)..T,laplaceWeight lambda t*(j t field).value

private def zero_timeSource (j : ℝ→Fin 289→SourceJet ℂ) (spatial : Fin 3→ℂ) (t : ℝ) (row : Fin 289) : ℂ :=
  (nativeReadbackTerms.attach.map (fun entry=>if row=entry.val.row then termSpatial spatial entry.val*
    jetEntry (j t entry.val.column) (nativeTimeOrder entry) else 0)).sum

private def zero_boundary (j : ℝ→Fin 289→SourceJet ℂ) (spatial : Fin 3→ℂ)
    (lambda : ℂ) (t : ℝ) (row : Fin 289) : ℂ :=
  (nativeReadbackTerms.attach.map (fun entry=>if row=entry.val.row then termSpatial spatial entry.val*
    (laplaceWeight lambda t*initialCoSource lambda (j t entry.val.column) (nativeTimeOrder entry)) else 0)).sum

private def zero_difference (j : ℝ→Fin 289→SourceJet ℂ) (spatial : Fin 3→ℂ)
    (lambda : ℂ) (t : ℝ) (row : Fin 289) : ℂ :=
  (nativeReadbackTerms.attach.map (fun entry=>if row=entry.val.row then termSpatial spatial entry.val*
    (laplaceWeight lambda t*(jetEntry (j t entry.val.column) (nativeTimeOrder entry)-
      lambda^(nativeTimeOrder entry).val*(j t entry.val.column).value)) else 0)).sum

private theorem zero_boundary_generated (j : ℝ→Fin 289→SourceJet ℂ)
    (paid : ∀field t,HasSourceJets (fun s=>j s field) t) (spatial : Fin 3→ℂ)
    (lambda : ℂ) (t : ℝ) (row : Fin 289) :
    HasDerivAt (fun s=>zero_boundary j spatial lambda s row) (zero_difference j spatial lambda t row) t := by
  unfold zero_boundary zero_difference
  convert! zero_list_derivative nativeReadbackTerms.attach
    (fun entry s=>if row=entry.val.row then termSpatial spatial entry.val*
      (laplaceWeight lambda s*initialCoSource lambda (j s entry.val.column) (nativeTimeOrder entry)) else 0)
    (fun entry s=>if row=entry.val.row then termSpatial spatial entry.val*
      (laplaceWeight lambda s*(jetEntry (j s entry.val.column) (nativeTimeOrder entry)-
        lambda^(nativeTimeOrder entry).val*(j s entry.val.column).value)) else 0) t (by
      intro entry _
      by_cases same : row=entry.val.row
      · simp only [if_pos same]
        exact (zero_weighted_boundary _ lambda t (paid entry.val.column t) _).const_mul _
      · simp only [if_neg same]
        exact hasDerivAt_const t 0) using 1

private theorem zero_entry_continuous (j : ℝ→SourceJet ℂ) (continuousJet : ContinuousJets j) (n : Fin 3) :
    Continuous (fun t=>jetEntry (j t) n) := by
  fin_cases n
  · exact continuousJet.1
  · exact continuousJet.2.1
  · exact continuousJet.2.2

private theorem zero_weight_continuous (lambda : ℂ) : Continuous (laplaceWeight lambda) := by
  unfold laplaceWeight
  fun_prop

private theorem zero_difference_continuous (j : ℝ→Fin 289→SourceJet ℂ)
    (continuousJet : ∀field,ContinuousJets (fun t=>j t field)) (spatial : Fin 3→ℂ) (lambda : ℂ) (row : Fin 289) :
    Continuous (fun t=>zero_difference j spatial lambda t row) := by
  unfold zero_difference
  apply zero_list_continuous
  intro entry _
  by_cases same : row=entry.val.row
  · simp only [if_pos same]
    have jet:=continuousJet entry.val.column
    exact ((zero_weight_continuous lambda).mul ((zero_entry_continuous _ jet _).sub (jet.1.const_mul _))).const_mul _
  · simp only [if_neg same]
    exact continuous_const

private theorem zero_timeSource_continuous (j : ℝ→Fin 289→SourceJet ℂ)
    (continuousJet : ∀field,ContinuousJets (fun t=>j t field)) (spatial : Fin 3→ℂ) (row : Fin 289) :
    Continuous (fun t=>zero_timeSource j spatial t row) := by
  unfold zero_timeSource
  apply zero_list_continuous
  intro entry _
  by_cases same : row=entry.val.row
  · simp only [if_pos same]
    exact (zero_entry_continuous _ (continuousJet entry.val.column) _).const_mul _
  · simp only [if_neg same]
    exact continuous_const

private theorem zero_weighted_list {ι : Type*} (entries : List ι) (left right : ι→ℂ) (weight : ℂ) :
    (entries.map (fun x=>weight*(left x-right x))).sum=
      weight*((entries.map left).sum-(entries.map right).sum) := by
  induction entries with
  | nil=>simp
  | cons x rest ih=>simp only [List.map_cons,List.sum_cons,ih];ring

private theorem zero_difference_source (j : ℝ→Fin 289→SourceJet ℂ) (spatial : Fin 3→ℂ)
    (lambda : ℂ) (t : ℝ) (row : Fin 289) :
    zero_difference j spatial lambda t row=laplaceWeight lambda t*
      (zero_timeSource j spatial t row-fullFrequency spatial lambda (fun field=>(j t field).value) row) := by
  unfold zero_difference zero_timeSource fullFrequency
  have difference:=zero_weighted_list nativeReadbackTerms.attach
    (fun entry=>if row=entry.val.row then termSpatial spatial entry.val*jetEntry (j t entry.val.column) (nativeTimeOrder entry) else 0)
    (fun entry=>if row=entry.val.row then termSpatial spatial entry.val*lambda^(nativeTimeOrder entry).val*(j t entry.val.column).value else 0)
    (laplaceWeight lambda t)
  apply Eq.trans _ difference
  congr 1
  apply List.map_congr_left
  intro entry _
  by_cases same : row=entry.val.row
  · simp only [if_pos same]
    ring
  · simp only [if_neg same]
    ring

private theorem zero_frequency_integral (j : ℝ→Fin 289→SourceJet ℂ)
    (continuousJet : ∀field,ContinuousJets (fun t=>j t field)) (spatial : Fin 3→ℂ)
    (lambda : ℂ) (T : ℝ) (row : Fin 289) :
    (∫t in (0:ℝ)..T,laplaceWeight lambda t*fullFrequency spatial lambda (fun field=>(j t field).value) row)=
      fullFrequency spatial lambda (zero_forcing j lambda T) row := by
  simp_rw [fullFrequency_original]
  symm
  change (∑field,originalReadback (fullMomentum spatial lambda) row field*zero_forcing j lambda T field)=_
  simp_rw [zero_forcing,←intervalIntegral.integral_const_mul]
  have exchange:=intervalIntegral.integral_finsetSum (s:=Finset.univ) (μ:=volume)
    (f:=fun (field : Fin 289) t=>originalReadback (fullMomentum spatial lambda) row field*
      (laplaceWeight lambda t*(j t field).value))
    (fun field _=>(((zero_weight_continuous lambda).mul (continuousJet field).1).const_mul
      (originalReadback (fullMomentum spatial lambda) row field)).intervalIntegrable 0 T)
  refine exchange.symm.trans ?_
  apply intervalIntegral.integral_congr
  intro t _
  simp only [Matrix.mulVec,dotProduct,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro field _
  ring

private theorem zero_forcing_readback (j : ℝ→Fin 289→SourceJet ℂ)
    (continuousJet : ∀field,ContinuousJets (fun t=>j t field))
    (paid : ∀field t,HasSourceJets (fun s=>j s field) t) (spatial : Fin 3→ℂ)
    (lambda : ℂ) (T : ℝ) (row : Fin 289) :
    (originalReadback (fullMomentum spatial lambda)*ᵥzero_forcing j lambda T) row=
      (∫t in (0:ℝ)..T,laplaceWeight lambda t*zero_timeSource j spatial t row)-
        (zero_boundary j spatial lambda T row-zero_boundary j spatial lambda 0 row) := by
  have boundary:=(intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _=>zero_boundary_generated j paid spatial lambda t row)
    ((zero_difference_continuous j continuousJet spatial lambda row).intervalIntegrable 0 T))
  simp_rw [zero_difference_source,mul_sub] at boundary
  have source : IntervalIntegrable (fun t=>laplaceWeight lambda t*zero_timeSource j spatial t row) volume 0 T:=
    ((zero_weight_continuous lambda).mul (zero_timeSource_continuous j continuousJet spatial row)).intervalIntegrable 0 T
  have frequency : IntervalIntegrable (fun t=>laplaceWeight lambda t*fullFrequency spatial lambda (fun field=>(j t field).value) row) volume 0 T := by
    simp_rw [fullFrequency_original]
    exact ((zero_weight_continuous lambda).mul (continuous_finsetSum _ (fun field _=>
      (continuousJet field).1.const_mul (originalReadback (fullMomentum spatial lambda) row field)))).intervalIntegrable 0 T
  rw [intervalIntegral.integral_sub source frequency,zero_frequency_integral j continuousJet,
    fullFrequency_original] at boundary
  linear_combination -boundary

def sourceActualCurrentTimeSource (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (left right : RestStateIndex) (spatial : Fin 3→ℂ) (t : ℝ) (row : Fin 289) : ℂ:=
  zero_timeSource (sourceActualCurrentJet q pL pR left right) spatial t row

def sourceActualCurrentBoundary (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (left right : RestStateIndex) (spatial : Fin 3→ℂ) (lambda : ℂ) (t : ℝ) (row : Fin 289) : ℂ:=
  zero_boundary (sourceActualCurrentJet q pL pR left right) spatial lambda t row

def sourceActualCurrentCosource (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (left right : RestStateIndex) (spatial : Fin 3→ℂ) (lambda : ℂ) (T : ℝ) : SignalAmplitude:=
  fun row=>(∫t in (0:ℝ)..T,laplaceWeight lambda t*sourceActualCurrentTimeSource q pL pR left right spatial t row)-
    (sourceActualCurrentBoundary q pL pR left right spatial lambda T row-
      sourceActualCurrentBoundary q pL pR left right spatial lambda 0 row)

theorem sourceActualCurrentWindow_ward (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (left right : RestStateIndex) (spatial : Fin 3→ℂ) (lambda : ℂ) (T : ℝ) :
    originalReadback (fullMomentum spatial lambda)*ᵥ sourcePoleCurrentWindow q pL pR left right lambda T=
      sourceActualCurrentCosource q pL pR left right spatial lambda T:=by
  have current : sourcePoleCurrentWindow q pL pR left right lambda T=
      zero_forcing (sourceActualCurrentJet q pL pR left right) lambda T:=by
    funext i
    simp_rw [sourcePoleCurrentWindow,zero_forcing,sourceActualCurrentJet_value]
  rw [current]
  funext row
  exact zero_forcing_readback _ (actualCurrentJet_continuous q pL pR left right)
    (fun i t=>sourceActualCurrentJet_generated q pL pR left right t i) spatial lambda T row

theorem sourceActualCurrentCosource_halfAxis (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (left right : RestStateIndex) (spatial : Fin 3→ℂ) (lambda : ℂ) (off : 0<lambda.re) (row : Fin 289) :
    Tendsto (fun T=>sourceActualCurrentCosource q pL pR left right spatial lambda T row) atTop
      (𝓝 ((originalReadback (fullMomentum spatial lambda)*ᵥ
        sourcePoleCurrentHalf q pL pR left right lambda) row)):=by
  have current : Tendsto (fun T=>sourcePoleCurrentWindow q pL pR left right lambda T) atTop
      (𝓝 (sourcePoleCurrentHalf q pL pR left right lambda)):=
    tendsto_pi_nhds.mpr (fun i=>sourcePoleCurrentWindow_halfAxis q pL pR left right lambda off i)
  have read : Continuous (fun a : SignalAmplitude=>
      (originalReadback (fullMomentum spatial lambda)*ᵥa) row):=by
    simp only [Matrix.mulVec,dotProduct]
    fun_prop
  simpa only [Function.comp_def,sourceActualCurrentWindow_ward] using (read.tendsto _).comp current

theorem sourceActualCurrentWindow_compatibility (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (left right : RestStateIndex) (spatial : Fin 3→ℂ) (lambda : ℂ) (T : ℝ) :
    sourceCompatibility (fullMomentum spatial lambda) (sourcePoleCurrentWindow q pL pR left right lambda T)=
      nullProjection*ᵥsourceActualCurrentCosource q pL pR left right spatial lambda T:=by
  rw [sourceCompatibility,sourceActualCurrentWindow_ward]

theorem sourceActualCurrentWindow_native (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (left right : RestStateIndex) (spatial : Fin 3→ℂ) (lambda : ℂ) (T : ℝ)
    (regular : fullMomentum spatial lambda∈regularSource) :
    nativeFourierHessian nativeHessian (fullMomentum spatial lambda)*ᵥ
      PreparationVacuumOriginalGreenFeedback.sourceField ⟨fullMomentum spatial lambda,regular⟩
        (sourcePoleCurrentWindow q pL pR left right lambda T)=
      sourcePoleCurrentWindow q pL pR left right lambda T-
        originalRowLift (fullMomentum spatial lambda)*ᵥ
          (nullProjection*ᵥsourceActualCurrentCosource q pL pR left right spatial lambda T):=by
  have returned:=nativeAction_sourceField (⟨fullMomentum spatial lambda,regular⟩:regularSource)
    (sourcePoleCurrentWindow q pL pR left right lambda T)
  simpa only [sourceActualCurrentWindow_compatibility] using returned

set_option backward.isDefEq.respectTransparency false in
theorem sourceActualCurrentWindow_native36 (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (left right : RestStateIndex) (spatial : Fin 3→ℂ) (lambda : ℂ) (T : ℝ)
    (regular : fullMomentum spatial lambda∈regularSource) :
    originalReader36 (fullMomentum spatial lambda)*ᵥ
      (nativeFourierHessian nativeHessian (fullMomentum spatial lambda)*ᵥ
        PreparationVacuumOriginalGreenFeedback.sourceField ⟨fullMomentum spatial lambda,regular⟩
          (sourcePoleCurrentWindow q pL pR left right lambda T))=
      originalReader36 (fullMomentum spatial lambda)*ᵥsourcePoleCurrentWindow q pL pR left right lambda T-
        originalReader36 (fullMomentum spatial lambda)*ᵥ
          (originalRowLift (fullMomentum spatial lambda)*ᵥ
            (nullProjection*ᵥsourceActualCurrentCosource q pL pR left right spatial lambda T)):=by
  rw [sourceActualCurrentWindow_native,Matrix.mulVec_sub]

private theorem staticReadMomentum (k : ℂ) :
    fullMomentum ![k,0,0] 0=PreparationVacuumPhysicalFieldChannel.staticAxis k:=rfl

theorem sourceActualCurrentWindow_mixed (q : PhysicalResponsePoint) (p : PhysicalMomentum)
    (left right : RestStateIndex) (k T : ℝ)
    (regular : PreparationVacuumPhysicalFieldChannel.staticAxis (k:ℂ)∈regularSource) :
    PreparationVacuumPhysicalFieldChannel.channelDenominator (k:ℂ)*
      (originalInverse (PreparationVacuumPhysicalFieldChannel.staticAxis (k:ℂ))*ᵥ
        PreparationVacuumOriginalGreenFeedback.sourceField
          ⟨PreparationVacuumPhysicalFieldChannel.staticAxis (k:ℂ),regular⟩
          (sourcePoleCurrentWindow q (p-![k,0,0]) p left right 0 T)) 21=
      PreparationVacuumPhysicalFieldChannel.channelNumerator (-(k:ℂ)) ⬝ᵥ
        sourceActualCurrentCosource q (p-![k,0,0]) p left right ![(k:ℂ),0,0] 0 T:=by
  rw [PreparationVacuumPhysicalFieldChannel.channel_actual_forcing_read]
  have generated:=sourceActualCurrentWindow_ward q (p-![k,0,0]) p left right ![(k:ℂ),0,0] 0 T
  rw [staticReadMomentum] at generated
  rw [generated]

theorem sourceActualCurrentWindow_mixed_cleared (q : PhysicalResponsePoint) (p : PhysicalMomentum)
    (left right : RestStateIndex) (k T : ℝ) :
    PreparationVacuumPhysicalFieldChannel.channelDenominator (k:ℂ)*
      (originalInverse (PreparationVacuumPhysicalFieldChannel.staticAxis (k:ℂ))*ᵥ
        (originalClearedGreen (PreparationVacuumPhysicalFieldChannel.staticAxis (k:ℂ))*ᵥ
          sourcePoleCurrentWindow q (p-![k,0,0]) p left right 0 T)) 21=
      originalFieldDenominator (PreparationVacuumPhysicalFieldChannel.staticAxis (k:ℂ))*
        (PreparationVacuumPhysicalFieldChannel.channelNumerator (-(k:ℂ)) ⬝ᵥ
          sourceActualCurrentCosource q (p-![k,0,0]) p left right ![(k:ℂ),0,0] 0 T):=by
  rw [PreparationVacuumPhysicalFieldChannel.channel_cleared_forcing_read]
  have generated:=sourceActualCurrentWindow_ward q (p-![k,0,0]) p left right ![(k:ℂ),0,0] 0 T
  rw [staticReadMomentum] at generated
  rw [generated]

end LowEnergy.PreparationVacuumPhysicalZeroRead
