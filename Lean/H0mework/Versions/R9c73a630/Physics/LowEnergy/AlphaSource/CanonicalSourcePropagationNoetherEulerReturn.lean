import H0mework.Versions.R9c73a630.Physics.LowEnergy.AlphaSource.CanonicalSourcePropagationNoetherHistoryResponse

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
noncomputable section
namespace LowEnergy.SourcePropagationNoetherTime
open PreparationVacuumGaugeSourceInjection PreparationVacuumOriginalGreenFeedback
open PreparationVacuumPhysicalFeedback PreparationVacuumPropagationPencil
open PreparationVacuumMixedFieldReturn PreparationVacuumFieldConstraintResponse
open PreparationVacuumActionFieldLift GaussCoreHilbert CanonicalGradedSpatialSource
open Filter MeasureTheory
open scoped Topology Interval BigOperators Matrix
attribute [local irreducible] originalJacobi originalChange originalReadback originalRowLift
  sourceGreen sourceCompatibility PreparationVacuumOriginalGreenFeedback.sourceField originalReader36 sourceRead

private theorem list_sum_derivative {ι : Type*} (entries : List ι) (f df : ι→ℝ→ℂ) (t : ℝ)
    (paid : ∀a∈entries,HasDerivAt (f a) (df a t) t) :
    HasDerivAt (fun s=>(entries.map (fun a=>f a s)).sum) ((entries.map (fun a=>df a t)).sum) t:=by
  induction entries with
  | nil=>exact hasDerivAt_const t 0
  | cons a rest ih=>simpa only [List.map_cons,List.sum_cons] using!
      (paid a (by simp)).add (ih (fun b hb=>paid b (by simp [hb])))

private theorem list_sum_continuous {ι : Type*} (entries : List ι) (f : ι→ℝ→ℂ)
    (paid : ∀a∈entries,Continuous (f a)) : Continuous (fun t=>(entries.map (fun a=>f a t)).sum):=by
  induction entries with
  | nil=>exact continuous_const
  | cons a rest ih=>simpa only [List.map_cons,List.sum_cons] using!
      (paid a (by simp)).add (ih (fun b hb=>paid b (by simp [hb])))

private theorem native_boundary_derivative (j : ℝ→SourceJet ℂ) (lambda : ℂ) (t : ℝ)
    (paid : HasSourceJets j t) (n : Fin 3) :
    HasDerivAt (fun s=>laplaceWeight lambda s*initialCoSource lambda (j s) n)
      (laplaceWeight lambda t*(jetEntry (j t) n-lambda^n.val*(j t).value)) t:=by
  run_tac
    let name:=(Lean.Name.num `_private.H0mework.Versions.R9c73a630.Physics.LowEnergy.AlphaSource.CanonicalPreparationPhysicalFullSourceWindow 0) ++
      `LowEnergy.PreparationVacuumPhysicalFeedback.weightedBoundaryDerivative
    Lean.Elab.Tactic.evalTactic (← `(tactic| exact $(Lean.mkIdent name) $(Lean.mkIdent `j) $(Lean.mkIdent `lambda)
      $(Lean.mkIdent `t) $(Lean.mkIdent `paid) $(Lean.mkIdent `n)))

def noetherForcing (q : PhysicalResponsePoint) (signal : ℝ→SourceJet Field289) (lambda : ℂ) (T : ℝ) : Fin 289→ℂ:=
  fun i=>∫t in (0:ℝ)..T,laplaceWeight lambda t*(noetherHistorySourceJet q signal t i).value

def noetherTimeSource (q : PhysicalResponsePoint) (signal : ℝ→SourceJet Field289)
    (spatial : Fin 3→ℂ) (t : ℝ) (row : Fin 289) : ℂ:=
  (nativeReadbackTerms.attach.map (fun a=>if row=a.val.row then termSpatial spatial a.val*
    jetEntry (noetherHistorySourceJet q signal t a.val.column) (nativeTimeOrder a) else 0)).sum

def noetherBoundary (q : PhysicalResponsePoint) (signal : ℝ→SourceJet Field289)
    (spatial : Fin 3→ℂ) (lambda : ℂ) (t : ℝ) (row : Fin 289) : ℂ:=
  (nativeReadbackTerms.attach.map (fun a=>if row=a.val.row then termSpatial spatial a.val*
    (laplaceWeight lambda t*initialCoSource lambda (noetherHistorySourceJet q signal t a.val.column)
      (nativeTimeOrder a)) else 0)).sum

def noetherDifference (q : PhysicalResponsePoint) (signal : ℝ→SourceJet Field289)
    (spatial : Fin 3→ℂ) (lambda : ℂ) (t : ℝ) (row : Fin 289) : ℂ:=
  (nativeReadbackTerms.attach.map (fun a=>if row=a.val.row then termSpatial spatial a.val*
    (laplaceWeight lambda t*(jetEntry (noetherHistorySourceJet q signal t a.val.column) (nativeTimeOrder a)-
      lambda^(nativeTimeOrder a).val*(noetherHistorySourceJet q signal t a.val.column).value)) else 0)).sum

theorem noetherBoundary_generated (q : PhysicalResponsePoint) (signal : ℝ→SourceJet Field289)
    (continuousSignal : Continuous (fun t=>(signal t).value))
    (paid : ∀t,HasSourceJets signal t) (spatial : Fin 3→ℂ) (lambda : ℂ) (t : ℝ) (row : Fin 289) :
    HasDerivAt (fun r=>noetherBoundary q signal spatial lambda r row)
      (noetherDifference q signal spatial lambda t row) t:=by
  unfold noetherBoundary noetherDifference
  convert! list_sum_derivative nativeReadbackTerms.attach
    (fun a r=>if row=a.val.row then termSpatial spatial a.val*
      (laplaceWeight lambda r*initialCoSource lambda (noetherHistorySourceJet q signal r a.val.column) (nativeTimeOrder a)) else 0)
    (fun a r=>if row=a.val.row then termSpatial spatial a.val*
      (laplaceWeight lambda r*(jetEntry (noetherHistorySourceJet q signal r a.val.column) (nativeTimeOrder a)-
        lambda^(nativeTimeOrder a).val*(noetherHistorySourceJet q signal r a.val.column).value)) else 0) t (by
      intro a _
      by_cases same : row=a.val.row
      · simp only [if_pos same]
        exact (native_boundary_derivative _ lambda t
          (noetherHistorySourceJet_generated q signal continuousSignal t (paid t) a.val.column) _).const_mul _
      · simp only [if_neg same]
        exact hasDerivAt_const t 0) using 1

private theorem weight_continuous (lambda : ℂ) : Continuous (laplaceWeight lambda):=by
  unfold laplaceWeight
  fun_prop

private theorem jet_entry_continuous (j : ℝ→SourceJet ℂ) (paid : ContinuousJets j) (n : Fin 3) :
    Continuous (fun t=>jetEntry (j t) n):=by
  fin_cases n
  · exact paid.1
  · exact paid.2.1
  · exact paid.2.2

theorem noetherDifference_continuous (q : PhysicalResponsePoint) (signal : ℝ→SourceJet Field289)
    (continuousSignal : ContinuousJets signal) (spatial : Fin 3→ℂ) (lambda : ℂ) (row : Fin 289) :
    Continuous (fun t=>noetherDifference q signal spatial lambda t row):=by
  unfold noetherDifference
  apply list_sum_continuous
  intro a _
  by_cases same : row=a.val.row
  · simp only [if_pos same]
    have hj:=noetherHistorySourceJet_continuous q signal continuousSignal a.val.column
    exact ((weight_continuous lambda).mul ((jet_entry_continuous _ hj _).sub (hj.1.const_mul _))).const_mul _
  · simp only [if_neg same]
    exact continuous_const

theorem noetherTimeSource_continuous (q : PhysicalResponsePoint) (signal : ℝ→SourceJet Field289)
    (continuousSignal : ContinuousJets signal) (spatial : Fin 3→ℂ) (row : Fin 289) :
    Continuous (fun t=>noetherTimeSource q signal spatial t row):=by
  unfold noetherTimeSource
  apply list_sum_continuous
  intro a _
  by_cases same : row=a.val.row
  · simp only [if_pos same]
    exact (jet_entry_continuous _ (noetherHistorySourceJet_continuous q signal continuousSignal a.val.column) _).const_mul _
  · simp only [if_neg same]
    exact continuous_const

private theorem weighted_list_difference {ι : Type*} (entries : List ι) (left right : ι→ℂ) (weight : ℂ) :
    (entries.map (fun a=>weight*(left a-right a))).sum=
      weight*((entries.map left).sum-(entries.map right).sum):=by
  induction entries with
  | nil=>simp
  | cons a rest ih=>simp only [List.map_cons,List.sum_cons,ih];ring

theorem noetherDifference_source (q : PhysicalResponsePoint) (signal : ℝ→SourceJet Field289)
    (spatial : Fin 3→ℂ) (lambda : ℂ) (t : ℝ) (row : Fin 289) :
    noetherDifference q signal spatial lambda t row=laplaceWeight lambda t*
      (noetherTimeSource q signal spatial t row-
        fullFrequency spatial lambda (fun i=>(noetherHistorySourceJet q signal t i).value) row):=by
  unfold noetherDifference noetherTimeSource fullFrequency
  have actual:=weighted_list_difference nativeReadbackTerms.attach
    (fun a=>if row=a.val.row then termSpatial spatial a.val*jetEntry (noetherHistorySourceJet q signal t a.val.column) (nativeTimeOrder a) else 0)
    (fun a=>if row=a.val.row then termSpatial spatial a.val*lambda^(nativeTimeOrder a).val*(noetherHistorySourceJet q signal t a.val.column).value else 0)
    (laplaceWeight lambda t)
  apply Eq.trans _ actual
  congr 1
  apply List.map_congr_left
  intro a _
  by_cases same : row=a.val.row
  · simp only [if_pos same]
    ring
  · simp only [if_neg same]
    ring

theorem noetherFrequency_integral (q : PhysicalResponsePoint) (signal : ℝ→SourceJet Field289)
    (continuousSignal : ContinuousJets signal) (spatial : Fin 3→ℂ) (lambda : ℂ) (T : ℝ) (row : Fin 289) :
    (∫t in (0:ℝ)..T,laplaceWeight lambda t*
      fullFrequency spatial lambda (fun i=>(noetherHistorySourceJet q signal t i).value) row)=
      fullFrequency spatial lambda (noetherForcing q signal lambda T) row:=by
  simp_rw [fullFrequency_original]
  symm
  change (∑j,originalReadback (fullMomentum spatial lambda) row j*noetherForcing q signal lambda T j)=_
  simp_rw [noetherForcing,←intervalIntegral.integral_const_mul]
  have actual:=intervalIntegral.integral_finsetSum (s:=Finset.univ) (μ:=volume)
    (f:=fun (j : Fin 289) t=>originalReadback (fullMomentum spatial lambda) row j*
      (laplaceWeight lambda t*(noetherHistorySourceJet q signal t j).value))
    (fun j _=>(((weight_continuous lambda).mul (noetherHistorySourceJet_continuous q signal continuousSignal j).1).const_mul
      (originalReadback (fullMomentum spatial lambda) row j)).intervalIntegrable 0 T)
  refine actual.symm.trans ?_
  apply intervalIntegral.integral_congr
  intro t _
  simp only [Matrix.mulVec,dotProduct,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem noetherForcing_readback (q : PhysicalResponsePoint) (signal : ℝ→SourceJet Field289)
    (continuousSignal : ContinuousJets signal) (paid : ∀t,HasSourceJets signal t)
    (spatial : Fin 3→ℂ) (lambda : ℂ) (T : ℝ) (row : Fin 289) :
    (originalReadback (fullMomentum spatial lambda)*ᵥnoetherForcing q signal lambda T) row=
      (∫t in (0:ℝ)..T,laplaceWeight lambda t*noetherTimeSource q signal spatial t row)-
        (noetherBoundary q signal spatial lambda T row-noetherBoundary q signal spatial lambda 0 row):=by
  have h:=(intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _=>noetherBoundary_generated q signal continuousSignal.1 paid spatial lambda t row)
    ((noetherDifference_continuous q signal continuousSignal spatial lambda row).intervalIntegrable 0 T))
  simp_rw [noetherDifference_source,mul_sub] at h
  have leftIntegral : IntervalIntegrable (fun t=>laplaceWeight lambda t*noetherTimeSource q signal spatial t row) volume 0 T:=((weight_continuous lambda).mul (noetherTimeSource_continuous q signal continuousSignal spatial row)).intervalIntegrable 0 T
  have rightContinuous : Continuous (fun t=>fullFrequency spatial lambda (fun i=>(noetherHistorySourceJet q signal t i).value) row):=by
    simp_rw [fullFrequency_original]
    change Continuous (fun t=>∑j,originalReadback (fullMomentum spatial lambda) row j*(noetherHistorySourceJet q signal t j).value)
    apply continuous_finsetSum
    intro j _
    exact (noetherHistorySourceJet_continuous q signal continuousSignal j).1.const_mul _
  have rightIntegral : IntervalIntegrable (fun t=>laplaceWeight lambda t*fullFrequency spatial lambda (fun i=>(noetherHistorySourceJet q signal t i).value) row) volume 0 T:=((weight_continuous lambda).mul rightContinuous).intervalIntegrable 0 T
  rw [intervalIntegral.integral_sub leftIntegral rightIntegral,noetherFrequency_integral q signal continuousSignal,
    fullFrequency_original] at h
  linear_combination -h

def noetherField (q : PhysicalResponsePoint) (signal : ℝ→SourceJet Field289)
    (lambda : physicalSpectralDomain q.k) (T : ℝ) : Fin 289→ℂ:=
  PreparationVacuumOriginalGreenFeedback.sourceField
    ⟨fullMomentum (physicalSpatial q.k) lambda.val,lambda.property⟩ (noetherForcing q signal lambda.val T)

theorem noetherField_equation (q : PhysicalResponsePoint) (signal : ℝ→SourceJet Field289)
    (lambda : physicalSpectralDomain q.k) (T : ℝ) :
    originalJacobi (fullMomentum (physicalSpatial q.k) lambda.val)*ᵥnoetherField q signal lambda T=
      noetherForcing q signal lambda.val T-originalRowLift (fullMomentum (physicalSpatial q.k) lambda.val)*ᵥ
        sourceCompatibility (fullMomentum (physicalSpatial q.k) lambda.val) (noetherForcing q signal lambda.val T):=by
  unfold noetherField
  exact original_forced_field (p:=⟨fullMomentum (physicalSpatial q.k) lambda.val,lambda.property⟩)
    (noetherForcing q signal lambda.val T)

def noetherCurvature (q : PhysicalResponsePoint) (signal : ℝ→SourceJet Field289)
    (lambda : physicalSpectralDomain q.k) (T : ℝ) : Fin 36→ℂ:=
  originalReader36 (fullMomentum (physicalSpatial q.k) lambda.val)*ᵥnoetherField q signal lambda T

theorem noetherField_cosources (q : PhysicalResponsePoint) (signal : ℝ→SourceJet Field289)
    (continuousSignal : ContinuousJets signal) (paid : ∀t,HasSourceJets signal t)
    (lambda : physicalSpectralDomain q.k) (T : ℝ) :
    noetherField q signal lambda T=
      originalChange (fullMomentum (physicalSpatial q.k) lambda.val)*ᵥ
        ((contactInverse (fullMomentum (physicalSpatial q.k) lambda.val)+activeProjection*
          (extendedKernel (fullMomentum (physicalSpatial q.k) lambda.val))⁻¹)*ᵥ
          (fun row=>(∫t in (0:ℝ)..T,laplaceWeight lambda.val t*noetherTimeSource q signal (physicalSpatial q.k) t row)-
            (noetherBoundary q signal (physicalSpatial q.k) lambda.val T row-
              noetherBoundary q signal (physicalSpatial q.k) lambda.val 0 row))):=by
  have read : originalReadback (fullMomentum (physicalSpatial q.k) lambda.val)*ᵥnoetherForcing q signal lambda.val T=
      (fun row=>(∫t in (0:ℝ)..T,laplaceWeight lambda.val t*noetherTimeSource q signal (physicalSpatial q.k) t row)-
        (noetherBoundary q signal (physicalSpatial q.k) lambda.val T row-
          noetherBoundary q signal (physicalSpatial q.k) lambda.val 0 row)):=
    funext (noetherForcing_readback q signal continuousSignal paid (physicalSpatial q.k) lambda.val T)
  unfold noetherField PreparationVacuumOriginalGreenFeedback.sourceField sourceGreen
  rw [←Matrix.mulVec_mulVec,←Matrix.mulVec_mulVec,read]

/-- Constant history retains the actual fixed-pi Noether current derivative. -/
theorem noetherForcing_constant (q : PhysicalResponsePoint) (force : Field289) (lambda : ℂ) (T : ℝ) (i : Fin 289) :
    noetherForcing q (fun _=>⟨force,0,0⟩) lambda T i=
      ∫t in (0:ℝ)..T,laplaceWeight lambda t*(-PreparationVacuumNoetherChart.noetherPreparedSlope q (fieldUnit i) force t):=by
  unfold noetherForcing
  apply intervalIntegral.integral_congr
  intro t _
  dsimp only
  rw [noetherHistorySourceJet_constant]


end LowEnergy.SourcePropagationNoetherTime
