import H0mework.Versions.Rc015842c.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationSourcePhysicalPoleEulerPrice
import H0mework.Versions.Rc015842c.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalSourcePropagationActualNativeHistoryReturn

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumElectromagneticIdentity
open SaturationMonoid.PhysicsCore ProofFreeRicherAnholonomicSource
open GaussCoreHilbert CanonicalGradedSpatialSource
open PreparationVacuumMovingPoleGaussReturn PreparationVacuumPhysicalPoleLegDynamics PreparationVacuumPhysicalPoleHalfResponse
open PreparationVacuumFixedMomentumActionReturn PreparationVacuumPhysicalFeedback
open PreparationVacuumJointFieldResponse PreparationVacuumRawJointFeedback
open PreparationVacuumCurrentSignalOperator PreparationVacuumCurrentSignalRealization
open PreparationVacuumMixedFieldReturn PreparationVacuumNoetherChart
open SourcePropagationNativeEulerHistory SourcePropagationNoetherTime SourcePropagationTimeDependentFeedback
open SourcePropagationNativeActionHessian SourcePropagationMotherEulerKernel SourcePropagationMotherResidualDirections
open PreparationVacuumActionFieldLift PreparationVacuumOriginalGreenFeedback PreparationVacuumPropagationPencil
open PreparationVacuumFieldConstraintResponse PreparationVacuumGaugeSourceInjection
open Filter Set MeasureTheory
open scoped BigOperators Topology ContDiff Matrix Interval InnerProductSpace
abbrev PoleWardOp:=H→L[ℂ] H
local instance : NormedAlgebra ℝ PoleWardOp:=NormedAlgebra.restrictScalars ℝ ℂ _
attribute [local irreducible] jointGenerator jointResolvent noetherReader sourceMatterActionOperator
  nativeHessian originalJacobi originalReadback sourcePolePrepared

def sourcePoleActionHistoryKernel (q : PhysicalResponsePoint) (reader : Field289)
    (history : ℝ→Field289) (smooth : ContDiffAt ℝ 1 history 0) (amplitude t : ℝ) : PoleWardOp :=
  historyDual (q.p+q.k) q.F history smooth amplitude t*
    jointResolvent (q.p+q.k) q.F q.z (amplitude • history 0)*
      (fderiv ℝ (sourceMatterActionOperator q.p q.F) (amplitude • history t) reader)*
        jointResolvent q.p q.F q.w (amplitude • history 0)*
          historyPrimal q.p q.F history smooth amplitude t

private theorem poleActionHistory_near (q : PhysicalResponsePoint) (reader : Field289)
    (history : ℝ→Field289) (smooth : ContDiffAt ℝ 1 history 0) (t : ℝ) :
    (fun a=>sourcePoleActionHistoryKernel q reader history smooth a t)=ᶠ[𝓝 0]
      (fun a=>actualPreparedHistoryKernel q reader history smooth a t) := by
  have ray : ContinuousAt (fun a : ℝ=>a • history t) 0:=continuousAt_id.smul continuousAt_const
  have limit : Tendsto (fun a : ℝ=>a • history t) (𝓝 0) (𝓝 (0:Field289)) := by
    simpa only [zero_smul] using ray.tendsto
  have near:=limit.eventually (sourceMatterActionOperator_gradient_near reader q.p q.F)
  filter_upwards [near] with a action
  simp only [sourcePoleActionHistoryKernel,actualPreparedHistoryKernel,action]

def sourcePoleActionHistoryEuler (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (left right : RestStateIndex) (history : ℝ→Field289) (smooth : ContDiffAt ℝ 1 history 0)
    (amplitude t : ℝ) (field : Fin 289) : ℂ :=
  -sourcePoleRead q.epsilon q.precision pL pR left right
    (sourcePoleActionHistoryKernel (sourcePhysicalMaterialPoint q pL pR) (fieldUnit field)
      history smooth amplitude t)

theorem sourcePoleActionHistoryEuler_generated (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (left right : RestStateIndex) (p : Fin 4→ℂ) (a : SignalAmplitude)
    (hz : q.z.im≠0) (hw : q.w.im≠0) (t : ℝ) (future : 0≤t)
    (inside : t<preparedHistoryDuration (sourcePhysicalMaterialPoint q pL pR)
      (nativeTimeHistory (sourceRealSignal p a)) (motherHistoryRegular _ (sourceRealSignal_smooth p a)))
    (field : Fin 289) :
    HasDerivAt (fun r=>sourcePoleActionHistoryEuler q pL pR left right
      (nativeTimeHistory (sourceRealSignal p a)) (motherHistoryRegular _ (sourceRealSignal_smooth p a)) r t field)
      (sourcePoleHistoryJet q.epsilon q.precision pL pR left right
        (sourcePhysicalMaterialPoint q pL pR) p a t field).value 0 := by
  have generated:=actualPreparedHistoryKernel_generated (sourcePhysicalMaterialPoint q pL pR) (fieldUnit field)
    (nativeTimeSignal (sourceRealSignal p a)) (motherHistoryRegular _ (sourceRealSignal_smooth p a)) hz hw t future inside
  have action:=generated.congr_of_eventuallyEq
    (poleActionHistory_near (sourcePhysicalMaterialPoint q pL pR) (fieldUnit field)
      (nativeTimeHistory (sourceRealSignal p a)) (motherHistoryRegular _ (sourceRealSignal_smooth p a)) t)
  have read:=(((sourcePoleRead q.epsilon q.precision pL pR left right).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0 action).neg
  convert! read using 1

private theorem poleJet_continuous (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (left right : RestStateIndex) (p : Fin 4→ℂ) (a : SignalAmplitude) (field : Fin 289) :
    ContinuousJets (fun t=>sourcePoleHistoryJet q.epsilon q.precision pL pR left right
      (sourcePhysicalMaterialPoint q pL pR) p a t field) := by
  have generated:=noetherHistoryOperatorJet_continuous (sourcePhysicalMaterialPoint q pL pR) (fieldUnit field)
    (nativeTimeSignal (sourceRealSignal p a)) (sourceTimeSignal_continuous p a)
  have first : Continuous (fun t=>sourcePoleRead q.epsilon q.precision pL pR left right
      (noetherHistoryOperatorJet (sourcePhysicalMaterialPoint q pL pR) (fieldUnit field)
        (nativeTimeSignal (sourceRealSignal p a)) t).value):=
    (sourcePoleRead q.epsilon q.precision pL pR left right).continuous.comp generated.1
  have second : Continuous (fun t=>sourcePoleRead q.epsilon q.precision pL pR left right
      (noetherHistoryOperatorJet (sourcePhysicalMaterialPoint q pL pR) (fieldUnit field)
        (nativeTimeSignal (sourceRealSignal p a)) t).first):=
    (sourcePoleRead q.epsilon q.precision pL pR left right).continuous.comp generated.2.1
  have third : Continuous (fun t=>sourcePoleRead q.epsilon q.precision pL pR left right
      (noetherHistoryOperatorJet (sourcePhysicalMaterialPoint q pL pR) (fieldUnit field)
        (nativeTimeSignal (sourceRealSignal p a)) t).second):=
    (sourcePoleRead q.epsilon q.precision pL pR left right).continuous.comp generated.2.2
  exact ⟨first.neg,second.neg,third.neg⟩

private theorem pole_weight_derivative (lambda : ℂ) (t : ℝ) :
    HasDerivAt (laplaceWeight lambda) (-lambda*laplaceWeight lambda t) t := by
  unfold laplaceWeight
  convert! (((Complex.ofRealCLM.hasFDerivAt).hasDerivAt.const_mul (-lambda)).cexp) using 1
  simp [Complex.ofRealCLM]
  ring

private theorem pole_weighted_boundary (j : ℝ→SourceJet ℂ) (lambda : ℂ)
    (t : ℝ) (paid : HasSourceJets j t) (n : Fin 3) :
    HasDerivAt (fun s=>laplaceWeight lambda s*initialCoSource lambda (j s) n)
      (laplaceWeight lambda t*(jetEntry (j t) n-lambda^n.val*(j t).value)) t := by
  fin_cases n
  · simpa [initialCoSource,jetEntry] using hasDerivAt_const t (0:ℂ)
  · have generated:=(pole_weight_derivative lambda t).mul paid.1
    change HasDerivAt (fun s=>laplaceWeight lambda s*(j s).value)
      (laplaceWeight lambda t*((j t).first-lambda^1*(j t).value)) t
    convert! generated using 1
    ring
  · have generated:=(pole_weight_derivative lambda t).mul ((paid.1.const_mul lambda).add paid.2)
    change HasDerivAt (fun s=>laplaceWeight lambda s*(lambda*(j s).value+(j s).first))
      (laplaceWeight lambda t*((j t).second-lambda^2*(j t).value)) t
    convert! generated using 1
    change _=(-lambda*laplaceWeight lambda t*(lambda*(j t).value+(j t).first)+
      laplaceWeight lambda t*(lambda*(j t).first+(j t).second))
    ring

private theorem pole_list_derivative {ι : Type*} (entries : List ι) (f df : ι→ℝ→ℂ) (t : ℝ)
    (paid : ∀x∈entries,HasDerivAt (f x) (df x t) t) :
    HasDerivAt (fun s=>(entries.map (fun x=>f x s)).sum) ((entries.map (fun x=>df x t)).sum) t := by
  induction entries with
  | nil=>exact hasDerivAt_const t 0
  | cons x rest ih=>simpa only [List.map_cons,List.sum_cons] using!
      (paid x (by simp)).add (ih (fun y member=>paid y (by simp [member])))

private theorem pole_list_continuous {ι : Type*} (entries : List ι) (f : ι→ℝ→ℂ)
    (paid : ∀x∈entries,Continuous (f x)) : Continuous (fun t=>(entries.map (fun x=>f x t)).sum) := by
  induction entries with
  | nil=>exact continuous_const
  | cons x rest ih=>simpa only [List.map_cons,List.sum_cons] using!
      (paid x (by simp)).add (ih (fun y member=>paid y (by simp [member])))

private def pole_forcing (j : ℝ→Fin 289→SourceJet ℂ) (lambda : ℂ) (T : ℝ) : Fin 289→ℂ :=
  fun field=>∫t in (0:ℝ)..T,laplaceWeight lambda t*(j t field).value

private def pole_timeSource (j : ℝ→Fin 289→SourceJet ℂ) (spatial : Fin 3→ℂ) (t : ℝ) (row : Fin 289) : ℂ :=
  (nativeReadbackTerms.attach.map (fun entry=>if row=entry.val.row then termSpatial spatial entry.val*
    jetEntry (j t entry.val.column) (nativeTimeOrder entry) else 0)).sum

private def pole_boundary (j : ℝ→Fin 289→SourceJet ℂ) (spatial : Fin 3→ℂ)
    (lambda : ℂ) (t : ℝ) (row : Fin 289) : ℂ :=
  (nativeReadbackTerms.attach.map (fun entry=>if row=entry.val.row then termSpatial spatial entry.val*
    (laplaceWeight lambda t*initialCoSource lambda (j t entry.val.column) (nativeTimeOrder entry)) else 0)).sum

private def pole_difference (j : ℝ→Fin 289→SourceJet ℂ) (spatial : Fin 3→ℂ)
    (lambda : ℂ) (t : ℝ) (row : Fin 289) : ℂ :=
  (nativeReadbackTerms.attach.map (fun entry=>if row=entry.val.row then termSpatial spatial entry.val*
    (laplaceWeight lambda t*(jetEntry (j t entry.val.column) (nativeTimeOrder entry)-
      lambda^(nativeTimeOrder entry).val*(j t entry.val.column).value)) else 0)).sum

private theorem pole_boundary_generated (j : ℝ→Fin 289→SourceJet ℂ)
    (paid : ∀field t,HasSourceJets (fun s=>j s field) t) (spatial : Fin 3→ℂ)
    (lambda : ℂ) (t : ℝ) (row : Fin 289) :
    HasDerivAt (fun s=>pole_boundary j spatial lambda s row) (pole_difference j spatial lambda t row) t := by
  unfold pole_boundary pole_difference
  convert! pole_list_derivative nativeReadbackTerms.attach
    (fun entry s=>if row=entry.val.row then termSpatial spatial entry.val*
      (laplaceWeight lambda s*initialCoSource lambda (j s entry.val.column) (nativeTimeOrder entry)) else 0)
    (fun entry s=>if row=entry.val.row then termSpatial spatial entry.val*
      (laplaceWeight lambda s*(jetEntry (j s entry.val.column) (nativeTimeOrder entry)-
        lambda^(nativeTimeOrder entry).val*(j s entry.val.column).value)) else 0) t (by
      intro entry _
      by_cases same : row=entry.val.row
      · simp only [if_pos same]
        exact (pole_weighted_boundary _ lambda t (paid entry.val.column t) _).const_mul _
      · simp only [if_neg same]
        exact hasDerivAt_const t 0) using 1

private theorem pole_entry_continuous (j : ℝ→SourceJet ℂ) (continuousJet : ContinuousJets j) (n : Fin 3) :
    Continuous (fun t=>jetEntry (j t) n) := by
  fin_cases n
  · exact continuousJet.1
  · exact continuousJet.2.1
  · exact continuousJet.2.2

private theorem pole_weight_continuous (lambda : ℂ) : Continuous (laplaceWeight lambda) := by
  unfold laplaceWeight
  fun_prop

private theorem pole_difference_continuous (j : ℝ→Fin 289→SourceJet ℂ)
    (continuousJet : ∀field,ContinuousJets (fun t=>j t field)) (spatial : Fin 3→ℂ) (lambda : ℂ) (row : Fin 289) :
    Continuous (fun t=>pole_difference j spatial lambda t row) := by
  unfold pole_difference
  apply pole_list_continuous
  intro entry _
  by_cases same : row=entry.val.row
  · simp only [if_pos same]
    have jet:=continuousJet entry.val.column
    exact ((pole_weight_continuous lambda).mul ((pole_entry_continuous _ jet _).sub (jet.1.const_mul _))).const_mul _
  · simp only [if_neg same]
    exact continuous_const

private theorem pole_timeSource_continuous (j : ℝ→Fin 289→SourceJet ℂ)
    (continuousJet : ∀field,ContinuousJets (fun t=>j t field)) (spatial : Fin 3→ℂ) (row : Fin 289) :
    Continuous (fun t=>pole_timeSource j spatial t row) := by
  unfold pole_timeSource
  apply pole_list_continuous
  intro entry _
  by_cases same : row=entry.val.row
  · simp only [if_pos same]
    exact (pole_entry_continuous _ (continuousJet entry.val.column) _).const_mul _
  · simp only [if_neg same]
    exact continuous_const

private theorem pole_weighted_list {ι : Type*} (entries : List ι) (left right : ι→ℂ) (weight : ℂ) :
    (entries.map (fun x=>weight*(left x-right x))).sum=
      weight*((entries.map left).sum-(entries.map right).sum) := by
  induction entries with
  | nil=>simp
  | cons x rest ih=>simp only [List.map_cons,List.sum_cons,ih];ring

private theorem pole_difference_source (j : ℝ→Fin 289→SourceJet ℂ) (spatial : Fin 3→ℂ)
    (lambda : ℂ) (t : ℝ) (row : Fin 289) :
    pole_difference j spatial lambda t row=laplaceWeight lambda t*
      (pole_timeSource j spatial t row-fullFrequency spatial lambda (fun field=>(j t field).value) row) := by
  unfold pole_difference pole_timeSource fullFrequency
  have difference:=pole_weighted_list nativeReadbackTerms.attach
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

private theorem pole_frequency_integral (j : ℝ→Fin 289→SourceJet ℂ)
    (continuousJet : ∀field,ContinuousJets (fun t=>j t field)) (spatial : Fin 3→ℂ)
    (lambda : ℂ) (T : ℝ) (row : Fin 289) :
    (∫t in (0:ℝ)..T,laplaceWeight lambda t*fullFrequency spatial lambda (fun field=>(j t field).value) row)=
      fullFrequency spatial lambda (pole_forcing j lambda T) row := by
  simp_rw [fullFrequency_original]
  symm
  change (∑field,originalReadback (fullMomentum spatial lambda) row field*pole_forcing j lambda T field)=_
  simp_rw [pole_forcing,←intervalIntegral.integral_const_mul]
  have exchange:=intervalIntegral.integral_finsetSum (s:=Finset.univ) (μ:=volume)
    (f:=fun (field : Fin 289) t=>originalReadback (fullMomentum spatial lambda) row field*
      (laplaceWeight lambda t*(j t field).value))
    (fun field _=>(((pole_weight_continuous lambda).mul (continuousJet field).1).const_mul
      (originalReadback (fullMomentum spatial lambda) row field)).intervalIntegrable 0 T)
  refine exchange.symm.trans ?_
  apply intervalIntegral.integral_congr
  intro t _
  simp only [Matrix.mulVec,dotProduct,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro field _
  ring

private theorem pole_forcing_readback (j : ℝ→Fin 289→SourceJet ℂ)
    (continuousJet : ∀field,ContinuousJets (fun t=>j t field))
    (paid : ∀field t,HasSourceJets (fun s=>j s field) t) (spatial : Fin 3→ℂ)
    (lambda : ℂ) (T : ℝ) (row : Fin 289) :
    (originalReadback (fullMomentum spatial lambda)*ᵥpole_forcing j lambda T) row=
      (∫t in (0:ℝ)..T,laplaceWeight lambda t*pole_timeSource j spatial t row)-
        (pole_boundary j spatial lambda T row-pole_boundary j spatial lambda 0 row) := by
  have boundary:=(intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _=>pole_boundary_generated j paid spatial lambda t row)
    ((pole_difference_continuous j continuousJet spatial lambda row).intervalIntegrable 0 T))
  simp_rw [pole_difference_source,mul_sub] at boundary
  have source : IntervalIntegrable (fun t=>laplaceWeight lambda t*pole_timeSource j spatial t row) volume 0 T:=
    ((pole_weight_continuous lambda).mul (pole_timeSource_continuous j continuousJet spatial row)).intervalIntegrable 0 T
  have frequency : IntervalIntegrable (fun t=>laplaceWeight lambda t*fullFrequency spatial lambda (fun field=>(j t field).value) row) volume 0 T := by
    simp_rw [fullFrequency_original]
    exact ((pole_weight_continuous lambda).mul (continuous_finsetSum _ (fun field _=>
      (continuousJet field).1.const_mul (originalReadback (fullMomentum spatial lambda) row field)))).intervalIntegrable 0 T
  rw [intervalIntegral.integral_sub source frequency,pole_frequency_integral j continuousJet,
    fullFrequency_original] at boundary
  linear_combination -boundary

abbrev sourcePoleQuantumJet (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (left right : RestStateIndex) (p : Fin 4→ℂ) (a : SignalAmplitude) (t : ℝ) (field : Fin 289) : SourceJet ℂ :=
  sourcePoleHistoryJet q.epsilon q.precision pL pR left right (sourcePhysicalMaterialPoint q pL pR) p a t field

def sourcePoleQuantumForcing (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (left right : RestStateIndex) (p : Fin 4→ℂ) (a : SignalAmplitude) (lambda : ℂ) (T : ℝ) : Fin 289→ℂ :=
  pole_forcing (sourcePoleQuantumJet q pL pR left right p a) lambda T

def sourcePoleQuantumTimeSource (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (left right : RestStateIndex) (p : Fin 4→ℂ) (a : SignalAmplitude) (spatial : Fin 3→ℂ) (t : ℝ) (row : Fin 289) : ℂ :=
  pole_timeSource (sourcePoleQuantumJet q pL pR left right p a) spatial t row

def sourcePoleQuantumBoundary (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (left right : RestStateIndex) (p : Fin 4→ℂ) (a : SignalAmplitude) (spatial : Fin 3→ℂ)
    (lambda : ℂ) (t : ℝ) (row : Fin 289) : ℂ :=
  pole_boundary (sourcePoleQuantumJet q pL pR left right p a) spatial lambda t row

theorem sourcePoleQuantumForcing_ward (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (left right : RestStateIndex) (p : Fin 4→ℂ) (a : SignalAmplitude) (spatial : Fin 3→ℂ)
    (lambda : ℂ) (T : ℝ) (row : Fin 289) :
    (originalReadback (fullMomentum spatial lambda)*ᵥsourcePoleQuantumForcing q pL pR left right p a lambda T) row=
      (∫t in (0:ℝ)..T,laplaceWeight lambda t*sourcePoleQuantumTimeSource q pL pR left right p a spatial t row)-
        (sourcePoleQuantumBoundary q pL pR left right p a spatial lambda T row-
          sourcePoleQuantumBoundary q pL pR left right p a spatial lambda 0 row) :=
  pole_forcing_readback _ (poleJet_continuous q pL pR left right p a)
    (fun field t=>sourcePoleHistoryJet_generated q.epsilon q.precision pL pR left right
      (sourcePhysicalMaterialPoint q pL pR) p a t field) spatial lambda T row

def sourcePoleQuantumWindow (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (left right : RestStateIndex) (p : Fin 4→ℂ) (a : SignalAmplitude) (lambda : ℂ) (T : ℝ) : Fin 289→ℂ :=
  sourcePoleQuantumForcing q pL pR left right p a lambda T+
    Complex.I • sourcePoleQuantumForcing q pL pR left right p (sourceQuadrature a) lambda T

def sourcePoleQuantumCosource (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (left right : RestStateIndex) (p : Fin 4→ℂ) (a : SignalAmplitude) (spatial : Fin 3→ℂ)
    (lambda : ℂ) (T : ℝ) : Fin 289→ℂ :=fun row=>
  ((∫t in (0:ℝ)..T,laplaceWeight lambda t*sourcePoleQuantumTimeSource q pL pR left right p a spatial t row)-
    (sourcePoleQuantumBoundary q pL pR left right p a spatial lambda T row-
      sourcePoleQuantumBoundary q pL pR left right p a spatial lambda 0 row))+
  Complex.I*((∫t in (0:ℝ)..T,laplaceWeight lambda t*
      sourcePoleQuantumTimeSource q pL pR left right p (sourceQuadrature a) spatial t row)-
    (sourcePoleQuantumBoundary q pL pR left right p (sourceQuadrature a) spatial lambda T row-
      sourcePoleQuantumBoundary q pL pR left right p (sourceQuadrature a) spatial lambda 0 row))

theorem sourcePoleQuantumWindow_ward (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (left right : RestStateIndex) (p : Fin 4→ℂ) (a : SignalAmplitude) (spatial : Fin 3→ℂ) (lambda : ℂ) (T : ℝ) :
    originalReadback (fullMomentum spatial lambda) *ᵥ sourcePoleQuantumWindow q pL pR left right p a lambda T=
      sourcePoleQuantumCosource q pL pR left right p a spatial lambda T := by
  rw [sourcePoleQuantumWindow,Matrix.mulVec_add,Matrix.mulVec_smul]
  funext row
  simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul,sourcePoleQuantumCosource]
  rw [sourcePoleQuantumForcing_ward,sourcePoleQuantumForcing_ward]

theorem sourcePoleQuantumWindow_compatibility (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (left right : RestStateIndex) (p : Fin 4→ℂ) (a : SignalAmplitude) (spatial : Fin 3→ℂ) (lambda : ℂ) (T : ℝ) :
    sourceCompatibility (fullMomentum spatial lambda) (sourcePoleQuantumWindow q pL pR left right p a lambda T)=
      nullProjection *ᵥ sourcePoleQuantumCosource q pL pR left right p a spatial lambda T := by
  rw [sourceCompatibility,sourcePoleQuantumWindow_ward]

theorem sourcePoleQuantumWindow_native (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (left right : RestStateIndex) (p : Fin 4→ℂ) (a : SignalAmplitude) (spatial : Fin 3→ℂ) (lambda : ℂ) (T : ℝ)
    (regular : fullMomentum spatial lambda∈regularSource) :
    nativeFourierHessian nativeHessian (fullMomentum spatial lambda) *ᵥ
      PreparationVacuumOriginalGreenFeedback.sourceField ⟨fullMomentum spatial lambda,regular⟩
        (sourcePoleQuantumWindow q pL pR left right p a lambda T)=
      sourcePoleQuantumWindow q pL pR left right p a lambda T-
        originalRowLift (fullMomentum spatial lambda) *ᵥ
          (nullProjection *ᵥ sourcePoleQuantumCosource q pL pR left right p a spatial lambda T) := by
  have returned:=nativeAction_sourceField (⟨fullMomentum spatial lambda,regular⟩:regularSource)
    (sourcePoleQuantumWindow q pL pR left right p a lambda T)
  simpa only [sourcePoleQuantumWindow_compatibility] using returned

theorem sourcePoleQuantumWindow_native36 (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (left right : RestStateIndex) (p : Fin 4→ℂ) (a : SignalAmplitude) (spatial : Fin 3→ℂ) (lambda : ℂ) (T : ℝ)
    (regular : fullMomentum spatial lambda∈regularSource) :
    originalReader36 (fullMomentum spatial lambda) *ᵥ
      (nativeFourierHessian nativeHessian (fullMomentum spatial lambda) *ᵥ
        PreparationVacuumOriginalGreenFeedback.sourceField ⟨fullMomentum spatial lambda,regular⟩
          (sourcePoleQuantumWindow q pL pR left right p a lambda T))=
      originalReader36 (fullMomentum spatial lambda) *ᵥ sourcePoleQuantumWindow q pL pR left right p a lambda T-
        originalReader36 (fullMomentum spatial lambda) *ᵥ
          (originalRowLift (fullMomentum spatial lambda) *ᵥ
            (nullProjection *ᵥ sourcePoleQuantumCosource q pL pR left right p a spatial lambda T)) := by
  rw [sourcePoleQuantumWindow_native,Matrix.mulVec_sub]

private theorem poleOperatorJet_initial (q : PhysicalResponsePoint) (reader : Field289)
    (signal : ℝ→SourceJet Field289) :
    (noetherHistoryOperatorJet q reader signal 0).value=
      slopeInitial q reader (signal 0).value+
        jointResolvent (q.p+q.k) q.F q.z 0*
          (noetherReaderContact reader (signal 0).value q.p q.F-rawReaderContact reader (signal 0).value q.p q.F)*
            jointResolvent q.p q.F q.w 0 := by
  rw [noetherHistoryOperatorJet_value,historyOperator_initial,neg_zero]
  simp only [physicalTime_initial,one_mul,mul_one]

theorem sourcePoleQuantumJet_initial (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (left right : RestStateIndex) (p : Fin 4→ℂ) (a : SignalAmplitude) (field : Fin 289) :
    (sourcePoleQuantumJet q pL pR left right p a 0 field).value=
      -sourcePoleRead q.epsilon q.precision pL pR left right
        (slopeInitial (sourcePhysicalMaterialPoint q pL pR) (fieldUnit field)
          (nativeTimeHistory (sourceRealSignal p a) 0)+
          jointResolvent pL q.F q.z 0*
            (noetherReaderContact (fieldUnit field) (nativeTimeHistory (sourceRealSignal p a) 0) pR q.F-
              rawReaderContact (fieldUnit field) (nativeTimeHistory (sourceRealSignal p a) 0) pR q.F)*
              jointResolvent pR q.F q.w 0) := by
  have operator:=poleOperatorJet_initial (sourcePhysicalMaterialPoint q pL pR) (fieldUnit field)
    (nativeTimeSignal (sourceRealSignal p a))
  rw [sourcePhysicalMaterialPoint_left] at operator
  have observed:=congrArg (fun A : PoleWardOp=> -sourcePoleRead q.epsilon q.precision pL pR left right A) operator
  simpa only [sourcePoleQuantumJet,sourcePoleHistoryJet,negativeJet,pairJet,sourcePoleRead_actual,
    sourcePhysicalMaterialPoint,nativeTimeSignal] using observed

private theorem poleActionHistoryKernel_base (q : PhysicalResponsePoint) (reader : Field289)
    (history : ℝ→Field289) (smooth : ContDiffAt ℝ 1 history 0) (t : ℝ) (future : 0≤t)
    (inside : t<preparedHistoryDuration q history smooth) :
    sourcePoleActionHistoryKernel q reader history smooth 0 t=
      physicalTime (q.p+q.k) q.F (-t) 0*jointResolvent (q.p+q.k) q.F q.z 0*
        rawReader reader q.p q.F 0*jointResolvent q.p q.F q.w 0*physicalTime q.p q.F t 0 := by
  have bounds:=lt_min_iff.mp inside
  have timeR : t∈Ioo (-(sourceHistoryWindow q.p q.F history smooth).duration)
      (sourceHistoryWindow q.p q.F history smooth).duration := by
    constructor
    · linarith [(sourceHistoryWindow q.p q.F history smooth).duration_positive]
    · exact bounds.1
  have timeL : t∈Ioo (-(sourceHistoryWindow (q.p+q.k) q.F history smooth).duration)
      (sourceHistoryWindow (q.p+q.k) q.F history smooth).duration := by
    constructor
    · linarith [(sourceHistoryWindow (q.p+q.k) q.F history smooth).duration_positive]
    · exact bounds.2
  have primal:=historyPrimal_zero q.p q.F history smooth t
    ((sourceHistoryWindow q.p q.F history smooth).time_inside timeR)
  have dual:=historyDual_zero (q.p+q.k) q.F history smooth t
    ((sourceHistoryWindow (q.p+q.k) q.F history smooth).time_inside timeL)
  unfold sourcePoleActionHistoryKernel
  rw [primal,dual]
  simp only [zero_smul,sourceMatterActionOperator_gradient]

theorem sourcePoleActionHistoryEuler_base (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (left right : RestStateIndex) (p : Fin 4→ℂ) (a : SignalAmplitude) (t : ℝ) (future : 0≤t)
    (inside : t<preparedHistoryDuration (sourcePhysicalMaterialPoint q pL pR)
      (nativeTimeHistory (sourceRealSignal p a)) (motherHistoryRegular _ (sourceRealSignal_smooth p a)))
    (field : Fin 289) :
    sourcePoleActionHistoryEuler q pL pR left right (nativeTimeHistory (sourceRealSignal p a))
      (motherHistoryRegular _ (sourceRealSignal_smooth p a)) 0 t field=
      sourcePoleActionEuler q pL pR left right 0 t field := by
  have kernel:=poleActionHistoryKernel_base (sourcePhysicalMaterialPoint q pL pR) (fieldUnit field)
    (nativeTimeHistory (sourceRealSignal p a)) (motherHistoryRegular _ (sourceRealSignal_smooth p a)) t future inside
  have momentum : pR+(pL-pR)=pL := by
    funext axis
    simp only [Pi.add_apply,Pi.sub_apply]
    ring
  have observed:=congrArg (fun A : PoleWardOp=> -sourcePoleRead q.epsilon q.precision pL pR left right A) kernel
  have shared:=sourcePoleActionEuler_source q pL pR left right t field
  rw [sourcePhysicalMaterialPoint_left] at observed
  simp only [sourcePhysicalMaterialPoint] at observed
  have baseline : sourcePoleActionHistoryEuler q pL pR left right (nativeTimeHistory (sourceRealSignal p a))
      (motherHistoryRegular _ (sourceRealSignal_smooth p a)) 0 t field=
      -sourcePoleRead q.epsilon q.precision pL pR left right
        (physicalTime pL q.F (-t) 0*jointResolvent pL q.F q.z 0*
          rawReader (fieldUnit field) pR q.F 0*jointResolvent pR q.F q.w 0*physicalTime pR q.F t 0) := observed
  rw [baseline,shared]
  congr 1
  simp only [fiveKernel,momentum]

end LowEnergy.PreparationVacuumElectromagneticIdentity
