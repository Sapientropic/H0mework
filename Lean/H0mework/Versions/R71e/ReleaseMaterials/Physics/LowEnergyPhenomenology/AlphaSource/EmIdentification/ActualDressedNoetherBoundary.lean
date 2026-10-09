import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedNoetherResponse

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualDressedNoether
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open CanonicalGradedSpatialSource PreparationVacuumMixedFieldReturn
open PreparationVacuumPhysicalFeedback PreparationVacuumOriginalGreenFeedback
open PreparationVacuumActionFieldLift PreparationVacuumGaugeSourceInjection
open ActualDressedFullCoulomb MeasureTheory Filter
open scoped Matrix BigOperators Topology Interval
attribute [local irreducible] originalJacobi originalReadback originalChange sourceGreen
  PreparationVacuumOriginalGreenFeedback.sourceField dressedNoetherJet

private theorem derivative_list_sum {ι : Type*} (entries : List ι) (f df : ι→ℝ→ℂ) (t : ℝ)
    (paid : ∀a∈entries,HasDerivAt (f a) (df a t) t) :
    HasDerivAt (fun s=>(entries.map (fun a=>f a s)).sum) ((entries.map (fun a=>df a t)).sum) t := by
  induction entries with
  | nil => exact hasDerivAt_const t 0
  | cons a rest ih =>
    simpa only [List.map_cons,List.sum_cons] using!
      (paid a (by simp)).add (ih (fun b hb=>paid b (by simp [hb])))

private theorem continuous_list_sum {ι : Type*} (entries : List ι) (f : ι→ℝ→ℂ)
    (paid : ∀a∈entries,Continuous (f a)) : Continuous (fun t=>(entries.map (fun a=>f a t)).sum) := by
  induction entries with
  | nil => exact continuous_const
  | cons a rest ih =>
    simpa only [List.map_cons,List.sum_cons] using!
      (paid a (by simp)).add (ih (fun b hb=>paid b (by simp [hb])))

private theorem weighted_boundary_derivative (j : ℝ→SourceJet ℂ) (lambda : ℂ) (t : ℝ)
    (paid : HasSourceJets j t) (n : Fin 3) :
    HasDerivAt (fun s=>laplaceWeight lambda s*initialCoSource lambda (j s) n)
      (laplaceWeight lambda t*(jetEntry (j t) n-lambda^n.val*(j t).value)) t := by
  run_tac
    let name:=(Lean.Name.num `_private.H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationPhysicalFullSourceWindow 0) ++
      `LowEnergy.PreparationVacuumPhysicalFeedback.weightedBoundaryDerivative
    Lean.Elab.Tactic.evalTactic (← `(tactic| exact $(Lean.mkIdent name) $(Lean.mkIdent `j) $(Lean.mkIdent `lambda)
      $(Lean.mkIdent `t) $(Lean.mkIdent `paid) $(Lean.mkIdent `n)))

private def jetForcing (J : ℝ→Fin 289→SourceJet ℂ) (lambda : ℂ) (T : ℝ) : Fin 289→ℂ :=
  fun i=>∫t in (0:ℝ)..T,laplaceWeight lambda t*(J t i).value

private def jetTimeSource (J : ℝ→Fin 289→SourceJet ℂ)
    (spatial : Fin 3→ℂ) (t : ℝ) (row : Fin 289) : ℂ :=
  (nativeReadbackTerms.attach.map (fun a=>if row=a.val.row then termSpatial spatial a.val*
    jetEntry (J t a.val.column) (nativeTimeOrder a) else 0)).sum

private def jetBoundary (J : ℝ→Fin 289→SourceJet ℂ)
    (spatial : Fin 3→ℂ) (lambda : ℂ) (t : ℝ) (row : Fin 289) : ℂ :=
  (nativeReadbackTerms.attach.map (fun a=>if row=a.val.row then termSpatial spatial a.val*
    (laplaceWeight lambda t*initialCoSource lambda (J t a.val.column) (nativeTimeOrder a)) else 0)).sum

private def jetDifference (J : ℝ→Fin 289→SourceJet ℂ)
    (spatial : Fin 3→ℂ) (lambda : ℂ) (t : ℝ) (row : Fin 289) : ℂ :=
  (nativeReadbackTerms.attach.map (fun a=>if row=a.val.row then termSpatial spatial a.val*
    (laplaceWeight lambda t*(jetEntry (J t a.val.column) (nativeTimeOrder a)-
      lambda^(nativeTimeOrder a).val*(J t a.val.column).value)) else 0)).sum

private theorem jet_boundary_generated (J : ℝ→Fin 289→SourceJet ℂ)
    (paid : ∀t i,HasSourceJets (fun s=>J s i) t)
    (spatial : Fin 3→ℂ) (lambda : ℂ) (t : ℝ) (row : Fin 289) :
    HasDerivAt (fun s=>jetBoundary J spatial lambda s row) (jetDifference J spatial lambda t row) t := by
  unfold jetBoundary jetDifference
  convert! derivative_list_sum nativeReadbackTerms.attach
    (fun a s=>if row=a.val.row then termSpatial spatial a.val*
      (laplaceWeight lambda s*initialCoSource lambda (J s a.val.column) (nativeTimeOrder a)) else 0)
    (fun a s=>if row=a.val.row then termSpatial spatial a.val*
      (laplaceWeight lambda s*(jetEntry (J s a.val.column) (nativeTimeOrder a)-
        lambda^(nativeTimeOrder a).val*(J s a.val.column).value)) else 0) t (by
      intro a _
      by_cases same : row=a.val.row
      · simp only [if_pos same]
        exact (weighted_boundary_derivative _ lambda t (paid t a.val.column) _).const_mul _
      · simp only [if_neg same]
        exact hasDerivAt_const t 0) using 1

private theorem weight_continuous (lambda : ℂ) : Continuous (laplaceWeight lambda) := by
  unfold laplaceWeight
  fun_prop

private theorem jet_entry_continuous (J : ℝ→Fin 289→SourceJet ℂ)
    (paid : ∀i,ContinuousJets (fun t=>J t i)) (i : Fin 289) (n : Fin 3) :
    Continuous (fun t=>jetEntry (J t i) n) := by
  fin_cases n
  · exact (paid i).1
  · exact (paid i).2.1
  · exact (paid i).2.2

private theorem jet_difference_continuous (J : ℝ→Fin 289→SourceJet ℂ)
    (paid : ∀i,ContinuousJets (fun t=>J t i))
    (spatial : Fin 3→ℂ) (lambda : ℂ) (row : Fin 289) :
    Continuous (fun t=>jetDifference J spatial lambda t row) := by
  unfold jetDifference
  apply continuous_list_sum
  intro a _
  by_cases same : row=a.val.row
  · simp only [if_pos same]
    exact ((weight_continuous lambda).mul ((jet_entry_continuous J paid _ _).sub
      ((paid a.val.column).1.const_mul _))).const_mul _
  · simp only [if_neg same]
    exact continuous_const

private theorem weighted_list_difference {ι : Type*} (entries : List ι)
    (left right : ι→ℂ) (weight : ℂ) :
    (entries.map (fun a=>weight*(left a-right a))).sum=
      weight*((entries.map left).sum-(entries.map right).sum) := by
  induction entries with
  | nil => simp
  | cons a rest ih => simp only [List.map_cons,List.sum_cons,ih]; ring

private theorem jet_difference_source (J : ℝ→Fin 289→SourceJet ℂ)
    (spatial : Fin 3→ℂ) (lambda : ℂ) (t : ℝ) (row : Fin 289) :
    jetDifference J spatial lambda t row=laplaceWeight lambda t*
      (jetTimeSource J spatial t row-fullFrequency spatial lambda (fun i=>(J t i).value) row) := by
  unfold jetDifference jetTimeSource fullFrequency
  have actual:=weighted_list_difference nativeReadbackTerms.attach
    (fun a=>if row=a.val.row then termSpatial spatial a.val*jetEntry (J t a.val.column) (nativeTimeOrder a) else 0)
    (fun a=>if row=a.val.row then termSpatial spatial a.val*lambda^(nativeTimeOrder a).val*(J t a.val.column).value else 0)
    (laplaceWeight lambda t)
  apply Eq.trans _ actual
  congr 1
  apply List.map_congr_left
  intro a _
  by_cases same : row=a.val.row
  · simp only [if_pos same]; ring
  · simp only [if_neg same]; ring

private theorem jet_frequency_integral (J : ℝ→Fin 289→SourceJet ℂ)
    (paid : ∀i,ContinuousJets (fun t=>J t i))
    (spatial : Fin 3→ℂ) (lambda : ℂ) (T : ℝ) (row : Fin 289) :
    (∫t in (0:ℝ)..T,laplaceWeight lambda t*
      fullFrequency spatial lambda (fun i=>(J t i).value) row)=
      fullFrequency spatial lambda (jetForcing J lambda T) row := by
  simp_rw [fullFrequency_original]
  symm
  change (∑i,originalReadback (fullMomentum spatial lambda) row i*jetForcing J lambda T i)=_
  simp_rw [jetForcing,←intervalIntegral.integral_const_mul]
  have actual:=intervalIntegral.integral_finsetSum (s:=Finset.univ) (μ:=volume)
    (f:=fun (i : Fin 289) t=>originalReadback (fullMomentum spatial lambda) row i*
      (laplaceWeight lambda t*(J t i).value))
    (fun i _=>(((weight_continuous lambda).mul (paid i).1).const_mul _).intervalIntegrable 0 T)
  refine actual.symm.trans ?_
  apply intervalIntegral.integral_congr
  intro t _
  simp only [Matrix.mulVec,dotProduct,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

private theorem jet_forcing_readback (J : ℝ→Fin 289→SourceJet ℂ)
    (continuousJ : ∀i,ContinuousJets (fun t=>J t i)) (paid : ∀t i,HasSourceJets (fun s=>J s i) t)
    (spatial : Fin 3→ℂ) (lambda : ℂ) (T : ℝ) (row : Fin 289) :
    (originalReadback (fullMomentum spatial lambda)*ᵥjetForcing J lambda T) row=
      (∫t in (0:ℝ)..T,laplaceWeight lambda t*jetTimeSource J spatial t row)-
        (jetBoundary J spatial lambda T row-jetBoundary J spatial lambda 0 row) := by
  have boundary:=intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _=>jet_boundary_generated J paid spatial lambda t row)
    ((jet_difference_continuous J continuousJ spatial lambda row).intervalIntegrable 0 T)
  simp_rw [jet_difference_source,mul_sub] at boundary
  have timeContinuous : Continuous (fun t=>jetTimeSource J spatial t row) := by
    unfold jetTimeSource
    apply continuous_list_sum
    intro a _
    by_cases same : row=a.val.row
    · simp only [if_pos same]
      exact (jet_entry_continuous J continuousJ _ _).const_mul _
    · simp only [if_neg same]
      exact continuous_const
  have frequencyContinuous : Continuous
      (fun t=>fullFrequency spatial lambda (fun i=>(J t i).value) row) := by
    simp_rw [fullFrequency_original]
    change Continuous (fun t=>∑i,originalReadback (fullMomentum spatial lambda) row i*(J t i).value)
    apply continuous_finsetSum
    intro i _
    exact (continuousJ i).1.const_mul _
  have timeIntegral : IntervalIntegrable
      (fun t=>laplaceWeight lambda t*jetTimeSource J spatial t row) volume 0 T :=
    ((weight_continuous lambda).mul timeContinuous).intervalIntegrable 0 T
  have frequencyIntegral : IntervalIntegrable
      (fun t=>laplaceWeight lambda t*fullFrequency spatial lambda (fun i=>(J t i).value) row) volume 0 T :=
    ((weight_continuous lambda).mul frequencyContinuous).intervalIntegrable 0 T
  rw [intervalIntegral.integral_sub timeIntegral frequencyIntegral,
    jet_frequency_integral J continuousJ,fullFrequency_original] at boundary
  linear_combination -boundary

def dressedNoetherTimeSource (event : DressedEvent) (transfer : PhysicalMomentum)
    (signal : ℝ→SourceJet Field289) (t : ℝ) (row : Fin 289) : ℂ :=
  jetTimeSource (fun s i=>dressedNoetherJet event transfer signal s i) (physicalSpatial transfer) t row

def dressedNoetherBoundary (event : DressedEvent) (transfer : PhysicalMomentum)
    (signal : ℝ→SourceJet Field289) (lambda : ℂ) (t : ℝ) (row : Fin 289) : ℂ :=
  jetBoundary (fun s i=>dressedNoetherJet event transfer signal s i) (physicalSpatial transfer) lambda t row

/-- Original F(-P)^T transports this actual quantum current and keeps both temporal co-sources. -/
theorem dressed_noether_readback (event : DressedEvent) (transfer : PhysicalMomentum)
    (signal : ℝ→SourceJet Field289) (continuousSignal : ContinuousJets signal)
    (paid : ∀t,HasSourceJets signal t) (lambda : ℂ) (T : ℝ) (row : Fin 289) :
    (originalReadback (fullMomentum (physicalSpatial transfer) lambda)*ᵥ
      dressedNoetherForcing event transfer signal lambda T) row=
      (∫t in (0:ℝ)..T,laplaceWeight lambda t*dressedNoetherTimeSource event transfer signal t row)-
        (dressedNoetherBoundary event transfer signal lambda T row-
          dressedNoetherBoundary event transfer signal lambda 0 row) := by
  exact jet_forcing_readback (fun t i=>dressedNoetherJet event transfer signal t i)
    (dressed_noether_jet_continuous event transfer signal continuousSignal)
    (fun t i=>dressed_noether_jet_generated event transfer signal continuousSignal.1 t (paid t) i)
    _ lambda T row

/-- Algebraic contact and active inverse consume exactly the same boundary-complete quantum forcing. -/
theorem dressed_noether_field_cosources (event : DressedEvent) (transfer : PhysicalMomentum)
    (signal : ℝ→SourceJet Field289) (continuousSignal : ContinuousJets signal)
    (paid : ∀t,HasSourceJets signal t) (lambda : physicalSpectralDomain transfer) (T : ℝ) :
    dressedNoetherField event transfer signal lambda T=
      originalChange (fullMomentum (physicalSpatial transfer) lambda.val)*ᵥ
        ((contactInverse (fullMomentum (physicalSpatial transfer) lambda.val)+activeProjection*
          (extendedKernel (fullMomentum (physicalSpatial transfer) lambda.val))⁻¹)*ᵥ
          (fun row=>(∫t in (0:ℝ)..T,laplaceWeight lambda.val t*
            dressedNoetherTimeSource event transfer signal t row)-
            (dressedNoetherBoundary event transfer signal lambda.val T row-
              dressedNoetherBoundary event transfer signal lambda.val 0 row))) := by
  have read:=funext (dressed_noether_readback event transfer signal continuousSignal paid lambda.val T)
  unfold dressedNoetherField PreparationVacuumOriginalGreenFeedback.sourceField sourceGreen
  rw [←Matrix.mulVec_mulVec,←Matrix.mulVec_mulVec,read]

end LowEnergy.GaussComposite.ActualDressedNoether
