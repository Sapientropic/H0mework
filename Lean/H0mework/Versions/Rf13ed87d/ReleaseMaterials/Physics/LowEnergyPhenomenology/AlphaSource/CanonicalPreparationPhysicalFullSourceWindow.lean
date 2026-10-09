import H0mework.Versions.Rf13ed87d.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationPhysicalRawTimeJets
import H0mework.Versions.Rf13ed87d.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationOriginalPreparedGreen

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
noncomputable section
namespace LowEnergy.PreparationVacuumPhysicalFeedback
open PreparationVacuumGaugeSourceInjection PreparationVacuumOriginalGreenFeedback
open GaussCoreHilbert CanonicalGradedSpatialSource PreparationVacuumJointFieldResponse PreparationVacuumMixedFieldReturn PreparationVacuumActionFieldLift
open PreparationVacuumRawJointFeedback PreparationVacuumFieldPerturbation
open Filter MeasureTheory
open scoped Topology Interval BigOperators Matrix InnerProductSpace
local instance : NormedAlgebra ℝ Op:=NormedAlgebra.restrictScalars ℝ ℂ _
local instance : NormedAlgebra ℚ Op:=NormedAlgebra.restrictScalars ℚ ℂ _

def ContinuousJets {E : Type*} [TopologicalSpace E] (j : ℝ→SourceJet E) : Prop :=
  Continuous (fun r=>(j r).value) ∧ Continuous (fun r=>(j r).first) ∧ Continuous (fun r=>(j r).second)

theorem constantJets_continuous (A : Op) : ContinuousJets (fun _=>jetConst A) :=
  ⟨continuous_const,continuous_const,continuous_const⟩

theorem productJets_continuous (a b : ℝ→SourceJet Op)
    (ha : ContinuousJets a) (hb : ContinuousJets b) :
    ContinuousJets (fun r=>jetMul (a r) (b r)) :=
  ⟨ha.1.mul hb.1,(ha.2.1.mul hb.1).add (ha.1.mul hb.2.1),
    ((ha.2.2.mul hb.1).add (ha.2.1.mul hb.2.1)).add
      ((ha.2.1.mul hb.2.1).add (ha.1.mul hb.2.2))⟩

theorem sumJets_continuous (a b : ℝ→SourceJet Op)
    (ha : ContinuousJets a) (hb : ContinuousJets b) :
    ContinuousJets (fun r=>addJet (a r) (b r)) :=
  ⟨ha.1.add hb.1,ha.2.1.add hb.2.1,ha.2.2.add hb.2.2⟩

theorem timeJets_continuous (C : Op) (rate shift : ℝ) : ContinuousJets (timeJet C rate shift) :=by
  have ht : Continuous (fun r : ℝ=>SourceFiniteUnitary.time C (rate*r+shift)):=
    (time_continuous C).comp ((continuous_const.mul continuous_id).add continuous_const)
  exact ⟨ht,(ht.mul continuous_const).const_smul rate,
    (((ht.mul continuous_const).const_smul rate).mul continuous_const).const_smul rate⟩

theorem variationJets_continuous (C B : Op) (rate shift : ℝ) : ContinuousJets (variationJet C B rate shift) :=by
  have hv : Continuous (CanonicalGradedVariation.variation C B):=
    continuous_iff_continuousAt.mpr (fun r=>(variation_ode C B r).continuousAt)
  have ht:=(timeJets_continuous C rate shift)
  have ha : Continuous (fun r : ℝ=>CanonicalGradedVariation.variation C B (rate*r+shift)):=
    hv.comp ((continuous_const.mul continuous_id).add continuous_const)
  have first : Continuous (fun r : ℝ=>(variationJet C B rate shift r).first):=
    ((ha.mul continuous_const).add (ht.1.mul continuous_const)).const_smul rate
  exact ⟨ha,first,((first.mul continuous_const).add (ht.2.1.mul continuous_const)).const_smul rate⟩

theorem physicalTimeJets_continuous (p : PhysicalMomentum) (F : Index) (h : Field289) (rate shift : ℝ) :
    ContinuousJets (physicalTimeJet p F h rate shift) :=timeJets_continuous _ _ _

theorem physicalSlopeJets_continuous (force : Field289) (p : PhysicalMomentum) (F : Index) (rate shift : ℝ) :
    ContinuousJets (physicalSlopeJet force p F rate shift) :=variationJets_continuous _ _ _ _

theorem rawKernelJets_continuous (reader : Field289) (p k : PhysicalMomentum) (F : Index)
    (z w : ℂ) (h : Field289) : ContinuousJets (rawKernelJet reader p k F z w h) :=by
  unfold rawKernelJet
  repeat first
    | apply productJets_continuous
    | exact physicalTimeJets_continuous _ _ _ _ _
    | exact constantJets_continuous _

theorem slopeKernelJets_continuous (reader force : Field289) (p k : PhysicalMomentum) (F : Index)
    (z w : ℂ) : ContinuousJets (slopeKernelJet reader force p k F z w) :=by
  unfold slopeKernelJet
  repeat first
    | apply sumJets_continuous
    | apply productJets_continuous
    | exact physicalTimeJets_continuous _ _ _ _ _
    | exact physicalSlopeJets_continuous _ _ _ _ _
    | exact constantJets_continuous _

def sourceRead (q : PhysicalResponsePoint) : Op→L[ℂ] ℂ :=
  (innerSL ℂ (responseLeft q)).comp (ContinuousLinearMap.apply ℂ H (responseRight q))

theorem pairJets_continuous (q : PhysicalResponsePoint) (j : ℝ→SourceJet Op) (hj : ContinuousJets j) :
    ContinuousJets (fun r=>pairJet (responseLeft q) (responseRight q) (j r)) :=
  ⟨(sourceRead q).continuous.comp hj.1,(sourceRead q).continuous.comp hj.2.1,
    (sourceRead q).continuous.comp hj.2.2⟩

theorem sourceJets_continuous (q : PhysicalResponsePoint) (h : Field289) (i : Fin 289) :
    ContinuousJets (fun r=>sourceJet q h r i) :=by
  have generated:=pairJets_continuous q _
    (rawKernelJets_continuous (fieldUnit i) q.p q.k q.F q.z q.w h)
  exact ⟨generated.1.neg,generated.2.1.neg,generated.2.2.neg⟩

theorem sourceSlopeJets_continuous (q : PhysicalResponsePoint) (force : Field289) (i : Fin 289) :
    ContinuousJets (fun r=>sourceSlopeJet q force r i) :=by
  have h:=pairJets_continuous q _
    (slopeKernelJets_continuous (fieldUnit i) force q.p q.k q.F q.z q.w)
  exact ⟨h.1.neg,h.2.1.neg,h.2.2.neg⟩

/-- Both actual full289 source and its five-term response use the same time jet mouth. -/
def fullSourceJet (q : PhysicalResponsePoint) (force : Field289) (response : Bool)
    (r : ℝ) (i : Fin 289) : SourceJet ℂ:=
  if response then sourceSlopeJet q force r i else sourceJet q 0 r i

theorem fullSourceJets_generated (q : PhysicalResponsePoint) (force : Field289) (response : Bool)
    (r : ℝ) (i : Fin 289) : HasSourceJets (fun t=>fullSourceJet q force response t i) r :=by
  cases response
  · exact sourceJet_generated _ _ _ _
  · exact sourceSlopeJet_generated _ _ _ _

theorem fullSourceJets_continuous (q : PhysicalResponsePoint) (force : Field289) (response : Bool)
    (i : Fin 289) : ContinuousJets (fun r=>fullSourceJet q force response r i) :=by
  cases response
  · exact sourceJets_continuous _ _ _
  · exact sourceSlopeJets_continuous _ _ _

def fullMomentum (spatial : Fin 3→ℂ) (lambda : ℂ) : Fin 4→ℂ:=Fin.cases lambda spatial

def termSpatial (spatial : Fin 3→ℂ) (a : SourceTerm) : ℂ:=
  coefficientValue a.coefficient*(spatial 0)^a.powers.first*
    (spatial 1)^a.powers.second*(spatial 2)^a.powers.third

def fullForcing (q : PhysicalResponsePoint) (force : Field289) (response : Bool)
    (lambda : ℂ) (T : ℝ) : Fin 289→ℂ:=
  fun i=>∫r in (0:ℝ)..T,laplaceWeight lambda r*(fullSourceJet q force response r i).value

def fullTimeSource (q : PhysicalResponsePoint) (force : Field289) (response : Bool)
    (spatial : Fin 3→ℂ) (r : ℝ) (row : Fin 289) : ℂ:=
  (nativeReadbackTerms.attach.map (fun a=>if row=a.val.row then termSpatial spatial a.val*
    jetEntry (fullSourceJet q force response r a.val.column) (nativeTimeOrder a) else 0)).sum

def fullBoundary (q : PhysicalResponsePoint) (force : Field289) (response : Bool)
    (spatial : Fin 3→ℂ) (lambda : ℂ) (r : ℝ) (row : Fin 289) : ℂ:=
  (nativeReadbackTerms.attach.map (fun a=>if row=a.val.row then termSpatial spatial a.val*
    (laplaceWeight lambda r*initialCoSource lambda (fullSourceJet q force response r a.val.column)
      (nativeTimeOrder a)) else 0)).sum

def fullDifference (q : PhysicalResponsePoint) (force : Field289) (response : Bool)
    (spatial : Fin 3→ℂ) (lambda : ℂ) (r : ℝ) (row : Fin 289) : ℂ:=
  (nativeReadbackTerms.attach.map (fun a=>if row=a.val.row then termSpatial spatial a.val*
    (laplaceWeight lambda r*(jetEntry (fullSourceJet q force response r a.val.column) (nativeTimeOrder a)-
      lambda^(nativeTimeOrder a).val*(fullSourceJet q force response r a.val.column).value)) else 0)).sum

private theorem derivativeListSum {ι : Type*} (entries : List ι) (f df : ι→ℝ→ℂ) (r : ℝ)
    (h : ∀a∈entries,HasDerivAt (f a) (df a r) r) :
    HasDerivAt (fun t=>(entries.map (fun a=>f a t)).sum) ((entries.map (fun a=>df a r)).sum) r :=by
  induction entries with
  | nil=>exact hasDerivAt_const r 0
  | cons a rest ih=>
    simpa only [List.map_cons,List.sum_cons] using!
      (h a (by simp)).add (ih (fun b hb=>h b (by simp [hb])))

private theorem continuousListSum {ι : Type*} (entries : List ι) (f : ι→ℝ→ℂ)
    (h : ∀a∈entries,Continuous (f a)) : Continuous (fun r=>(entries.map (fun a=>f a r)).sum) :=by
  induction entries with
  | nil=>exact continuous_const
  | cons a rest ih=>
    simpa only [List.map_cons,List.sum_cons] using!
      (h a (by simp)).add (ih (fun b hb=>h b (by simp [hb])))

private theorem weight_derivative (lambda : ℂ) (t : ℝ) :
    HasDerivAt (laplaceWeight lambda) (-lambda*laplaceWeight lambda t) t :=by
  unfold laplaceWeight
  convert! (((Complex.ofRealCLM.hasFDerivAt).hasDerivAt.const_mul (-lambda)).cexp) using 1
  simp [Complex.ofRealCLM]
  ring

private theorem weightedBoundaryDerivative (j : ℝ→SourceJet ℂ) (lambda : ℂ)
    (t : ℝ) (h : HasSourceJets j t) (n : Fin 3) :
    HasDerivAt (fun s=>laplaceWeight lambda s*initialCoSource lambda (j s) n)
      (laplaceWeight lambda t*(jetEntry (j t) n-lambda^n.val*(j t).value)) t :=by
  fin_cases n
  · simpa [initialCoSource,jetEntry] using hasDerivAt_const t (0:ℂ)
  · have H:=(weight_derivative lambda t).mul h.1
    change HasDerivAt (fun s=>laplaceWeight lambda s*(j s).value)
      (laplaceWeight lambda t*((j t).first-lambda^1*(j t).value)) t
    convert! H using 1
    ring
  · have H:=(weight_derivative lambda t).mul ((h.1.const_mul lambda).add h.2)
    change HasDerivAt (fun s=>laplaceWeight lambda s*(lambda*(j s).value+(j s).first))
      (laplaceWeight lambda t*((j t).second-lambda^2*(j t).value)) t
    convert! H using 1
    change _=(-lambda*laplaceWeight lambda t*(lambda*(j t).value+(j t).first)+
      laplaceWeight lambda t*(lambda*(j t).first+(j t).second))
    ring

theorem fullBoundary_generated (q : PhysicalResponsePoint) (force : Field289) (response : Bool)
    (spatial : Fin 3→ℂ) (lambda : ℂ) (t : ℝ) (row : Fin 289) :
    HasDerivAt (fun r=>fullBoundary q force response spatial lambda r row)
      (fullDifference q force response spatial lambda t row) t :=by
  unfold fullBoundary fullDifference
  convert! derivativeListSum nativeReadbackTerms.attach
    (fun a r=>if row=a.val.row then termSpatial spatial a.val*
      (laplaceWeight lambda r*initialCoSource lambda (fullSourceJet q force response r a.val.column) (nativeTimeOrder a)) else 0)
    (fun a r=>if row=a.val.row then termSpatial spatial a.val*
      (laplaceWeight lambda r*(jetEntry (fullSourceJet q force response r a.val.column) (nativeTimeOrder a)-
        lambda^(nativeTimeOrder a).val*(fullSourceJet q force response r a.val.column).value)) else 0) t (by
    intro a _
    by_cases h : row=a.val.row
    · simp only [if_pos h]
      exact (weightedBoundaryDerivative _ lambda t (fullSourceJets_generated _ _ _ _ _) _).const_mul _
    · simp only [if_neg h]
      exact hasDerivAt_const t 0) using 1

theorem fullDifference_continuous (q : PhysicalResponsePoint) (force : Field289) (response : Bool)
    (spatial : Fin 3→ℂ) (lambda : ℂ) (row : Fin 289) :
    Continuous (fun r=>fullDifference q force response spatial lambda r row) :=by
  unfold fullDifference
  apply continuousListSum
  intro a _
  by_cases same : row=a.val.row
  · simp only [if_pos same]
    have hj:=fullSourceJets_continuous q force response a.val.column
    have entry : Continuous (fun r=>jetEntry (fullSourceJet q force response r a.val.column) (nativeTimeOrder a)) :=by
      generalize nativeTimeOrder a=n
      fin_cases n
      · exact hj.1
      · exact hj.2.1
      · exact hj.2.2
    exact ((continuous_iff_continuousAt.mpr (fun r=>(weight_derivative lambda r).continuousAt)).mul
      (entry.sub (hj.1.const_mul _))).const_mul _
  · simp only [if_neg same]
    exact continuous_const

theorem fullWindow_boundary (q : PhysicalResponsePoint) (force : Field289) (response : Bool)
    (spatial : Fin 3→ℂ) (lambda : ℂ) (T : ℝ) (row : Fin 289) :
    (∫r in (0:ℝ)..T,fullDifference q force response spatial lambda r row)=
      fullBoundary q force response spatial lambda T row-fullBoundary q force response spatial lambda 0 row :=
  intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun r _=>fullBoundary_generated q force response spatial lambda r row)
    ((fullDifference_continuous q force response spatial lambda row).intervalIntegrable _ _)

private theorem termSpatial_value (spatial : Fin 3→ℂ) (lambda : ℂ) (a : SourceTerm) :
    termSpatial spatial a*lambda^a.powers.temporal=
      coefficientValue a.coefficient*a.powers.value (fullMomentum spatial lambda) :=by
  simp only [termSpatial,Powers.value,fullMomentum]
  change _=coefficientValue a.coefficient*(lambda^a.powers.temporal*
    (spatial 0)^a.powers.first*(spatial 1)^a.powers.second*(spatial 2)^a.powers.third)
  ring

private theorem attachedValues {α β : Type*} (ts : List α) (f : α→β) :
    ts.attach.map (fun a=>f a.val)=ts.map f :=by
  have h:=congrArg (List.map f) (List.attach_map_subtype_val ts)
  simpa only [List.map_map] using! h

def fullFrequency (spatial : Fin 3→ℂ) (lambda : ℂ) (current : Fin 289→ℂ) (row : Fin 289) : ℂ:=
  (nativeReadbackTerms.attach.map (fun a=>if row=a.val.row then termSpatial spatial a.val*
    lambda^(nativeTimeOrder a).val*current a.val.column else 0)).sum

theorem fullFrequency_original (spatial : Fin 3→ℂ) (lambda : ℂ) (current : Fin 289→ℂ) (row : Fin 289) :
    fullFrequency spatial lambda current row=(originalReadback (fullMomentum spatial lambda)*ᵥcurrent) row :=by
  let f : SourceTerm→ℂ:=fun a=>if row=a.row then termSpatial spatial a*lambda^a.powers.temporal*current a.column else 0
  let g : SourceTerm→ℂ:=fun a=>if row=a.row then coefficientValue a.coefficient*a.powers.value (fullMomentum spatial lambda)*current a.column else 0
  have step (a : SourceTerm) : f a=g a :=by
    dsimp [f,g]
    by_cases same : row=a.row
    · simp only [if_pos same];rw [termSpatial_value]
    · simp only [if_neg same]
  have maps : nativeReadbackTerms.attach.map (fun a=>f a.val)=nativeReadbackTerms.attach.map (fun a=>g a.val):=
    List.map_congr_left (fun a _=>step a.val)
  have reflected : sourceMatrix nativeReadbackTerms (fullMomentum spatial lambda)=originalReadback (fullMomentum spatial lambda):=
    reflectedTerms_value originalChangeTerms _
  calc
    _=(nativeReadbackTerms.attach.map (fun a=>f a.val)).sum :=rfl
    _=(nativeReadbackTerms.attach.map (fun a=>g a.val)).sum :=congrArg List.sum maps
    _=(nativeReadbackTerms.map g).sum :=congrArg List.sum (attachedValues nativeReadbackTerms g)
    _=(sourceMatrix nativeReadbackTerms (fullMomentum spatial lambda)*ᵥcurrent) row :=
      (sourceMatrix_mulVec nativeReadbackTerms (fullMomentum spatial lambda) current row).symm
    _=_ :=congrArg (fun M : Matrix (Fin 289) (Fin 289) ℂ=>(M*ᵥcurrent) row) reflected

private theorem sumWeightedDifference {ι : Type*} (ts : List ι) (left right : ι→ℂ) (weight : ℂ) :
    (ts.map (fun a=>weight*(left a-right a))).sum=
      weight*((ts.map left).sum-(ts.map right).sum) :=by
  induction ts with
  | nil=>simp
  | cons a rest ih=>simp only [List.map_cons,List.sum_cons,ih];ring

theorem fullDifference_source (q : PhysicalResponsePoint) (force : Field289) (response : Bool)
    (spatial : Fin 3→ℂ) (lambda : ℂ) (r : ℝ) (row : Fin 289) :
    fullDifference q force response spatial lambda r row=laplaceWeight lambda r*
      (fullTimeSource q force response spatial r row-
        fullFrequency spatial lambda (fun i=>(fullSourceJet q force response r i).value) row) :=by
  unfold fullDifference fullTimeSource fullFrequency
  rw [←sumWeightedDifference]
  congr 1
  apply List.map_congr_left
  intro a _
  by_cases same : row=a.val.row
  · simp only [if_pos same]
    ring
  · simp only [if_neg same]
    ring

theorem fullFrequency_integral (q : PhysicalResponsePoint) (force : Field289) (response : Bool)
    (spatial : Fin 3→ℂ) (lambda : ℂ) (T : ℝ) (row : Fin 289) :
    (∫r in (0:ℝ)..T,laplaceWeight lambda r*
      fullFrequency spatial lambda (fun i=>(fullSourceJet q force response r i).value) row)=
      fullFrequency spatial lambda (fullForcing q force response lambda T) row :=by
  simp_rw [fullFrequency_original]
  symm
  have hw : Continuous (laplaceWeight lambda):=by unfold laplaceWeight;fun_prop
  change (∑j,originalReadback (fullMomentum spatial lambda) row j*
    fullForcing q force response lambda T j)=_
  simp_rw [fullForcing,←intervalIntegral.integral_const_mul]
  have hs:=intervalIntegral.integral_finsetSum (s:=Finset.univ) (μ:=volume)
    (f:=fun (j : Fin 289) r=>originalReadback (fullMomentum spatial lambda) row j*
      (laplaceWeight lambda r*(fullSourceJet q force response r j).value))
    (fun j _=>((hw.mul (fullSourceJets_continuous q force response j).1).const_mul
      (originalReadback (fullMomentum spatial lambda) row j)).intervalIntegrable 0 T)
  refine hs.symm.trans ?_
  apply intervalIntegral.integral_congr
  intro r _
  simp only [Matrix.mulVec,dotProduct,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem fullTimeSource_continuous (q : PhysicalResponsePoint) (force : Field289) (response : Bool)
    (spatial : Fin 3→ℂ) (row : Fin 289) : Continuous (fun r=>fullTimeSource q force response spatial r row) :=by
  unfold fullTimeSource
  apply continuousListSum
  intro a _
  by_cases same : row=a.val.row
  · simp only [if_pos same]
    have hj:=fullSourceJets_continuous q force response a.val.column
    generalize nativeTimeOrder a=n
    fin_cases n
    · exact hj.1.const_mul _
    · exact hj.2.1.const_mul _
    · exact hj.2.2.const_mul _
  · simp only [if_neg same]
    exact continuous_const

theorem fullForcing_readback (q : PhysicalResponsePoint) (force : Field289) (response : Bool)
    (spatial : Fin 3→ℂ) (lambda : ℂ) (T : ℝ) (row : Fin 289) :
    (originalReadback (fullMomentum spatial lambda)*ᵥfullForcing q force response lambda T) row=
      (∫r in (0:ℝ)..T,laplaceWeight lambda r*fullTimeSource q force response spatial r row)-
        (fullBoundary q force response spatial lambda T row-fullBoundary q force response spatial lambda 0 row) :=by
  have h:=fullWindow_boundary q force response spatial lambda T row
  simp_rw [fullDifference_source] at h
  have hw : Continuous (laplaceWeight lambda):=
    continuous_iff_continuousAt.mpr (fun r=>(weight_derivative lambda r).continuousAt)
  have hi : IntervalIntegrable (fun r=>laplaceWeight lambda r*fullTimeSource q force response spatial r row) volume 0 T:=
    (hw.mul (fullTimeSource_continuous q force response spatial row)).intervalIntegrable 0 T
  have hread : Continuous (fun r=>fullFrequency spatial lambda
      (fun i=>(fullSourceJet q force response r i).value) row) :=by
    simp_rw [fullFrequency_original]
    change Continuous (fun r=>∑j,originalReadback (fullMomentum spatial lambda) row j*
      (fullSourceJet q force response r j).value)
    apply continuous_finsetSum
    intro j _
    exact (fullSourceJets_continuous q force response j).1.const_mul _
  have hf : IntervalIntegrable (fun r=>laplaceWeight lambda r*fullFrequency spatial lambda
      (fun i=>(fullSourceJet q force response r i).value) row) volume 0 T:=
    (hw.mul hread).intervalIntegrable 0 T
  simp_rw [mul_sub] at h
  rw [intervalIntegral.integral_sub hi hf,fullFrequency_integral,fullFrequency_original] at h
  exact (eq_sub_iff_add_eq.mpr (by linear_combination -h))

end LowEnergy.PreparationVacuumPhysicalFeedback
