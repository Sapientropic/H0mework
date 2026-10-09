import H0mework.Versions.Rc015842c.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationNoetherSourceWardChannels

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
noncomputable section
namespace LowEnergy.PreparationVacuumNoetherOrdinaryWard
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open GaussCoreHilbert CanonicalGradedSpatialSource PreparationVacuumMixedFieldReturn
open PreparationVacuumOriginalDensity PreparationVacuumNoetherChart PreparationVacuumPhysicalFeedback
open PreparationVacuumOrderedRealSignal PreparationVacuumOriginalGreenFeedback
open PreparationVacuumGaugeSourceInjection
open Filter Set MeasureTheory
open scoped Topology ContDiff BigOperators Matrix InnerProductSpace Interval
local instance : DecidableEq PhysicalMomentum:=Classical.decEq _
attribute [local irreducible] originalReadback originalChange originalRowLift originalJacobi
  sourceCompatibility sourceGreen PreparationVacuumOriginalGreenFeedback.sourceField

/-- The original action pairs a field wave k with its density coefficient -k. -/
def variationMode (wave : PhysicalMomentum) (coefficients : MomentumCoefficients) : MomentumCoefficients:=
  Finsupp.mapDomain (fun p=>p+wave) coefficients

theorem variationMode_zero (wave : PhysicalMomentum) (coefficients : MomentumCoefficients) :
    variationMode wave coefficients 0=coefficients (-wave) :=by
  have shift : Function.Injective (fun p : PhysicalMomentum=>p+wave):=fun _ _ h=>add_right_cancel h
  have source:=Finsupp.mapDomain_apply shift coefficients (-wave)
  simpa only [variationMode,neg_add_cancel] using source

theorem variationPhase_original (wave : PhysicalMomentum) (x : PhysicalPosition) :
    phase (-wave) x*phase wave x=1 :=by
  rw [←phase_add,neg_add_cancel]
  simp [phase]

def modeJet (q : PhysicalResponsePoint) (force : Field289) (response : Bool) (wave : PhysicalMomentum)
    (t : ℝ) (i : Fin 289) : SourceJet ℂ:=realEulerTimeJet q force response t (-wave) i

def modeForcing (q : PhysicalResponsePoint) (force : Field289) (response : Bool) (wave : PhysicalMomentum)
    (lambda : ℂ) (T : ℝ) : Fin 289→ℂ:=
  fun i=>∫t in (0:ℝ)..T,laplaceWeight lambda t*(modeJet q force response wave t i).value

def modeTimeSource (q : PhysicalResponsePoint) (force : Field289) (response : Bool) (wave : PhysicalMomentum)
    (spatial : Fin 3→ℂ) (t : ℝ) (row : Fin 289) : ℂ:=
  (nativeReadbackTerms.attach.map (fun a=>if row=a.val.row then termSpatial spatial a.val*
    jetEntry (modeJet q force response wave t a.val.column) (nativeTimeOrder a) else 0)).sum

def modeBoundary (q : PhysicalResponsePoint) (force : Field289) (response : Bool) (wave : PhysicalMomentum)
    (spatial : Fin 3→ℂ) (lambda : ℂ) (t : ℝ) (row : Fin 289) : ℂ:=
  (nativeReadbackTerms.attach.map (fun a=>if row=a.val.row then termSpatial spatial a.val*
    (laplaceWeight lambda t*initialCoSource lambda (modeJet q force response wave t a.val.column)
      (nativeTimeOrder a)) else 0)).sum

def modeDifference (q : PhysicalResponsePoint) (force : Field289) (response : Bool) (wave : PhysicalMomentum)
    (spatial : Fin 3→ℂ) (lambda : ℂ) (t : ℝ) (row : Fin 289) : ℂ:=
  (nativeReadbackTerms.attach.map (fun a=>if row=a.val.row then termSpatial spatial a.val*
    (laplaceWeight lambda t*(jetEntry (modeJet q force response wave t a.val.column) (nativeTimeOrder a)-
      lambda^(nativeTimeOrder a).val*(modeJet q force response wave t a.val.column).value)) else 0)).sum

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

theorem modeBoundary_generated (q : PhysicalResponsePoint) (force : Field289) (response : Bool) (wave : PhysicalMomentum)
    (spatial : Fin 3→ℂ) (lambda : ℂ) (t : ℝ) (row : Fin 289) :
    HasDerivAt (fun r=>modeBoundary q force response wave spatial lambda r row)
      (modeDifference q force response wave spatial lambda t row) t :=by
  unfold modeBoundary modeDifference
  convert! derivativeListSum nativeReadbackTerms.attach
    (fun a r=>if row=a.val.row then termSpatial spatial a.val*
      (laplaceWeight lambda r*initialCoSource lambda (modeJet q force response wave r a.val.column) (nativeTimeOrder a)) else 0)
    (fun a r=>if row=a.val.row then termSpatial spatial a.val*
      (laplaceWeight lambda r*(jetEntry (modeJet q force response wave r a.val.column) (nativeTimeOrder a)-
        lambda^(nativeTimeOrder a).val*(modeJet q force response wave r a.val.column).value)) else 0) t (by
    intro a _
    by_cases h : row=a.val.row
    · simp only [if_pos h]
      exact (weightedBoundaryDerivative _ lambda t (realEulerTimeJets_generated _ _ _ _ _ _) _).const_mul _
    · simp only [if_neg h]
      exact hasDerivAt_const t 0) using 1

theorem modeDifference_continuous (q : PhysicalResponsePoint) (force : Field289) (response : Bool) (wave : PhysicalMomentum)
    (spatial : Fin 3→ℂ) (lambda : ℂ) (row : Fin 289) :
    Continuous (fun r=>modeDifference q force response wave spatial lambda r row) :=by
  unfold modeDifference
  apply continuousListSum
  intro a _
  by_cases same : row=a.val.row
  · simp only [if_pos same]
    have hj:=realEulerTimeJets_continuous q force response (-wave) a.val.column
    have entry : Continuous (fun r=>jetEntry (modeJet q force response wave r a.val.column) (nativeTimeOrder a)) :=by
      generalize nativeTimeOrder a=n
      fin_cases n
      · exact hj.1
      · exact hj.2.1
      · exact hj.2.2
    exact ((continuous_iff_continuousAt.mpr (fun r=>(weight_derivative lambda r).continuousAt)).mul
      (entry.sub (hj.1.const_mul _))).const_mul _
  · simp only [if_neg same]
    exact continuous_const

private theorem sumWeightedDifference {ι : Type*} (ts : List ι) (left right : ι→ℂ) (weight : ℂ) :
    (ts.map (fun a=>weight*(left a-right a))).sum=
      weight*((ts.map left).sum-(ts.map right).sum) :=by
  induction ts with
  | nil=>simp
  | cons a rest ih=>simp only [List.map_cons,List.sum_cons,ih];ring

theorem modeDifference_source (q : PhysicalResponsePoint) (force : Field289) (response : Bool) (wave : PhysicalMomentum)
    (spatial : Fin 3→ℂ) (lambda : ℂ) (t : ℝ) (row : Fin 289) :
    modeDifference q force response wave spatial lambda t row=laplaceWeight lambda t*
      (modeTimeSource q force response wave spatial t row-
        fullFrequency spatial lambda (fun i=>(modeJet q force response wave t i).value) row) :=by
  unfold modeDifference modeTimeSource fullFrequency
  rw [←sumWeightedDifference]
  congr 1
  apply List.map_congr_left
  intro a _
  by_cases same : row=a.val.row
  · simp only [if_pos same]
    ring
  · simp only [if_neg same]
    ring

theorem modeWindow_boundary (q : PhysicalResponsePoint) (force : Field289) (response : Bool) (wave : PhysicalMomentum)
    (spatial : Fin 3→ℂ) (lambda : ℂ) (T : ℝ) (row : Fin 289) :
    (∫t in (0:ℝ)..T,modeDifference q force response wave spatial lambda t row)=
      modeBoundary q force response wave spatial lambda T row-modeBoundary q force response wave spatial lambda 0 row :=
  intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun r _=>modeBoundary_generated q force response wave spatial lambda r row)
    ((modeDifference_continuous q force response wave spatial lambda row).intervalIntegrable _ _)

theorem modeFrequency_integral (q : PhysicalResponsePoint) (force : Field289) (response : Bool) (wave : PhysicalMomentum)
    (spatial : Fin 3→ℂ) (lambda : ℂ) (T : ℝ) (row : Fin 289) :
    (∫t in (0:ℝ)..T,laplaceWeight lambda t*
      fullFrequency spatial lambda (fun i=>(modeJet q force response wave t i).value) row)=
      fullFrequency spatial lambda (modeForcing q force response wave lambda T) row :=by
  simp_rw [fullFrequency_original]
  symm
  have hw : Continuous (laplaceWeight lambda):=by unfold laplaceWeight;fun_prop
  change (∑j,originalReadback (fullMomentum spatial lambda) row j*
    modeForcing q force response wave lambda T j)=_
  simp_rw [modeForcing,←intervalIntegral.integral_const_mul]
  have hs:=intervalIntegral.integral_finsetSum (s:=Finset.univ) (μ:=volume)
    (f:=fun (j : Fin 289) r=>originalReadback (fullMomentum spatial lambda) row j*
      (laplaceWeight lambda r*(modeJet q force response wave r j).value))
    (fun j _=>((hw.mul (realEulerTimeJets_continuous q force response (-wave) j).1).const_mul
      (originalReadback (fullMomentum spatial lambda) row j)).intervalIntegrable 0 T)
  refine hs.symm.trans ?_
  apply intervalIntegral.integral_congr
  intro r _
  simp only [Matrix.mulVec,dotProduct,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem modeTimeSource_continuous (q : PhysicalResponsePoint) (force : Field289) (response : Bool) (wave : PhysicalMomentum)
    (spatial : Fin 3→ℂ) (row : Fin 289) : Continuous (fun r=>modeTimeSource q force response wave spatial r row) :=by
  unfold modeTimeSource
  apply continuousListSum
  intro a _
  by_cases same : row=a.val.row
  · simp only [if_pos same]
    have hj:=realEulerTimeJets_continuous q force response (-wave) a.val.column
    generalize nativeTimeOrder a=n
    fin_cases n
    · exact hj.1.const_mul _
    · exact hj.2.1.const_mul _
    · exact hj.2.2.const_mul _
  · simp only [if_neg same]
    exact continuous_const

theorem modeForcing_readback (q : PhysicalResponsePoint) (force : Field289) (response : Bool) (wave : PhysicalMomentum)
    (spatial : Fin 3→ℂ) (lambda : ℂ) (T : ℝ) (row : Fin 289) :
    (originalReadback (fullMomentum spatial lambda)*ᵥmodeForcing q force response wave lambda T) row=
      (∫t in (0:ℝ)..T,laplaceWeight lambda t*modeTimeSource q force response wave spatial t row)-
        (modeBoundary q force response wave spatial lambda T row-modeBoundary q force response wave spatial lambda 0 row) :=by
  have hw : Continuous (laplaceWeight lambda):=by unfold laplaceWeight;fun_prop
  have nativeIntegral : IntervalIntegrable (fun t=>laplaceWeight lambda t*
      modeTimeSource q force response wave spatial t row) volume 0 T:=by
    exact ((hw.mul (modeTimeSource_continuous q force response wave spatial row)).intervalIntegrable (μ:=volume) 0 T).congr_ae
      (Filter.Eventually.of_forall (fun t=>by rfl))
  have frequencyIntegral : IntervalIntegrable (fun t=>laplaceWeight lambda t*
      fullFrequency spatial lambda (fun i=>(modeJet q force response wave t i).value) row) volume 0 T:=by
    simp_rw [fullFrequency_original]
    have cont : Continuous (fun t=>fullFrequency spatial lambda (fun i=>(modeJet q force response wave t i).value) row):=by
      simp_rw [fullFrequency_original,Matrix.mulVec,dotProduct]
      exact continuous_finsetSum _ (fun j _=>(realEulerTimeJets_continuous q force response (-wave) j).1.const_mul _)
    exact ((hw.mul cont).intervalIntegrable (μ:=volume) 0 T).congr_ae
      (Filter.Eventually.of_forall (fun t=>by simp only [Pi.mul_apply,fullFrequency_original]))
  have boundary:=modeWindow_boundary q force response wave spatial lambda T row
  simp_rw [modeDifference_source] at boundary
  simp_rw [mul_sub] at boundary
  rw [intervalIntegral.integral_sub nativeIntegral frequencyIntegral] at boundary
  rw [modeFrequency_integral,fullFrequency_original] at boundary
  exact eq_sub_iff_add_eq.mpr (by linear_combination -boundary)

def compatibilitySlot (row : Fin 9) : Fin 289:=⟨112+row.val,by omega⟩

private theorem nativeNullTimeOrder :
    nativeReadbackTerms.all (fun a=>decide (112≤a.row.val ∧ a.row.val<121→a.powers.temporal<2))=true :=by
  decide +kernel

private theorem nullTimeOrder (a : {a // a∈nativeReadbackTerms}) (row : Fin 9)
    (same : compatibilitySlot row=a.val.row) : (nativeTimeOrder a).val=0 ∨ (nativeTimeOrder a).val=1 :=by
  have source : (112≤a.val.row.val ∧ a.val.row.val<121)→a.val.powers.temporal<2:=
    of_decide_eq_true (List.all_eq_true.mp nativeNullTimeOrder a.val a.property)
  have inside : 112≤a.val.row.val ∧ a.val.row.val<121 :=by
    rw [←same]
    change 112≤112+row.val ∧ 112+row.val<121
    omega
  have bound:=source inside
  change a.val.powers.temporal=0 ∨ a.val.powers.temporal=1
  omega

/-- The actual ordinary constraint coefficients are read from the original null rows. -/
def compatibilityC0 (spatial : Fin 3→ℂ) (current : Fin 289→ℂ) (row : Fin 9) : ℂ:=
  (nativeReadbackTerms.attach.map (fun a=>if compatibilitySlot row=a.val.row then
    if (nativeTimeOrder a).val=0 then termSpatial spatial a.val*current a.val.column else 0 else 0)).sum

def compatibilityCtime (spatial : Fin 3→ℂ) (current : Fin 289→ℂ) (row : Fin 9) : ℂ:=
  (nativeReadbackTerms.attach.map (fun a=>if compatibilitySlot row=a.val.row then
    if (nativeTimeOrder a).val=1 then termSpatial spatial a.val*current a.val.column else 0 else 0)).sum

private theorem listSumAdd {ι : Type*} (ts : List ι) (f g : ι→ℂ) :
    (ts.map (fun a=>f a+g a)).sum=(ts.map f).sum+(ts.map g).sum :=by
  induction ts with
  | nil=>simp
  | cons a rest ih=>simp only [List.map_cons,List.sum_cons,ih];abel

private theorem listSumMul {ι : Type*} (ts : List ι) (f : ι→ℂ) (c : ℂ) :
    (ts.map (fun a=>c*f a)).sum=c*(ts.map f).sum :=by
  induction ts with
  | nil=>simp
  | cons a rest ih=>simp only [List.map_cons,List.sum_cons,ih,mul_add]

theorem modeCompatibility_time (q : PhysicalResponsePoint) (force : Field289) (response : Bool) (wave : PhysicalMomentum)
    (spatial : Fin 3→ℂ) (t : ℝ) (row : Fin 9) :
    modeTimeSource q force response wave spatial t (compatibilitySlot row)=
      compatibilityC0 spatial (fun i=>(modeJet q force response wave t i).value) row+
        compatibilityCtime spatial (fun i=>(modeJet q force response wave t i).first) row :=by
  unfold modeTimeSource compatibilityC0 compatibilityCtime
  rw [←listSumAdd]
  congr 1
  apply List.map_congr_left
  intro a _
  by_cases same : compatibilitySlot row=a.val.row
  · simp only [if_pos same]
    rcases nullTimeOrder a row same with zero|one
    · have index : nativeTimeOrder a=0:=Fin.ext zero
      simp [index,jetEntry]
    · have index : nativeTimeOrder a=1:=Fin.ext one
      simp [index,jetEntry]
  · simp only [if_neg same,add_zero]

theorem compatibilityFrequency_original (spatial : Fin 3→ℂ) (lambda : ℂ) (current : Fin 289→ℂ) (row : Fin 9) :
    (originalReadback (fullMomentum spatial lambda)*ᵥcurrent) (compatibilitySlot row)=
      compatibilityC0 spatial current row+lambda*compatibilityCtime spatial current row :=by
  rw [←fullFrequency_original]
  unfold fullFrequency compatibilityC0 compatibilityCtime
  rw [←listSumMul,←listSumAdd]
  congr 1
  apply List.map_congr_left
  intro a _
  by_cases same : compatibilitySlot row=a.val.row
  · simp only [if_pos same]
    rcases nullTimeOrder a row same with zero|one
    · simp only [zero,if_pos rfl,zero_ne_one,if_false,if_true,pow_zero,mul_one,mul_zero,add_zero]
    · simp only [one,one_ne_zero,if_false,if_pos rfl,if_true,pow_one,zero_add]
      ring
  · simp only [if_neg same,mul_zero,add_zero]

theorem modeBoundary_initial_compatibility (q : PhysicalResponsePoint) (force : Field289) (response : Bool) (wave : PhysicalMomentum)
    (spatial : Fin 3→ℂ) (lambda : ℂ) (row : Fin 9) :
    modeBoundary q force response wave spatial lambda 0 (compatibilitySlot row)=
      compatibilityCtime spatial (fun i=>(modeJet q force response wave 0 i).value) row :=by
  unfold modeBoundary compatibilityCtime
  congr 1
  apply List.map_congr_left
  intro a _
  by_cases same : compatibilitySlot row=a.val.row
  · simp only [if_pos same]
    rcases nullTimeOrder a row same with zero|one
    · have index : nativeTimeOrder a=0:=Fin.ext zero
      simp [index,initialCoSource]
    · have index : nativeTimeOrder a=1:=Fin.ext one
      simp [index,initialCoSource,laplaceWeight]
  · simp only [if_neg same]

/-- The actual C_time initial co-source is retained; no compatibility vanishing is assumed. -/
theorem modeCompatibility_window (q : PhysicalResponsePoint) (force : Field289) (response : Bool) (wave : PhysicalMomentum)
    (spatial : Fin 3→ℂ) (lambda : ℂ) (T : ℝ) (row : Fin 9) :
    sourceCompatibility (fullMomentum spatial lambda) (modeForcing q force response wave lambda T) (compatibilitySlot row)=
      (∫t in (0:ℝ)..T,laplaceWeight lambda t*
        (compatibilityC0 spatial (fun i=>(modeJet q force response wave t i).value) row+
          compatibilityCtime spatial (fun i=>(modeJet q force response wave t i).first) row))-
        (modeBoundary q force response wave spatial lambda T (compatibilitySlot row)-
          compatibilityCtime spatial (fun i=>(modeJet q force response wave 0 i).value) row) :=by
  have flag : nullFlag (compatibilitySlot row)=true :=by
    simp only [nullFlag,compatibilitySlot,decide_eq_true_eq]
    omega
  unfold sourceCompatibility nullProjection projectionMatrix
  rw [Matrix.mulVec_diagonal]
  simp only [flag,if_true,one_mul]
  rw [modeForcing_readback,modeBoundary_initial_compatibility]
  simp only [modeCompatibility_time]

/-- This is the unchanged original full289 Green with all nine residual directions. -/
def modeField (q : PhysicalResponsePoint) (force : Field289) (response : Bool) (wave : PhysicalMomentum)
    (lambda : physicalSpectralDomain wave) (T : ℝ) : Fin 289→ℂ:=
  PreparationVacuumOriginalGreenFeedback.sourceField ⟨fullMomentum (PreparationVacuumPhysicalFeedback.physicalSpatial wave) lambda.val,lambda.property⟩
    (modeForcing q force response wave lambda.val T)

theorem modeField_equation (q : PhysicalResponsePoint) (force : Field289) (response : Bool) (wave : PhysicalMomentum)
    (lambda : physicalSpectralDomain wave) (T : ℝ) :
    originalJacobi (fullMomentum (PreparationVacuumPhysicalFeedback.physicalSpatial wave) lambda.val)*ᵥmodeField q force response wave lambda T=
      modeForcing q force response wave lambda.val T-originalRowLift
        (fullMomentum (PreparationVacuumPhysicalFeedback.physicalSpatial wave) lambda.val)*ᵥsourceCompatibility
          (fullMomentum (PreparationVacuumPhysicalFeedback.physicalSpatial wave) lambda.val)
            (modeForcing q force response wave lambda.val T) :=
  original_forced_field ⟨fullMomentum (PreparationVacuumPhysicalFeedback.physicalSpatial wave) lambda.val,lambda.property⟩
    (modeForcing q force response wave lambda.val T)

theorem modeField_cosources (q : PhysicalResponsePoint) (force : Field289) (response : Bool) (wave : PhysicalMomentum)
    (lambda : physicalSpectralDomain wave) (T : ℝ) :
    modeField q force response wave lambda T=
      originalChange (fullMomentum (PreparationVacuumPhysicalFeedback.physicalSpatial wave) lambda.val)*ᵥ
        ((contactInverse (fullMomentum (PreparationVacuumPhysicalFeedback.physicalSpatial wave) lambda.val)+activeProjection*
          (extendedKernel (fullMomentum (PreparationVacuumPhysicalFeedback.physicalSpatial wave) lambda.val))⁻¹)*ᵥ
            (fun row=>(∫t in (0:ℝ)..T,laplaceWeight lambda.val t*
              modeTimeSource q force response wave (PreparationVacuumPhysicalFeedback.physicalSpatial wave) t row)-
                (modeBoundary q force response wave (PreparationVacuumPhysicalFeedback.physicalSpatial wave) lambda.val T row-
                  modeBoundary q force response wave (PreparationVacuumPhysicalFeedback.physicalSpatial wave) lambda.val 0 row))) :=by
  have read : originalReadback (fullMomentum (PreparationVacuumPhysicalFeedback.physicalSpatial wave) lambda.val)*ᵥ
      modeForcing q force response wave lambda.val T=_:=
    funext (modeForcing_readback q force response wave (PreparationVacuumPhysicalFeedback.physicalSpatial wave) lambda.val T)
  unfold modeField PreparationVacuumOriginalGreenFeedback.sourceField sourceGreen
  rw [←Matrix.mulVec_mulVec,←Matrix.mulVec_mulVec,read]

end LowEnergy.PreparationVacuumNoetherOrdinaryWard
