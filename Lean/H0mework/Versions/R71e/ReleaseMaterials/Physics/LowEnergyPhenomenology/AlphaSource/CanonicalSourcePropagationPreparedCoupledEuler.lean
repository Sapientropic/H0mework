import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalSourcePropagationOriginalEulerDirections

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 8192
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.SourcePropagationMotherEulerKernel
open SaturationMonoid.PhysicsCore StageNineHolonomicField ProofFreeRicherAnholonomicSource
open SourcePropagationNativeActionHessian SourcePropagationNativeEulerHistory SourcePropagationNoetherTime
open PreparationVacuumMixedFieldReturn PreparationVacuumPhysicalFeedback PreparationVacuumGaugeSourceInjection
open PreparationVacuumActionFieldLift PreparationVacuumFieldConstraintResponse PreparationVacuumOriginalGreenFeedback
open Filter MeasureTheory
open scoped Topology ContDiff BigOperators Matrix
attribute [local irreducible] nativeJetDensity nativeHessian nativeEulerQuadratic nativeJetBasis
  originalJacobi originalRowLift sourceCompatibility originalReadback originalReader36

private theorem smooth_deriv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ→E) (smooth : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (deriv f) :=
  (smooth.fderiv_right (m:=∞) (by simp)).clm_apply contDiff_const

/-- The observation uses the original coordinate-time axis. -/
def nativeTimePoint (t : ℝ) : BasePoint := t • coordinateDirection 0

def nativeTimeHistory (signal : BasePoint→Field289) (t : ℝ) : Field289 := signal (nativeTimePoint t)

theorem nativeTimePoint_smooth : ContDiff ℝ ∞ nativeTimePoint :=
  contDiff_id.smul contDiff_const

theorem nativeTimeHistory_smooth (signal : BasePoint→Field289) (smooth : ContDiff ℝ ∞ signal) :
    ContDiff ℝ ∞ (nativeTimeHistory signal) := smooth.comp nativeTimePoint_smooth

def nativeTimeSignal (signal : BasePoint→Field289) (t : ℝ) : SourceJet Field289 :=
  ⟨nativeTimeHistory signal t,deriv (nativeTimeHistory signal) t,deriv (deriv (nativeTimeHistory signal)) t⟩

theorem nativeTimeSignal_generated (signal : BasePoint→Field289) (smooth : ContDiff ℝ ∞ signal) (t : ℝ) :
    HasSourceJets (nativeTimeSignal signal) t := by
  have history:=nativeTimeHistory_smooth signal smooth
  have first : DifferentiableAt ℝ (nativeTimeHistory signal) t := history.differentiable (by simp) |>.differentiableAt
  have second : DifferentiableAt ℝ (deriv (nativeTimeHistory signal)) t :=
    (smooth_deriv _ history).differentiable (by simp) |>.differentiableAt
  exact ⟨first.hasDerivAt,second.hasDerivAt⟩

theorem nativeTimeSignal_continuous (signal : BasePoint→Field289) (smooth : ContDiff ℝ ∞ signal) :
    ContinuousJets (nativeTimeSignal signal) := by
  have history:=nativeTimeHistory_smooth signal smooth
  exact ⟨history.continuous,(smooth_deriv _ history).continuous,
    (smooth_deriv _ (smooth_deriv _ history)).continuous⟩

def nativeOrdinaryRemainder (signal : BasePoint→Field289) (t : ℝ) (i : Fin 289) : ℝ :=
  nativeEulerQuadratic (signalSecondJet signal (nativeTimePoint t)) i

theorem nativeOrdinaryRemainder_generated (signal : BasePoint→Field289) (smooth : ContDiff ℝ ∞ signal)
    (t : ℝ) (i : Fin 289) :
    HasDerivAt (deriv (fun a : ℝ=>nativeHolonomicEuler (fun position=>a • signal position) (nativeTimePoint t) i))
      (2*nativeOrdinaryRemainder signal t i) 0 :=
  nativeHolonomicEuler_source_quadratic signal (nativeTimePoint t) (smooth.contDiffAt.of_le (by
    change ((2 : ℕ∞) : ℕ∞ω)≤((⊤ : ℕ∞) : ℕ∞ω)
    exact WithTop.coe_le_coe.mpr le_top)) i

private theorem signalFirstJet_smooth (signal : BasePoint→Field289) (smooth : ContDiff ℝ ∞ signal) :
    ContDiff ℝ ∞ (signalFirstJet signal) := by
  have differential:=smooth.fderiv_right (m:=∞) (by simp)
  exact smooth.prodMk (contDiff_pi.2 (fun mu=>differential.clm_apply contDiff_const))

private theorem signalSecondJet_smooth (signal : BasePoint→Field289) (smooth : ContDiff ℝ ∞ signal) :
    ContDiff ℝ ∞ (signalSecondJet signal) := by
  have first:=signalFirstJet_smooth signal smooth
  have differential:=first.fderiv_right (m:=∞) (by simp)
  exact first.prodMk (contDiff_pi.2 (fun mu=>differential.clm_apply contDiff_const))

private theorem nativeEulerQuadratic_smooth (i : Fin 289) : ContDiff ℝ ∞ (fun jet : NativeSecondJet=>nativeEulerQuadratic jet i) := by
  unfold nativeEulerQuadratic
  let A:=fderiv ℝ (fun data : NativeSecondJet=>fderiv ℝ (fun state : NativeSecondJet=>nativeEulerDensityJet state i) data) 0
  have quadratic : ContDiff ℝ ∞ (fun jet : NativeSecondJet=>A jet jet) := A.contDiff.clm_apply contDiff_id
  exact contDiff_const.mul quadratic

theorem nativeOrdinaryRemainder_smooth (signal : BasePoint→Field289) (smooth : ContDiff ℝ ∞ signal) (i : Fin 289) :
    ContDiff ℝ ∞ (fun t=>nativeOrdinaryRemainder signal t i) :=
  (nativeEulerQuadratic_smooth i).comp ((signalSecondJet_smooth signal smooth).comp nativeTimePoint_smooth)

def nativeRemainderJet (signal : BasePoint→Field289) (t : ℝ) (i : Fin 289) : SourceJet ℂ :=
  ⟨Complex.ofReal (nativeOrdinaryRemainder signal t i),
    Complex.ofReal (deriv (fun s : ℝ=>nativeOrdinaryRemainder signal s i) t),
    Complex.ofReal (deriv (deriv (fun s : ℝ=>nativeOrdinaryRemainder signal s i)) t)⟩

theorem nativeRemainderJet_generated (signal : BasePoint→Field289) (smooth : ContDiff ℝ ∞ signal) (t : ℝ) (i : Fin 289) :
    HasSourceJets (fun s=>nativeRemainderJet signal s i) t := by
  have original:=nativeOrdinaryRemainder_smooth signal smooth i
  have first:=original.differentiable (by simp) |>.differentiableAt.hasDerivAt (x:=t)
  have second:=(smooth_deriv _ original).differentiable (by simp) |>.differentiableAt.hasDerivAt (x:=t)
  refine ⟨?_,?_⟩
  · convert! Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt t first using 1
  · convert! Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt t second using 1

theorem nativeRemainderJet_continuous (signal : BasePoint→Field289) (smooth : ContDiff ℝ ∞ signal) (i : Fin 289) :
    ContinuousJets (fun t=>nativeRemainderJet signal t i) := by
  have original:=nativeOrdinaryRemainder_smooth signal smooth i
  refine ⟨?_,?_,?_⟩
  · convert! Complex.ofRealCLM.continuous.comp original.continuous using 1
  · convert! Complex.ofRealCLM.continuous.comp (smooth_deriv _ original).continuous using 1
  · convert! Complex.ofRealCLM.continuous.comp (smooth_deriv _ (smooth_deriv _ original)).continuous using 1

/-- This generated forcing is the given-field ordered-current response minus the complete native ordinary remainder. -/
def preparedOrdinarySource (q : PhysicalResponsePoint) (signal : BasePoint→Field289) (t : ℝ) (i : Fin 289) : ℂ :=
  (noetherHistorySourceJet q (nativeTimeSignal signal) t i).value-(nativeOrdinaryRemainder signal t i : ℂ)

def preparedOrdinarySourceJet (q : PhysicalResponsePoint) (signal : BasePoint→Field289) (t : ℝ) (i : Fin 289) : SourceJet ℂ :=
  ⟨(noetherHistorySourceJet q (nativeTimeSignal signal) t i).value-(nativeRemainderJet signal t i).value,
    (noetherHistorySourceJet q (nativeTimeSignal signal) t i).first-(nativeRemainderJet signal t i).first,
    (noetherHistorySourceJet q (nativeTimeSignal signal) t i).second-(nativeRemainderJet signal t i).second⟩

theorem preparedOrdinarySourceJet_value (q : PhysicalResponsePoint) (signal : BasePoint→Field289) (t : ℝ) (i : Fin 289) :
    (preparedOrdinarySourceJet q signal t i).value=preparedOrdinarySource q signal t i := rfl

theorem preparedOrdinarySourceJet_generated (q : PhysicalResponsePoint) (signal : BasePoint→Field289)
    (smooth : ContDiff ℝ ∞ signal) (t : ℝ) (i : Fin 289) :
    HasSourceJets (fun s=>preparedOrdinarySourceJet q signal s i) t := by
  have quantum:=noetherHistorySourceJet_generated q (nativeTimeSignal signal) (nativeTimeHistory_smooth signal smooth).continuous t
    (nativeTimeSignal_generated signal smooth t) i
  have native:=nativeRemainderJet_generated signal smooth t i
  exact ⟨quantum.1.sub native.1,quantum.2.sub native.2⟩

theorem preparedOrdinarySourceJet_continuous (q : PhysicalResponsePoint) (signal : BasePoint→Field289)
    (smooth : ContDiff ℝ ∞ signal) (i : Fin 289) : ContinuousJets (fun t=>preparedOrdinarySourceJet q signal t i) := by
  have quantum:=noetherHistorySourceJet_continuous q (nativeTimeSignal signal) (nativeTimeSignal_continuous signal smooth) i
  have native:=nativeRemainderJet_continuous signal smooth i
  exact ⟨quantum.1.sub native.1,quantum.2.1.sub native.2.1,quantum.2.2.sub native.2.2⟩

theorem preparedOrdinarySource_actual (q : PhysicalResponsePoint) (signal : BasePoint→Field289)
    (smooth : ContDiff ℝ ∞ signal) (hz : q.z.im≠0) (hw : q.w.im≠0) (t : ℝ) (nonnegative : 0≤t)
    (inside : t<preparedHistoryDuration q (nativeTimeHistory signal)
      ((nativeTimeHistory_smooth signal smooth).contDiffAt.of_le (by
        change ((1 : ℕ∞) : ℕ∞ω)≤((⊤ : ℕ∞) : ℕ∞ω)
        exact WithTop.coe_le_coe.mpr le_top))) (i : Fin 289) :
    preparedOrdinarySource q signal t i=
      actualHistoryLinearSource q (nativeTimeSignal signal)
        ((nativeTimeHistory_smooth signal smooth).contDiffAt.of_le (by
          change ((1 : ℕ∞) : ℕ∞ω)≤((⊤ : ℕ∞) : ℕ∞ω)
          exact WithTop.coe_le_coe.mpr le_top)) t i-(nativeOrdinaryRemainder signal t i : ℂ) := by
  unfold preparedOrdinarySource
  rw [actualHistoryLinearSource_value q (nativeTimeSignal signal)
    ((nativeTimeHistory_smooth signal smooth).contDiffAt.of_le (by
      change ((1 : ℕ∞) : ℕ∞ω)≤((⊤ : ℕ∞) : ℕ∞ω)
      exact WithTop.coe_le_coe.mpr le_top)) hz hw t nonnegative inside]

/-- All 289 entries remain present; no Ward row is projected away. -/
def preparedOrdinaryForcing (q : PhysicalResponsePoint) (signal : BasePoint→Field289) (lambda : ℂ) (T : ℝ) : Fin 289→ℂ :=
  fun i=>∫ t in (0 : ℝ)..T,laplaceWeight lambda t*preparedOrdinarySource q signal t i

def nativeRemainderForcing (signal : BasePoint→Field289) (lambda : ℂ) (T : ℝ) : Fin 289→ℂ :=
  fun i=>∫ t in (0 : ℝ)..T,laplaceWeight lambda t*(nativeOrdinaryRemainder signal t i : ℂ)

theorem preparedOrdinaryForcing_components (q : PhysicalResponsePoint) (signal : BasePoint→Field289)
    (smooth : ContDiff ℝ ∞ signal) (lambda : ℂ) (T : ℝ) :
    preparedOrdinaryForcing q signal lambda T=noetherForcing q (nativeTimeSignal signal) lambda T-nativeRemainderForcing signal lambda T := by
  have weight : Continuous (laplaceWeight lambda) := by unfold laplaceWeight;fun_prop
  funext i
  unfold preparedOrdinaryForcing preparedOrdinarySource noetherForcing nativeRemainderForcing
  simp only [mul_sub,Pi.sub_apply]
  apply intervalIntegral.integral_sub
  · exact (weight.mul (noetherHistorySourceJet_continuous q (nativeTimeSignal signal)
      (nativeTimeSignal_continuous signal smooth) i).1).intervalIntegrable 0 T
  · exact (weight.mul (Complex.ofRealCLM.continuous.comp (nativeOrdinaryRemainder_smooth signal smooth i).continuous)).intervalIntegrable 0 T

theorem preparedOrdinaryForcing_actual (q : PhysicalResponsePoint) (signal : BasePoint→Field289)
    (smooth : ContDiff ℝ ∞ signal) (hz : q.z.im≠0) (hw : q.w.im≠0) (lambda : ℂ) (T : ℝ) (nonnegative : 0≤T)
    (inside : T<preparedHistoryDuration q (nativeTimeHistory signal)
      ((nativeTimeHistory_smooth signal smooth).contDiffAt.of_le (by
        change ((1 : ℕ∞) : ℕ∞ω)≤((⊤ : ℕ∞) : ℕ∞ω)
        exact WithTop.coe_le_coe.mpr le_top))) :
    preparedOrdinaryForcing q signal lambda T=
      actualHistoryForcing q (nativeTimeSignal signal)
        ((nativeTimeHistory_smooth signal smooth).contDiffAt.of_le (by
          change ((1 : ℕ∞) : ℕ∞ω)≤((⊤ : ℕ∞) : ℕ∞ω)
          exact WithTop.coe_le_coe.mpr le_top)) lambda T-nativeRemainderForcing signal lambda T := by
  rw [preparedOrdinaryForcing_components q signal smooth lambda T,
    actualHistoryForcing_noether q (nativeTimeSignal signal)
      ((nativeTimeHistory_smooth signal smooth).contDiffAt.of_le (by
        change ((1 : ℕ∞) : ℕ∞ω)≤((⊤ : ℕ∞) : ℕ∞ω)
        exact WithTop.coe_le_coe.mpr le_top)) hz hw lambda T nonnegative inside]

def preparedOrdinaryField (q : PhysicalResponsePoint) (signal : BasePoint→Field289)
    (lambda : physicalSpectralDomain q.k) (T : ℝ) : Fin 289→ℂ :=
  PreparationVacuumOriginalGreenFeedback.sourceField
    ⟨fullMomentum (physicalSpatial q.k) lambda.val,lambda.property⟩ (preparedOrdinaryForcing q signal lambda.val T)

theorem preparedOrdinaryField_native (q : PhysicalResponsePoint) (signal : BasePoint→Field289)
    (lambda : physicalSpectralDomain q.k) (T : ℝ) :
    nativeFourierHessian nativeHessian (fullMomentum (physicalSpatial q.k) lambda.val) *ᵥ
      preparedOrdinaryField q signal lambda T=
        preparedOrdinaryForcing q signal lambda.val T-
          originalRowLift (fullMomentum (physicalSpatial q.k) lambda.val) *ᵥ
            sourceCompatibility (fullMomentum (physicalSpatial q.k) lambda.val)
              (preparedOrdinaryForcing q signal lambda.val T) := by
  unfold preparedOrdinaryField
  exact nativeAction_sourceField ⟨fullMomentum (physicalSpatial q.k) lambda.val,lambda.property⟩ _

theorem preparedOrdinaryField_native36 (q : PhysicalResponsePoint) (signal : BasePoint→Field289)
    (lambda : physicalSpectralDomain q.k) (T : ℝ) :
    originalReader36 (fullMomentum (physicalSpatial q.k) lambda.val) *ᵥ
      (nativeFourierHessian nativeHessian (fullMomentum (physicalSpatial q.k) lambda.val) *ᵥ
        preparedOrdinaryField q signal lambda T)=
          originalReader36 (fullMomentum (physicalSpatial q.k) lambda.val) *ᵥ
            preparedOrdinaryForcing q signal lambda.val T-
              originalReader36 (fullMomentum (physicalSpatial q.k) lambda.val) *ᵥ
                (originalRowLift (fullMomentum (physicalSpatial q.k) lambda.val) *ᵥ
                  sourceCompatibility (fullMomentum (physicalSpatial q.k) lambda.val)
                    (preparedOrdinaryForcing q signal lambda.val T)) := by
  rw [preparedOrdinaryField_native,Matrix.mulVec_sub]

private theorem list_derivative {ι : Type*} (entries : List ι) (f df : ι→ℝ→ℂ) (t : ℝ)
    (paid : ∀a∈entries,HasDerivAt (f a) (df a t) t) :
    HasDerivAt (fun s=>(entries.map (fun a=>f a s)).sum) ((entries.map (fun a=>df a t)).sum) t := by
  induction entries with
  | nil=>exact hasDerivAt_const t 0
  | cons a rest ih=>simpa only [List.map_cons,List.sum_cons] using!
      (paid a (by simp)).add (ih (fun b hb=>paid b (by simp [hb])))

private theorem list_continuous {ι : Type*} (entries : List ι) (f : ι→ℝ→ℂ)
    (paid : ∀a∈entries,Continuous (f a)) : Continuous (fun t=>(entries.map (fun a=>f a t)).sum) := by
  induction entries with
  | nil=>exact continuous_const
  | cons a rest ih=>simpa only [List.map_cons,List.sum_cons] using!
      (paid a (by simp)).add (ih (fun b hb=>paid b (by simp [hb])))

private theorem boundary_derivative (j : ℝ→SourceJet ℂ) (lambda : ℂ) (t : ℝ)
    (paid : HasSourceJets j t) (n : Fin 3) :
    HasDerivAt (fun s=>laplaceWeight lambda s*initialCoSource lambda (j s) n)
      (laplaceWeight lambda t*(jetEntry (j t) n-lambda^n.val*(j t).value)) t := by
  run_tac
    let name:=(Lean.Name.num `_private.H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationPhysicalFullSourceWindow 0) ++
      `LowEnergy.PreparationVacuumPhysicalFeedback.weightedBoundaryDerivative
    Lean.Elab.Tactic.evalTactic (← `(tactic| exact $(Lean.mkIdent name) $(Lean.mkIdent `j) $(Lean.mkIdent `lambda)
      $(Lean.mkIdent `t) $(Lean.mkIdent `paid) $(Lean.mkIdent `n)))

def preparedOrdinaryTimeSource (q : PhysicalResponsePoint) (signal : BasePoint→Field289)
    (spatial : Fin 3→ℂ) (t : ℝ) (row : Fin 289) : ℂ :=
  (nativeReadbackTerms.attach.map (fun a=>if row=a.val.row then termSpatial spatial a.val*
    jetEntry (preparedOrdinarySourceJet q signal t a.val.column) (nativeTimeOrder a) else 0)).sum

def preparedOrdinaryBoundary (q : PhysicalResponsePoint) (signal : BasePoint→Field289)
    (spatial : Fin 3→ℂ) (lambda : ℂ) (t : ℝ) (row : Fin 289) : ℂ :=
  (nativeReadbackTerms.attach.map (fun a=>if row=a.val.row then termSpatial spatial a.val*
    (laplaceWeight lambda t*initialCoSource lambda (preparedOrdinarySourceJet q signal t a.val.column)
      (nativeTimeOrder a)) else 0)).sum

private def preparedOrdinaryDifference (q : PhysicalResponsePoint) (signal : BasePoint→Field289)
    (spatial : Fin 3→ℂ) (lambda : ℂ) (t : ℝ) (row : Fin 289) : ℂ :=
  (nativeReadbackTerms.attach.map (fun a=>if row=a.val.row then termSpatial spatial a.val*
    (laplaceWeight lambda t*(jetEntry (preparedOrdinarySourceJet q signal t a.val.column) (nativeTimeOrder a)-
      lambda^(nativeTimeOrder a).val*(preparedOrdinarySourceJet q signal t a.val.column).value)) else 0)).sum

theorem preparedOrdinaryBoundary_generated (q : PhysicalResponsePoint) (signal : BasePoint→Field289)
    (smooth : ContDiff ℝ ∞ signal) (spatial : Fin 3→ℂ) (lambda : ℂ) (t : ℝ) (row : Fin 289) :
    HasDerivAt (fun r=>preparedOrdinaryBoundary q signal spatial lambda r row)
      (preparedOrdinaryDifference q signal spatial lambda t row) t := by
  unfold preparedOrdinaryBoundary preparedOrdinaryDifference
  convert! list_derivative nativeReadbackTerms.attach
    (fun a r=>if row=a.val.row then termSpatial spatial a.val*
      (laplaceWeight lambda r*initialCoSource lambda (preparedOrdinarySourceJet q signal r a.val.column) (nativeTimeOrder a)) else 0)
    (fun a r=>if row=a.val.row then termSpatial spatial a.val*
      (laplaceWeight lambda r*(jetEntry (preparedOrdinarySourceJet q signal r a.val.column) (nativeTimeOrder a)-
        lambda^(nativeTimeOrder a).val*(preparedOrdinarySourceJet q signal r a.val.column).value)) else 0) t (by
    intro a _
    by_cases same : row=a.val.row
    · simp only [if_pos same]
      exact (boundary_derivative _ lambda t (preparedOrdinarySourceJet_generated q signal smooth t a.val.column) _).const_mul _
    · simp only [if_neg same]
      exact hasDerivAt_const t 0) using 1

private theorem weight_continuous (lambda : ℂ) : Continuous (laplaceWeight lambda) := by
  unfold laplaceWeight
  fun_prop

private theorem entry_continuous (j : ℝ→SourceJet ℂ) (paid : ContinuousJets j) (n : Fin 3) :
    Continuous (fun t=>jetEntry (j t) n) := by
  fin_cases n
  · exact paid.1
  · exact paid.2.1
  · exact paid.2.2

private theorem difference_continuous (q : PhysicalResponsePoint) (signal : BasePoint→Field289)
    (smooth : ContDiff ℝ ∞ signal) (spatial : Fin 3→ℂ) (lambda : ℂ) (row : Fin 289) :
    Continuous (fun t=>preparedOrdinaryDifference q signal spatial lambda t row) := by
  unfold preparedOrdinaryDifference
  apply list_continuous
  intro a _
  by_cases same : row=a.val.row
  · simp only [if_pos same]
    have source:=preparedOrdinarySourceJet_continuous q signal smooth a.val.column
    exact ((weight_continuous lambda).mul ((entry_continuous _ source _).sub (source.1.const_mul _))).const_mul _
  · simp only [if_neg same]
    exact continuous_const

private theorem timeSource_continuous (q : PhysicalResponsePoint) (signal : BasePoint→Field289)
    (smooth : ContDiff ℝ ∞ signal) (spatial : Fin 3→ℂ) (row : Fin 289) :
    Continuous (fun t=>preparedOrdinaryTimeSource q signal spatial t row) := by
  unfold preparedOrdinaryTimeSource
  apply list_continuous
  intro a _
  by_cases same : row=a.val.row
  · simp only [if_pos same]
    exact (entry_continuous _ (preparedOrdinarySourceJet_continuous q signal smooth a.val.column) _).const_mul _
  · simp only [if_neg same]
    exact continuous_const

private theorem weighted_list_difference {ι : Type*} (entries : List ι) (left right : ι→ℂ) (weight : ℂ) :
    (entries.map (fun a=>weight*(left a-right a))).sum=
      weight*((entries.map left).sum-(entries.map right).sum) := by
  induction entries with
  | nil=>simp
  | cons a rest ih=>simp only [List.map_cons,List.sum_cons,ih];ring

private theorem difference_source (q : PhysicalResponsePoint) (signal : BasePoint→Field289)
    (spatial : Fin 3→ℂ) (lambda : ℂ) (t : ℝ) (row : Fin 289) :
    preparedOrdinaryDifference q signal spatial lambda t row=laplaceWeight lambda t*
      (preparedOrdinaryTimeSource q signal spatial t row-
        fullFrequency spatial lambda (preparedOrdinarySource q signal t) row) := by
  unfold preparedOrdinaryDifference preparedOrdinaryTimeSource fullFrequency
  have actual:=weighted_list_difference nativeReadbackTerms.attach
    (fun a=>if row=a.val.row then termSpatial spatial a.val*jetEntry (preparedOrdinarySourceJet q signal t a.val.column) (nativeTimeOrder a) else 0)
    (fun a=>if row=a.val.row then termSpatial spatial a.val*lambda^(nativeTimeOrder a).val*(preparedOrdinarySourceJet q signal t a.val.column).value else 0)
    (laplaceWeight lambda t)
  apply Eq.trans _ actual
  · congr 1
    apply List.map_congr_left
    intro a _
    by_cases same : row=a.val.row
    · simp only [if_pos same]
      ring
    · simp only [if_neg same]
      ring

private theorem frequency_integral (q : PhysicalResponsePoint) (signal : BasePoint→Field289)
    (smooth : ContDiff ℝ ∞ signal) (spatial : Fin 3→ℂ) (lambda : ℂ) (T : ℝ) (row : Fin 289) :
    (∫ t in (0 : ℝ)..T,laplaceWeight lambda t*fullFrequency spatial lambda (preparedOrdinarySource q signal t) row)=
      fullFrequency spatial lambda (preparedOrdinaryForcing q signal lambda T) row := by
  simp_rw [fullFrequency_original]
  symm
  change (∑j,originalReadback (fullMomentum spatial lambda) row j*preparedOrdinaryForcing q signal lambda T j)=_
  simp_rw [preparedOrdinaryForcing,←intervalIntegral.integral_const_mul]
  have actual:=intervalIntegral.integral_finsetSum (s:=Finset.univ) (μ:=volume)
    (f:=fun (j : Fin 289) t=>originalReadback (fullMomentum spatial lambda) row j*(laplaceWeight lambda t*preparedOrdinarySource q signal t j))
    (fun j _=>(((weight_continuous lambda).mul (by
      simpa only [←preparedOrdinarySourceJet_value] using (preparedOrdinarySourceJet_continuous q signal smooth j).1)).const_mul _).intervalIntegrable 0 T)
  refine actual.symm.trans ?_
  apply intervalIntegral.integral_congr
  intro t _
  simp only [Matrix.mulVec,dotProduct,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem preparedOrdinaryForcing_cosources (q : PhysicalResponsePoint) (signal : BasePoint→Field289)
    (smooth : ContDiff ℝ ∞ signal) (spatial : Fin 3→ℂ) (lambda : ℂ) (T : ℝ) (row : Fin 289) :
    (originalReadback (fullMomentum spatial lambda) *ᵥ preparedOrdinaryForcing q signal lambda T) row=
      (∫ t in (0 : ℝ)..T,laplaceWeight lambda t*preparedOrdinaryTimeSource q signal spatial t row)-
        (preparedOrdinaryBoundary q signal spatial lambda T row-preparedOrdinaryBoundary q signal spatial lambda 0 row) := by
  have h:=intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _=>preparedOrdinaryBoundary_generated q signal smooth spatial lambda t row)
    ((difference_continuous q signal smooth spatial lambda row).intervalIntegrable 0 T)
  simp_rw [difference_source,mul_sub] at h
  have leftIntegral : IntervalIntegrable (fun t=>laplaceWeight lambda t*preparedOrdinaryTimeSource q signal spatial t row) volume 0 T :=
    ((weight_continuous lambda).mul (timeSource_continuous q signal smooth spatial row)).intervalIntegrable 0 T
  have rightContinuous : Continuous (fun t=>fullFrequency spatial lambda (preparedOrdinarySource q signal t) row) := by
    simp_rw [fullFrequency_original]
    change Continuous (fun t=>∑j,originalReadback (fullMomentum spatial lambda) row j*preparedOrdinarySource q signal t j)
    apply continuous_finsetSum
    intro j _
    have source : Continuous (fun t=>preparedOrdinarySource q signal t j) := by
      simpa only [←preparedOrdinarySourceJet_value] using (preparedOrdinarySourceJet_continuous q signal smooth j).1
    exact source.const_mul _
  have rightIntegral : IntervalIntegrable (fun t=>laplaceWeight lambda t*fullFrequency spatial lambda (preparedOrdinarySource q signal t) row) volume 0 T :=
    ((weight_continuous lambda).mul rightContinuous).intervalIntegrable 0 T
  rw [intervalIntegral.integral_sub leftIntegral rightIntegral,frequency_integral q signal smooth,
    fullFrequency_original] at h
  linear_combination -h

theorem preparedOrdinaryField_cosources (q : PhysicalResponsePoint) (signal : BasePoint→Field289)
    (smooth : ContDiff ℝ ∞ signal) (lambda : physicalSpectralDomain q.k) (T : ℝ) :
    preparedOrdinaryField q signal lambda T=
      originalChange (fullMomentum (physicalSpatial q.k) lambda.val) *ᵥ
        ((contactInverse (fullMomentum (physicalSpatial q.k) lambda.val)+activeProjection*
          (extendedKernel (fullMomentum (physicalSpatial q.k) lambda.val))⁻¹) *ᵥ
          (fun row=>(∫ t in (0 : ℝ)..T,laplaceWeight lambda.val t*preparedOrdinaryTimeSource q signal (physicalSpatial q.k) t row)-
            (preparedOrdinaryBoundary q signal (physicalSpatial q.k) lambda.val T row-
              preparedOrdinaryBoundary q signal (physicalSpatial q.k) lambda.val 0 row))) := by
  have read : originalReadback (fullMomentum (physicalSpatial q.k) lambda.val) *ᵥ
      preparedOrdinaryForcing q signal lambda.val T=
        (fun row=>(∫ t in (0 : ℝ)..T,laplaceWeight lambda.val t*preparedOrdinaryTimeSource q signal (physicalSpatial q.k) t row)-
          (preparedOrdinaryBoundary q signal (physicalSpatial q.k) lambda.val T row-
            preparedOrdinaryBoundary q signal (physicalSpatial q.k) lambda.val 0 row)) :=
    funext (preparedOrdinaryForcing_cosources q signal smooth (physicalSpatial q.k) lambda.val T)
  unfold preparedOrdinaryField PreparationVacuumOriginalGreenFeedback.sourceField sourceGreen
  rw [←Matrix.mulVec_mulVec,←Matrix.mulVec_mulVec,read]

end LowEnergy.SourcePropagationMotherEulerKernel
