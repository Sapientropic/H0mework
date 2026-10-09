import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedPhaseHeldAction

set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
noncomputable section
namespace LowEnergy.GaussComposite.ActualDressedPhaseWard
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open StageNineHolonomicField FullQuantum.StateGreen
open SourceQuantumFockGauge SourceQuantumGaugeSliceCoordinates SourceQuantumConfigurationHilbert
open GaussCoreHilbert GaussCoreDifferential GaussQuantumMultiplier GaussHistoryHilbert
open PreparationVacuumMixedFieldReturn CanonicalGradedSpatialSource
open PreparationVacuumSourceFieldFamily PreparationVacuumNonlinearFieldCurve
open PreparationVacuumGaugeSourceInjection PreparationVacuumActionFieldLift PreparationVacuumActualFieldQuantization
open PreparationVacuumOriginalDensity PreparationVacuumJointFieldResponse PreparationVacuumRawJointFeedback
open PreparationVacuumFullFieldRiesz PreparationVacuumSourceActionJets PreparationVacuumPhysicalFeedback
open PreparationVacuumNoetherChart
open Filter Set MeasureTheory
open scoped Topology ContDiff BigOperators Matrix Matrix.Norms.L2Operator InnerProductSpace
abbrev Operator:=H→L[ℂ] H
attribute [local instance] SourceRealScalarFock.branchOrder
local instance : DecidableEq Quantum.Index:=Classical.decEq _
local instance : DecidableEq Mode:=Classical.decEq _
local instance : NormedAlgebra ℝ SourceMatrix:=NormedAlgebra.restrictScalars ℝ ℂ _
local instance : FiniteDimensional ℂ SourceMatrix:=Matrix.finiteDimensional
local instance : NormedAlgebra ℝ FullMatrix:=NormedAlgebra.restrictScalars ℝ ℂ _
local instance : FiniteDimensional ℂ FullMatrix:=Matrix.finiteDimensional
local instance : NormedAddCommGroup LorentzianCoframe:=Matrix.normedAddCommGroup
local instance : SeminormedAddCommGroup LorentzianCoframe:=Matrix.seminormedAddCommGroup
local instance : NormedSpace ℝ LorentzianCoframe:=Matrix.normedSpace
local instance : NormedAlgebra ℝ Operator:=NormedAlgebra.restrictScalars ℝ ℂ _

open PreparationVacuumNativeLocalWard PreparationVacuumNativeSourceRestriction PreparationVacuumHalfDensityFiber
local instance : Fintype NativeHistoryGrade.Label:=Fintype.ofFinite _
open ActualEMOriginWard Stage9C.Material.SpinPair PreparationVacuumPhysicalModeContact

private theorem direction_smooth (part : PhasePart) : ContDiff ℝ ∞ (phaseDirection part) := by
  cases part with
  | ward=>exact emGaugeState.toContinuousLinearMap.contDiff
  | scalar=>exact contDiff_const
  | deviation=>exact emGaugeState.toContinuousLinearMap.contDiff.comp (contDiff_id.sub contDiff_const)

private theorem direction_generated (part : PhasePart) (s : ActionState) (force : Field289) :
    HasDerivAt (fun r : ℝ=>phaseDirection part (s+r • fieldDirection force)) (phaseDirectionContact part force) 0 := by
  have ray:=state_line s (fieldDirection force)
  cases part with
  | ward=>exact emGaugeState.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt 0 ray
  | scalar=>exact hasDerivAt_const 0 emScalarCounterState
  | deviation=>
    exact emGaugeState.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt 0 (ray.sub_const _)

private theorem held_fiber_smooth (part : PhasePart) (p : PhysicalMomentum) (u : JointParameter)
    (base : u.2∈physicalChart) (valid : ambientState u∈validStates) :
    ContDiffAt ℝ ∞ (fun w : JointParameter=>quantizer (phaseHeldAction part p (sourceState w.2) (ambientState w))) u := by
  have bvalid : sourceState u.2∈validStates:=⟨coframe_nondegenerate ⟨u.2,base⟩,temporal_noncharacteristic ⟨u.2,base⟩⟩
  have bs:=sourceState_smooth.contDiffAt.comp u contDiffAt_snd
  have weight:=(sourceActionWeight_smooth (sourceState u.2) bvalid).comp u bs
  have first : ContDiffAt ℝ ∞ (fun s=>symbolFirst p s (phaseDirection part s)) (ambientState u) :=
    ((sourceSymbol_smooth p (ambientState u) valid).fderiv_right (m:=∞) (by simp)).clm_apply
      (direction_smooth part).contDiffAt
  have current:=first.comp u ambientState_smooth.contDiffAt
  exact (quantizer.toContinuousLinearMap.restrictScalars ℝ).contDiff.contDiffAt.comp u
    ((weight.mul current).const_smul (-(4:ℂ)))

private theorem held_fiber_generated (part : PhasePart) (force : Field289) (p : PhysicalMomentum) (z : physicalChart) :
    HasDerivAt (fun r : ℝ=>quantizer (phaseHeldAction part p (sourceState z.val) (ambientState (r • force,z.val))))
      (quantizer (phaseHeldMixed part force p (sourceState z.val) (sourceState z.val))) 0 := by
  let s:=sourceState z.val
  have valid : s∈validStates:=⟨coframe_nondegenerate z,temporal_noncharacteristic z⟩
  have outer:=((sourceSymbol_smooth p s valid).fderiv_right (m:=∞) (by simp)).differentiableAt (by simp)
  have D:=outer.hasFDerivAt.comp_hasDerivAt_of_eq 0 (state_line s (fieldDirection force)) (by simp)
  have generated:=(D.clm_apply (direction_generated part s force)).const_mul (sourceActionWeight s)
  have weighted:=generated.const_smul (-(4:ℂ))
  have full:=(quantizer.toContinuousLinearMap.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0 weighted
  convert! full using 1
  · funext r
    simp only [phaseHeldAction,ambientState,map_smul,s,Function.comp_apply,Pi.smul_apply,
      ContinuousLinearMap.coe_restrictScalars',LinearMap.coe_toContinuousLinearMap',symbolFirst]
    rfl
  · simp only [phaseHeldMixed,symbolSecond,symbolFirst,Function.comp_apply,zero_smul,add_zero,s,
      ContinuousLinearMap.coe_restrictScalars',LinearMap.coe_toContinuousLinearMap']

/-- The original full504 CAR is integrated against the same two compact source tests. -/
def phaseSample (part : PhasePart) (p : PhysicalMomentum) (a b : QuantumTest) (u : JointParameter) : ℂ :=
  pairSample u.2 (a u.2) (quantizer (phaseHeldAction part p (sourceState u.2) (ambientState u)) (b u.2))

private theorem phaseSample_zero (part : PhasePart) (p : PhysicalMomentum) (a b : QuantumTest)
    (h : Field289) (z : SourceCoordinateSlice) (outside : z∉tsupport a) : phaseSample part p a b (h,z)=0 := by
  simp only [phaseSample,image_eq_zero_of_notMem_tsupport outside,pairSample_zero_left]

private theorem phaseSample_smooth (part : PhasePart) (p : PhysicalMomentum) (a b : QuantumTest)
    (h : Field289) (z : SourceCoordinateSlice) (small : ‖h‖<ambientRadius a) :
    ContDiffAt ℝ ∞ (phaseSample part p a b) (h,z) := by
  by_cases inside : z∈tsupport a
  · let R:=ContinuousLinearMap.restrictScalarsL ℂ FockFiber FockFiber ℝ ℝ
    have coefficient:=R.contDiff.contDiffAt.comp (h,z)
      (held_fiber_smooth part p (h,z) (a.tsupport_subset inside) (ambientRadius_valid a h z small.le inside))
    exact pairSample_param Prod.snd _ _ (h,z) (a.tsupport_subset inside) contDiffAt_snd
      (a.contDiff.contDiffAt.comp (h,z) contDiffAt_snd)
      (coefficient.clm_apply (b.contDiff.contDiffAt.comp (h,z) contDiffAt_snd))
  · apply (contDiffAt_const (c:=(0:ℂ))).congr_of_eventuallyEq
    filter_upwards [continuous_snd.continuousAt.preimage_mem_nhds
      ((isClosed_tsupport a).isOpen_compl.mem_nhds inside)] with u hu
    exact phaseSample_zero part p a b u.1 u.2 hu

def phaseForm (part : PhasePart) (p : PhysicalMomentum) (a b : QuantumTest) (h : Field289) : ℂ :=
  ∫z,phaseSample part p a b (h,z) ∂GaussHistoryHilbert.configurationMeasure

theorem phase_forms_integrable (part : PhasePart) (p : PhysicalMomentum) (a b : QuantumTest)
    (h : Field289) (small : ‖h‖<ambientRadius a) :
    Integrable (fun z=>phaseSample part p a b (h,z)) GaussHistoryHilbert.configurationMeasure :=
  parameter_slice_integrable _ (tsupport a) a.hasCompactSupport h
    (fun z=>phaseSample_smooth part p a b h z small) (phaseSample_zero part p a b)

private theorem phaseForm_C2 (part : PhasePart) (p : PhysicalMomentum) (a b : QuantumTest) :
    ContDiffAt ℝ 2 (phaseForm part p a b) 0 :=
  source_integral_C2 _ (tsupport a) a.hasCompactSupport (ambientRadius a) (ambientRadius_positive a)
    (phaseSample_smooth part p a b) (phaseSample_zero part p a b)

private theorem phase_sample_return (p : PhysicalMomentum) (a b : QuantumTest)
    (h : Field289) (z : SourceCoordinateSlice) (small : ‖h‖<ambientRadius a) :
    (gaugeScale/2:ℝ) • noetherSample sourceModeField p a b (h,z)=
      phaseSample .ward p a b (h,z)-phaseSample .scalar p a b (h,z)-phaseSample .deviation p a b (h,z) := by
  by_cases inside : z∈tsupport a
  · have valid:=ambientRadius_valid a h z small.le inside
    change (gaugeScale/2:ℝ) • (pairRight z (a z))
        (quantizer (transportedRawSymbol sourceModeField (sourceState z) (ambientState (h,z)) p) (b z))=
      (pairRight z (a z)) (quantizer (phaseHeldAction .ward p (sourceState z) (ambientState (h,z))) (b z))-
      (pairRight z (a z)) (quantizer (phaseHeldAction .scalar p (sourceState z) (ambientState (h,z))) (b z))-
      (pairRight z (a z)) (quantizer (phaseHeldAction .deviation p (sourceState z) (ambientState (h,z))) (b z))
    have paid:=congrArg (fun M : FullMatrix=>(pairRight z (a z)) (quantizer M (b z)))
      (phase_held_transport p (sourceState z) (ambientState (h,z)) valid)
    simpa only [map_sub,LinearMap.map_smul_of_tower,ContinuousLinearMap.map_smul_of_tower,
      sub_apply,smul_apply] using paid
  · simp only [noetherSample_zero _ p a b h z inside,phaseSample_zero _ p a b h z inside,smul_zero,sub_self]

/-- The held Noether form, including its actual configuration and scalar terms, is generated before finite completion. -/
theorem phase_form_return (p : PhysicalMomentum) (a b : QuantumTest) (h : Field289) (small : ‖h‖<ambientRadius a) :
    (gaugeScale/2:ℝ) • noetherForm sourceModeField p a b h=
      phaseForm .ward p a b h-phaseForm .scalar p a b h-phaseForm .deviation p a b h := by
  have w:=phase_forms_integrable .ward p a b h small
  have s:=phase_forms_integrable .scalar p a b h small
  have d:=phase_forms_integrable .deviation p a b h small
  unfold noetherForm phaseForm
  rw [←integral_smul]
  have first:=integral_sub (w.sub s) d
  have second:=integral_sub w s
  simp only [Pi.sub_apply] at first second
  rw [←second,←first]
  exact integral_congr_ae (Eventually.of_forall (fun z=>phase_sample_return p a b h z small))

def phaseReader (part : PhasePart) (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) (h : Field289) : Operator :=
  finiteRiesz F (fun i j=>phaseForm part p (frameTest F i) (frameTest F j) h)

private theorem phaseReader_C2 (part : PhasePart) (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) :
    ContDiffAt ℝ 2 (phaseReader part p F) 0 := by
  apply ContDiffAt.sum
  intro i _
  apply ContDiffAt.sum
  intro j _
  exact (phaseForm_C2 part p (frameTest F i) (frameTest F j)).smul contDiffAt_const

def phaseReaderContact (part : PhasePart) (force : Field289) (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) : Operator :=
  fderiv ℝ (phaseReader part p F) 0 force

/-- The mixed contact is generated by differentiating the same compact source integral. -/
theorem phase_reader_generated (part : PhasePart) (force : Field289) (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) :
    HasDerivAt (fun r : ℝ=>phaseReader part p F (r • force)) (phaseReaderContact part force p F) 0 :=
  (phaseReader_C2 part p F).differentiableAt (by norm_num) |>.hasFDerivAt.comp_hasDerivAt_of_eq 0
    (fieldRay_derivative force 0) (by simp)

/-- This contact integrates the positively generated mixed full504 action, not a reader difference. -/
def phaseContactForm (part : PhasePart) (force : Field289) (p : PhysicalMomentum) (a b : QuantumTest) : ℂ :=
  ∫z,pairSample z (a z)
    (quantizer (phaseHeldMixed part force p (sourceState z) (sourceState z)) (b z))
      ∂GaussHistoryHilbert.configurationMeasure

private theorem phaseForm_generated (part : PhasePart) (force : Field289) (p : PhysicalMomentum) (a b : QuantumTest) :
    HasDerivAt (fun r : ℝ=>phaseForm part p a b (r • force)) (phaseContactForm part force p a b) 0 := by
  have differential:=source_integral_fderivative (phaseSample part p a b) (tsupport a) a.hasCompactSupport
    (ambientRadius a) (ambientRadius_positive a) (phaseSample_smooth part p a b)
    (phaseSample_zero part p a b) 0 (by simpa only [norm_zero] using half_pos (ambientRadius_positive a))
  have original:=differential.comp_hasDerivAt_of_eq 0 (fieldRay_derivative force 0) (by simp)
  have integrable:=parameter_slice_integrable (parameterPartial (phaseSample part p a b))
    (tsupport a) a.hasCompactSupport 0
    (fun z=>parameterPartial_smooth _ _ (phaseSample_smooth part p a b 0 z
      (by simpa using ambientRadius_positive a)))
    (parameterPartial_zero _ _ (isClosed_tsupport a) (phaseSample_zero part p a b))
  have each (z : SourceCoordinateSlice) : parameterPartial (phaseSample part p a b) (0,z) force=
      pairSample z (a z) (quantizer (phaseHeldMixed part force p (sourceState z) (sourceState z)) (b z)) := by
    by_cases inside : z∈tsupport a
    · have d:=parameterPartial_derivative (phaseSample part p a b) 0 z
        (phaseSample_smooth part p a b 0 z (by simpa using ambientRadius_positive a))
      have first:=d.comp_hasDerivAt_of_eq 0 (fieldRay_derivative force 0) (by simp)
      let E:=(ContinuousLinearMap.apply ℂ FockFiber (b z)).restrictScalars ℝ
      let P:=(pairRight z (a z)).restrictScalars ℝ
      have second:=P.hasFDerivAt.comp_hasDerivAt 0
        (E.hasFDerivAt.comp_hasDerivAt 0 (held_fiber_generated part force p ⟨z,a.tsupport_subset inside⟩))
      exact first.unique second
    · rw [parameterPartial_zero _ _ (isClosed_tsupport a) (phaseSample_zero part p a b) 0 z inside]
      simp only [image_eq_zero_of_notMem_tsupport inside,pairSample_zero_left,zero_apply]
  have value : (∫z,parameterPartial (phaseSample part p a b) (0,z) ∂GaussHistoryHilbert.configurationMeasure) force=
      phaseContactForm part force p a b := by
    rw [ContinuousLinearMap.integral_apply integrable]
    exact integral_congr_ae (Eventually.of_forall each)
  exact original.congr_deriv value

theorem phase_reader_contact_source (part : PhasePart) (force : Field289) (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) :
    phaseReaderContact part force p F=
      finiteRiesz F (fun i j=>phaseContactForm part force p (frameTest F i) (frameTest F j)) := by
  have generated : HasDerivAt (fun r : ℝ=>phaseReader part p F (r • force))
      (finiteRiesz F (fun i j=>phaseContactForm part force p (frameTest F i) (frameTest F j))) 0 := by
    apply HasDerivAt.fun_sum
    intro i _
    apply HasDerivAt.fun_sum
    intro j _
    exact (phaseForm_generated part force p (frameTest F i) (frameTest F j)).smul_const
      (InnerProductSpace.rankOne ℂ (frameVector F i) (frameVector F j))
  exact (phase_reader_generated part force p F).unique generated

private theorem finite_three {ι M : Type*} [Fintype ι] [AddCommGroup M] [Module ℂ M]
    (n w s d : ι→ι→ℂ) (v : ι→ι→M) (c : ℂ)
    (paid : ∀i j,c*n i j=w i j-s i j-d i j) :
    c • (∑i,∑j,n i j • v i j)=
      (∑i,∑j,w i j • v i j)-(∑i,∑j,s i j • v i j)-(∑i,∑j,d i j • v i j) := by
  simp only [Finset.smul_sum,smul_smul,←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [paid,sub_smul,sub_smul]

/-- Same F and same source chart: no change of completion or external legs occurs. -/
theorem phase_reader_germ (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) :
    (fun h=>(gaugeScale/2:ℝ) • noetherReader sourceModeField p F h)=ᶠ[𝓝 0]
      fun h=>phaseReader .ward p F h-phaseReader .scalar p F h-phaseReader .deviation p F h := by
  have entries : ∀ᶠh : Field289 in 𝓝 0,∀i j : FrameIndex F,
      (gaugeScale/2:ℝ) • noetherForm sourceModeField p (frameTest F i) (frameTest F j) h=
        phaseForm .ward p (frameTest F i) (frameTest F j) h-phaseForm .scalar p (frameTest F i) (frameTest F j) h-
          phaseForm .deviation p (frameTest F i) (frameTest F j) h := by
    apply eventually_all.mpr
    intro i
    apply eventually_all.mpr
    intro j
    have near : ∀ᶠh : Field289 in 𝓝 0,‖h‖<ambientRadius (frameTest F i) :=
      (continuous_norm.tendsto 0).eventually (gt_mem_nhds (by simpa using ambientRadius_positive (frameTest F i)))
    exact near.mono (fun h small=>phase_form_return p (frameTest F i) (frameTest F j) h small)
  filter_upwards [entries] with h paid
  unfold noetherReader phaseReader finiteRiesz
  have generated:=finite_three (ι:=FrameIndex F) (M:=Operator)
    (fun i j=>noetherForm sourceModeField p (frameTest F i) (frameTest F j) h)
    (fun i j=>phaseForm .ward p (frameTest F i) (frameTest F j) h)
    (fun i j=>phaseForm .scalar p (frameTest F i) (frameTest F j) h)
    (fun i j=>phaseForm .deviation p (frameTest F i) (frameTest F j) h)
    (fun i j=>InnerProductSpace.rankOne ℂ (frameVector F i) (frameVector F j))
    ((gaugeScale/2:ℝ):ℂ) (fun i j=>by simpa only [Complex.real_smul] using paid i j)
  calc
    _=((gaugeScale/2:ℝ):ℂ) • (∑i,∑j,noetherForm sourceModeField p (frameTest F i) (frameTest F j) h •
        InnerProductSpace.rankOne ℂ (frameVector F i) (frameVector F j)) := by
      apply ContinuousLinearMap.ext
      intro v
      exact RCLike.real_smul_eq_coe_smul (K:=ℂ) (gaugeScale/2) _
    _=_ := generated

theorem phase_reader_initial (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) :
    (gaugeScale/2:ℝ) • noetherReader sourceModeField p F 0=
      phaseReader .ward p F 0-phaseReader .scalar p F 0-phaseReader .deviation p F 0 :=
  (phase_reader_germ p F).self_of_nhds

theorem phase_reader_contact (force : Field289) (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) :
    (gaugeScale/2:ℝ) • noetherReaderContact sourceModeField force p F=
      phaseReaderContact .ward force p F-phaseReaderContact .scalar force p F-phaseReaderContact .deviation force p F := by
  have left:=(noetherReader_generated sourceModeField force p F).const_smul (gaugeScale/2:ℝ)
  have right:=((phase_reader_generated .ward force p F).sub (phase_reader_generated .scalar force p F)).sub
    (phase_reader_generated .deviation force p F)
  have same:=(phase_reader_germ p F).comp_tendsto
    (by simpa only [zero_smul] using (fieldRay_derivative force 0).continuousAt.tendsto)
  exact left.unique (right.congr_of_eventuallyEq same)

end LowEnergy.GaussComposite.ActualDressedPhaseWard
