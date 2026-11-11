import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKConstantFourierResponse.Consumer
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Execution.Trace.Add

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1200000
set_option pp.deepTerms.threshold 24
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalConstantFourierFullResponseSource
open RootInquiryCompletion BurnolPhysicalState SourceOperationEffects SourceOperationExecution OriginalRieszSource
open FixedWindowFourierReaction FixedWindowFourierReaction.FullSchur
namespace Prior
export OriginalConstantFourierResponseAction
  (sourceRoot sourceVisit sourceU7 sourceCalculus sourceReader actualFrame actualOriginFace)
end Prior
namespace C
export OriginalConstantFourierResponseConsumer
  (nextFace nextState nextValue next_state_source next_trace_source next_value_source etaInput eta_actual)
end C
namespace R
export OriginalConstantFourierResponseSource (embed read u_actual)
end R
namespace N
export OriginalConstantFourierNativeConsumer (eta u v mu nu forcing actual_existing_inverse)
end N
namespace Prog
export OriginalKPaNativePortSourceCalculation (Value Var E)
end Prog
namespace O
export RootGeneratedDebtActivationJointSource.OwnerFree (Raw)
end O
namespace Installed
export RootGeneratedDebtActivationJointSource.OwnerFree.Installation (ResultAt resultAt source_history)
end Installed
open private result_expression from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKPairedWaveActionSource
open private mp_heq from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKOutsideCorrectionRSource
open private targetRoot targetVisit frame_root frame_visit from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKPairedWaveNativeStockSource
open private read_embed from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKConstantFourierResponse.Source

local notation "Hq" => BurnolQuarterIntervalL2
local notation "M" => BurnolQuarterMeanZeroCarrier
local notation "q" => (1/4:ℝ)
local notation "T" => burnolTruncatedFourier
local notation "S" => burnolMeanZeroTruncatedFourier
local notation "E" => burnolQuarterZeroExtension
local notation "Rq" => burnolQuarterRestriction

noncomputable def constant : BurnolL2 := E (intervalConstant q)
noncomputable def meanRead : Hq →L[ℂ] ℂ :=
  (((‖intervalConstant q‖^2:ℝ):ℂ)⁻¹) • innerSL ℂ (intervalConstant q)
noncomputable def meanScalar : BurnolL2 →L[ℂ] ℂ := meanRead.comp ((T).comp Rq)
noncomputable def meanChannel : BurnolL2 →L[ℂ] BurnolL2 := meanScalar.smulRight constant
noncomputable def wave : BurnolL2 →L[ℂ] BurnolL2 := R.embed.comp ((S).comp R.read)
noncomputable def ambientFourier : BurnolL2 →L[ℂ] BurnolL2 := (E).comp ((T).comp Rq)
noncomputable def fullInverse : BurnolL2 →L[ℂ] BurnolL2 :=
  (E).comp (quarterChart.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((sourceInverse q).comp (quarterChart.toContinuousLinearEquiv.toContinuousLinearMap.comp Rq)))

theorem constant_normalization : (‖intervalConstant q‖^2:ℝ)=1/2 := by
  have source := burnolIntervalConstant_norm_sq (by norm_num : (0:ℝ)<q)
  have real := congrArg Complex.re source
  norm_num [← Complex.ofReal_pow] at real
  exact real

theorem mean_read (value:Hq) : meanRead value=burnolQuarterMeanCoefficient value := by
  change (((‖intervalConstant q‖^2:ℝ):ℂ)⁻¹)*inner ℂ (intervalConstant q) value=
    inner ℂ (intervalConstant q) value/((‖intervalConstant q‖^2:ℝ):ℂ)
  exact (mul_comm _ _).trans (div_eq_mul_inv _ _).symm

private theorem wave_embed (value:M) : wave (R.embed value)=R.embed (S value) := by
  change R.embed (S (R.read (R.embed value)))=_
  rw [read_embed]
private theorem mean_embed (value:M) : meanScalar (R.embed value)=
    burnolQuarterMeanCoefficient (T (value:Hq)) := by
  change meanRead (T (Rq (E (value:Hq))))=_
  rw [burnolQuarterRestriction_zeroExtension,mean_read]
private theorem full_inverse_extension (value:Hq) : fullInverse (E value)=
    E (quarterChart.symm (sourceInverse q (quarterChart value))) := by
  change E (quarterChart.symm (sourceInverse q (quarterChart (Rq (E value)))))=_
  rw [burnolQuarterRestriction_zeroExtension]

noncomputable def forcingWord (u eta:BurnolL2) : BurnolL2 :=
  eta + -(meanScalar (wave u) • constant) + -(ambientFourier (meanScalar u • constant))

private theorem forcing_embed (u eta:M) : forcingWord (R.embed u) (R.embed eta)=
    E ((eta:Hq)-burnolQuarterMeanCoefficient (T (S u:Hq)) • intervalConstant q-
      burnolQuarterMeanCoefficient (T (u:Hq)) • T (intervalConstant q)) := by
  unfold forcingWord
  rw [wave_embed,mean_embed,mean_embed]
  change E (eta:Hq) + -(burnolQuarterMeanCoefficient (T (S u:Hq)) • E (intervalConstant q)) +
    -(E (T (Rq (burnolQuarterMeanCoefficient (T (u:Hq)) • E (intervalConstant q)))))=_
  rw [map_smul,burnolQuarterRestriction_zeroExtension,map_smul,map_smul,
    map_sub,map_sub,map_smul,map_smul]
  simp only [sub_eq_add_neg]

private def linear (operation:BurnolL2 →L[ℂ] BurnolL2) (body:Prog.E) : Prog.E :=
  .linear operation.toLinearMap.toAddMonoidHom body
private noncomputable def negate : BurnolL2 →L[ℂ] BurnolL2 := -ContinuousLinearMap.id ℂ BurnolL2
noncomputable def vCode : Prog.E := linear wave (.var (0:Fin 2))
noncomputable def nuCode : Prog.E := linear meanChannel vCode
noncomputable def muCode : Prog.E := linear meanChannel (.var (0:Fin 2))
noncomputable def leftCode : Prog.E := .add (.var (1:Fin 2)) (linear negate nuCode)
noncomputable def rightCode : Prog.E := linear negate (linear ambientFourier muCode)
noncomputable def forcingCode : Prog.E := .add leftCode rightCode
noncomputable def code : Prog.E := linear fullInverse forcingCode

private abbrev Read {W:WorldRelationNetwork} {V:Vocabulary}
    (old:SourceNativeAuthoritativeRootClosure W V) :=
  {now:V.Current} → old.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt now →
    O.Raw (Value:=Prog.Value) (Var:=Prog.Var) (sort:=())

namespace Generated
variable {W:WorldRelationNetwork} {V:Vocabulary}
variable (old:SourceNativeAuthoritativeRootClosure W V) (stage:V.Current) (u eta:BurnolL2)
noncomputable def environment : Env Prog.Value Prog.Var := fun _ index => Fin.cases u (fun _:Fin 1 => eta) index
noncomputable def reader : Read old := fun {_} _ => ⟨environment u eta,code⟩
noncomputable def result : Installed.ResultAt old (reader old u eta) (old.emitted stage) :=
  Installed.resultAt old (reader old u eta) (old.emitted stage)
private theorem expression : type_of% (result_expression old (reader old u eta) (old.emitted stage)) :=
  result_expression old (reader old u eta) (old.emitted stage)
noncomputable def trace : Trace (environment u eta) code (.const ((result old stage u eta).2.2.1)) :=
  Eq.mp (congrArg (Trace (environment u eta) code) (expression old stage u eta)) (result old stage u eta).2.1.2
theorem trace_source : type_of% (mp_heq
    (congrArg (Trace (environment u eta) code) (expression old stage u eta)) (result old stage u eta).2.1.2) :=
  mp_heq _ _
noncomputable def inverseInput := originalInput (trace old stage u eta)
noncomputable def forcingSplit := Trace.splitAdd (inverseInput old stage u eta).2.1
noncomputable def leftSplit := Trace.splitAdd (forcingSplit old stage u eta).leftTrace
noncomputable def nuNegInput := originalInput (leftSplit old stage u eta).rightTrace
noncomputable def nuInput := originalInput (nuNegInput old stage u eta).2.1
noncomputable def vInput := originalInput (nuInput old stage u eta).2.1
noncomputable def muNegInput := originalInput (forcingSplit old stage u eta).rightTrace
noncomputable def muFourierInput := originalInput (muNegInput old stage u eta).2.1
noncomputable def muInput := originalInput (muFourierInput old stage u eta).2.1
noncomputable def rawMu : ℂ := meanScalar (muInput old stage u eta).1
noncomputable def rawNu : ℂ := meanScalar (nuInput old stage u eta).1
theorem u_binding : (vInput old stage u eta).1=u := (vInput old stage u eta).2.1.sound.symm
theorem mu_binding : (muInput old stage u eta).1=u := (muInput old stage u eta).2.1.sound.symm
theorem eta_binding : (leftSplit old stage u eta).leftValue=eta := (leftSplit old stage u eta).leftTrace.sound.symm
theorem v_equation : (nuInput old stage u eta).1=wave u := (nuInput old stage u eta).2.1.sound.symm
theorem nu_lift : (nuNegInput old stage u eta).1=rawNu old stage u eta • constant :=
  (nuInput old stage u eta).2.2.down.symm
theorem mu_lift : (muFourierInput old stage u eta).1=rawMu old stage u eta • constant :=
  (muInput old stage u eta).2.2.down.symm
theorem forcing_equation : (inverseInput old stage u eta).1=forcingWord u eta :=
  (inverseInput old stage u eta).2.1.sound.symm
theorem equation : (result old stage u eta).2.2.1=fullInverse ((inverseInput old stage u eta).1) :=
  (inverseInput old stage u eta).2.2.down.symm
theorem paid : (result old stage u eta).2.1.2.length=12 :=
  Installed.source_history old (reader old u eta) (old.emitted stage)
end Generated

variable (observation:GeneratedRiemannZeroObservation)
variable (nontrivial:¬ ∃ n:Nat, observation.coordinate = -2*(n+1))
variable (half:OriginalKCombCalculation.Half observation) (depth ordinal:Nat) (t:ℝ)
local notation "baseRoot" => Prior.sourceRoot observation nontrivial half depth ordinal t
local notation "baseVisit" => Prior.sourceVisit observation nontrivial half depth ordinal t
local notation "baseU7" => Prior.sourceU7 observation nontrivial half depth ordinal t
local notation "baseCalculus" => Prior.sourceCalculus observation nontrivial half depth ordinal t
local notation "baseReader" => Prior.sourceReader observation nontrivial half depth ordinal t
noncomputable def sourceRoot := targetRoot baseRoot baseVisit baseU7 baseCalculus baseReader
noncomputable def sourceVisit := targetVisit baseRoot baseVisit baseU7 baseCalculus baseReader
private abbrev auth := (sourceRoot observation nontrivial half depth ordinal t).toAuthoritativeRoot
private abbrev current := (sourceVisit observation nontrivial half depth ordinal t).current
local notation "old" => auth observation nontrivial half depth ordinal t
local notation "now0" => current observation nontrivial half depth ordinal t

noncomputable def inputFace := C.nextFace observation nontrivial half depth ordinal t
noncomputable def inputState := C.nextState observation nontrivial half depth ordinal t
noncomputable def inputU : BurnolL2 := C.nextValue observation nontrivial half depth ordinal t
noncomputable def inputEtaReceipt := C.etaInput observation nontrivial half depth ordinal t
noncomputable def inputEta : BurnolL2 := (inputEtaReceipt observation nontrivial half depth ordinal t).1
local notation "actualU" => inputU observation nontrivial half depth ordinal t
local notation "actualEta" => inputEta observation nontrivial half depth ordinal t

theorem source_frame_root : type_of% (frame_root baseRoot baseVisit baseU7 baseCalculus baseReader) :=
  frame_root baseRoot baseVisit baseU7 baseCalculus baseReader
theorem source_frame_visit : type_of% (frame_visit baseRoot baseVisit baseU7 baseCalculus baseReader) :=
  frame_visit baseRoot baseVisit baseU7 baseCalculus baseReader
theorem input_state_source : type_of% (C.next_state_source observation nontrivial half depth ordinal t) :=
  C.next_state_source observation nontrivial half depth ordinal t
theorem input_trace_source : type_of% (C.next_trace_source observation nontrivial half depth ordinal t) :=
  C.next_trace_source observation nontrivial half depth ordinal t
theorem input_u_actual : actualU=R.embed (N.u observation nontrivial half depth ordinal t) :=
  (C.next_value_source observation nontrivial half depth ordinal t).trans
    (R.u_actual observation nontrivial half depth ordinal t)
theorem input_eta_actual : actualEta=R.embed (N.eta observation nontrivial half depth ordinal t) :=
  C.eta_actual observation nontrivial half depth ordinal t

noncomputable def environment := Generated.environment actualU actualEta
noncomputable def reader : Read old := Generated.reader old actualU actualEta
noncomputable def result := Generated.result old now0 actualU actualEta
noncomputable def trace := Generated.trace old now0 actualU actualEta
noncomputable def inverseInput := Generated.inverseInput old now0 actualU actualEta
noncomputable def nuNegInput := Generated.nuNegInput old now0 actualU actualEta
noncomputable def nuInput := Generated.nuInput old now0 actualU actualEta
noncomputable def vInput := Generated.vInput old now0 actualU actualEta
noncomputable def muFourierInput := Generated.muFourierInput old now0 actualU actualEta
noncomputable def muInput := Generated.muInput old now0 actualU actualEta
noncomputable def rawMu := Generated.rawMu old now0 actualU actualEta
noncomputable def rawNu := Generated.rawNu old now0 actualU actualEta

theorem trace_source : type_of% (Generated.trace_source old now0 actualU actualEta) :=
  Generated.trace_source old now0 actualU actualEta
theorem u_binding : type_of% (Generated.u_binding old now0 actualU actualEta) :=
  Generated.u_binding old now0 actualU actualEta
theorem mu_binding : type_of% (Generated.mu_binding old now0 actualU actualEta) :=
  Generated.mu_binding old now0 actualU actualEta
theorem eta_binding : type_of% (Generated.eta_binding old now0 actualU actualEta) :=
  Generated.eta_binding old now0 actualU actualEta
theorem nu_lift : type_of% (Generated.nu_lift old now0 actualU actualEta) :=
  Generated.nu_lift old now0 actualU actualEta
theorem mu_lift : type_of% (Generated.mu_lift old now0 actualU actualEta) :=
  Generated.mu_lift old now0 actualU actualEta
theorem equation : type_of% (Generated.equation old now0 actualU actualEta) :=
  Generated.equation old now0 actualU actualEta
theorem paid : type_of% (Generated.paid old now0 actualU actualEta) :=
  Generated.paid old now0 actualU actualEta

theorem v_actual : (nuInput observation nontrivial half depth ordinal t).1=
    R.embed (N.v observation nontrivial half depth ordinal t) :=
  (Generated.v_equation old now0 actualU actualEta).trans
    ((congrArg wave (input_u_actual observation nontrivial half depth ordinal t)).trans
      (wave_embed (N.u observation nontrivial half depth ordinal t)))
theorem mu_scalar_actual : rawMu observation nontrivial half depth ordinal t=
    N.mu observation nontrivial half depth ordinal t :=
  (congrArg meanScalar (Generated.mu_binding old now0 actualU actualEta)).trans
    ((congrArg meanScalar (input_u_actual observation nontrivial half depth ordinal t)).trans
      (mean_embed (N.u observation nontrivial half depth ordinal t)))
theorem nu_scalar_actual : rawNu observation nontrivial half depth ordinal t=
    N.nu observation nontrivial half depth ordinal t :=
  (congrArg meanScalar (v_actual observation nontrivial half depth ordinal t)).trans
    (mean_embed (N.v observation nontrivial half depth ordinal t))

theorem actual_forcing : (inverseInput observation nontrivial half depth ordinal t).1=
    E (N.forcing observation nontrivial half depth ordinal t) :=
  (Generated.forcing_equation old now0 actualU actualEta).trans
    ((congrArg₂ forcingWord (input_u_actual observation nontrivial half depth ordinal t)
      (input_eta_actual observation nontrivial half depth ordinal t)).trans
        (forcing_embed (N.u observation nontrivial half depth ordinal t)
          (N.eta observation nontrivial half depth ordinal t)))

theorem output_actual : (result observation nontrivial half depth ordinal t).2.2.1=
    R.embed (N.u observation nontrivial half depth ordinal t) := by
  have generated := (Generated.equation old now0 actualU actualEta).trans
    (congrArg fullInverse (actual_forcing observation nontrivial half depth ordinal t))
  have restored := congrArg (fun value => E (quarterChart.symm value))
    (N.actual_existing_inverse observation nontrivial half depth ordinal t)
  rw [quarterChart.symm_apply_apply] at restored
  exact generated.trans ((full_inverse_extension (N.forcing observation nontrivial half depth ordinal t)).trans restored)

theorem actual_return : (result observation nontrivial half depth ordinal t).2.2.1=actualU :=
  (output_actual observation nontrivial half depth ordinal t).trans
    (input_u_actual observation nontrivial half depth ordinal t).symm

end OriginalConstantFourierFullResponseSource
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end

run_cmd Lean.modifyEnv fun env =>
  Lean.LibrarySuggestions.nameDenyListExt.addEntry env "OriginalConstantFourierFullResponseSource"
