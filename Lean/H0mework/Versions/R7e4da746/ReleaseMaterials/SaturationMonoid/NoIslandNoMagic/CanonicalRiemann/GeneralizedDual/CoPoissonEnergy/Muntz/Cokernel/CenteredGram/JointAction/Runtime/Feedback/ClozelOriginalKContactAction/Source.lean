import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKContactAction.Origin
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Material.Calculation.ClozelOriginalKContactActionProgram

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1200000
set_option pp.deepTerms.threshold 24
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalContactSource
open RootInquiryCompletion BurnolPhysicalState SourceOperationEffects SourceOperationExecution
namespace Input
export OriginalContactPriceInput
  (actualFace state trace uValue vValue alphaLift betaLift gapValue uTrace vTrace alphaTrace betaTrace gapTrace
   inheritedBTrace u_actual v_actual alpha_actual beta_actual gap_actual)
end Input
namespace P
export OriginalContactProgram (code environment forcingCode contactCode returnCode edgeCode code_eval forcing_eval contact_eval return_eval edge_eval code_budget)
end P
namespace M
export OriginalConstantFourierPriceMath (scalarRead embed)
end M
namespace Prog
export OriginalKPaNativePortSourceCalculation (Value Var E)
end Prog
namespace Prior
export OriginalCFixedAdjointAction (sourceRoot sourceVisit sourceU7 sourceCalculus sourceReader)
end Prior
namespace O
export RootGeneratedDebtActivationJointSource.OwnerFree (Raw)
end O
namespace Installed
export RootGeneratedDebtActivationJointSource.OwnerFree.Installation (ResultAt resultAt source_value source_history)
end Installed
open private targetRoot targetVisit frame_root frame_visit from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKPairedWaveNativeStockSource
open private result_expression from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKPairedWaveActionSource
open private mp_heq from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKOutsideCorrectionRSource

private theorem recognize (c:BurnolCompletedMellinCoordinate) (u v alpha beta gap:BurnolL2)
    (hu:u=M.embed OriginalRieszSource.Response.u) (hv:v=M.embed OriginalRieszSource.Response.v)
    (ha:M.scalarRead alpha=OriginalRieszSource.Kernel.A c)
    (hb:M.scalarRead beta=OriginalRieszSource.Kernel.beta c)
    (hg:gap=OriginalRieszSourceGreen.gapState c) :
    (P.code c alpha beta gap).eval (P.environment u v)=OriginalContactFeedbackSource.generatedContactAction c := by
  rw [P.code_eval,P.forcing_eval,P.contact_eval,P.return_eval,P.edge_eval,ha,hb,hg]
  change FiniteMobiusResolventFlux.Rplus (star c.value/2)
    (-burnolTateReciprocalL2 (FiniteMobiusResolventFlux.M (fourierL2
      (OriginalRieszSource.Kernel.A c • u-OriginalRieszSource.Kernel.beta c • v)))+
      FiniteMobiusResolventFlux.D (OriginalRieszSource.Kernel.beta c • u-OriginalRieszSource.Kernel.A c • v)-
      (2*(star c.value-1/2)*OriginalRieszSource.Kernel.beta c) •
        FiniteMobiusResolventFlux.D (fourierL2 (OriginalContactFeedbackSource.primitiveScale c • OriginalRieszSourceGreen.gapState c)))=_
  rw [hu,hv]
  have contact : OriginalRieszSource.Kernel.A c • M.embed OriginalRieszSource.Response.u-
      OriginalRieszSource.Kernel.beta c • M.embed OriginalRieszSource.Response.v=
        OriginalColumnMomentSource.wholeContactResponse c := by
    unfold OriginalColumnMomentSource.wholeContactResponse OriginalColumnMomentSource.contactResponse
    rw [map_sub,map_smul,map_smul]
    rfl
  have returned : OriginalRieszSource.Kernel.beta c • M.embed OriginalRieszSource.Response.u-
      OriginalRieszSource.Kernel.A c • M.embed OriginalRieszSource.Response.v=
        OriginalColumnMomentSource.wholeReturnResponse c := by
    rw [OriginalReturnResponseSource.original_return_response_occurrence]
    unfold OriginalReturnResponseSource.wholeReturnResponse
    rw [OriginalReturnResponseSource.actual_return_response_coefficients,map_add,map_smul,map_smul]
    change OriginalRieszSource.Kernel.beta c • burnolQuarterZeroExtension (OriginalRieszSource.Response.u:BurnolQuarterIntervalL2)-
      OriginalRieszSource.Kernel.A c • burnolQuarterZeroExtension (OriginalRieszSource.Response.v:BurnolQuarterIntervalL2)=_
    module
  rw [contact,returned,←OriginalContactFeedbackSource.original_primitive_gap_source]
  change FiniteMobiusResolventFlux.Rplus (star c.value/2) (OriginalColumnMomentSource.etaRemainingSource c)=_
  rw [OriginalReturnResponseSource.original_eta_remaining_action,
    OriginalFourierMobiusReturnSource.original_eta_fourier_action,OriginalContactFeedbackSource.original_complete_contact_action]

private abbrev Read {W:WorldRelationNetwork} {V:Vocabulary}
    (old:SourceNativeAuthoritativeRootClosure W V) :=
  {now:V.Current} → old.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt now →
    O.Raw (Value:=Prog.Value) (Var:=Prog.Var) (sort:=())
namespace Generated
variable {W:WorldRelationNetwork} {V:Vocabulary}
variable (old:SourceNativeAuthoritativeRootClosure W V) (stage:V.Current)
variable (c:BurnolCompletedMellinCoordinate) (u v alpha beta gap:BurnolL2)
noncomputable def reader : Read old := fun {_} _ => ⟨P.environment u v,P.code c alpha beta gap⟩
noncomputable def result : Installed.ResultAt old (reader old c u v alpha beta gap) (old.emitted stage) :=
  Installed.resultAt old (reader old c u v alpha beta gap) (old.emitted stage)
private theorem expression : type_of% (result_expression old (reader old c u v alpha beta gap) (old.emitted stage)) :=
  result_expression old (reader old c u v alpha beta gap) (old.emitted stage)
noncomputable def trace : Trace (P.environment u v) (P.code c alpha beta gap)
    (.const ((result old stage c u v alpha beta gap).2.2.1)) :=
  Eq.mp (congrArg (Trace (P.environment u v) (P.code c alpha beta gap))
    (expression old stage c u v alpha beta gap)) (result old stage c u v alpha beta gap).2.1.2
theorem trace_source : type_of% (mp_heq
    (congrArg (Trace (P.environment u v) (P.code c alpha beta gap)) (expression old stage c u v alpha beta gap))
      (result old stage c u v alpha beta gap).2.1.2) := mp_heq _ _
theorem equation : (result old stage c u v alpha beta gap).2.2.1=
    (P.code c alpha beta gap).eval (P.environment u v) :=
  Installed.source_value old (reader old c u v alpha beta gap) (old.emitted stage)
theorem paid : (result old stage c u v alpha beta gap).2.1.2.length=46 :=
  (Installed.source_history old (reader old c u v alpha beta gap) (old.emitted stage)).trans (P.code_budget c alpha beta gap)
noncomputable def tateInput := originalInput (trace old stage c u v alpha beta gap)
noncomputable def rInput := originalInput (tateInput old stage c u v alpha beta gap).2.1
noncomputable def forcingInput := originalInput (rInput old stage c u v alpha beta gap).2.1
end Generated

variable (observation:GeneratedRiemannZeroObservation)
variable (nontrivial:¬ ∃ n:Nat,observation.coordinate=-2*(n+1))
variable (half:OriginalKCombCalculation.Half observation) (depth ordinal:Nat) (t:ℝ)
local notation "prior" => Prior.sourceRoot observation nontrivial half depth ordinal t
local notation "visit" => Prior.sourceVisit observation nontrivial half depth ordinal t
local notation "u7" => Prior.sourceU7 observation nontrivial half depth ordinal t
local notation "calculus" => Prior.sourceCalculus observation nontrivial half depth ordinal t
local notation "priorReader" => Prior.sourceReader observation nontrivial half depth ordinal t
noncomputable def sourceRoot := targetRoot prior visit u7 calculus priorReader
noncomputable def sourceVisit := targetVisit prior visit u7 calculus priorReader
theorem source_frame_root : type_of% (frame_root prior visit u7 calculus priorReader) :=
  frame_root prior visit u7 calculus priorReader
theorem source_frame_visit : type_of% (frame_visit prior visit u7 calculus priorReader) :=
  frame_visit prior visit u7 calculus priorReader
private abbrev authority := (sourceRoot observation nontrivial half depth ordinal t).toAuthoritativeRoot
private abbrev current := (sourceVisit observation nontrivial half depth ordinal t).current
local notation "old" => authority observation nontrivial half depth ordinal t
local notation "now0" => current observation nontrivial half depth ordinal t
local notation "c" => OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half
local notation "u" => Input.uValue observation nontrivial half depth ordinal t
local notation "v" => Input.vValue observation nontrivial half depth ordinal t
local notation "alpha" => Input.alphaLift observation nontrivial half depth ordinal t
local notation "beta" => Input.betaLift observation nontrivial half depth ordinal t
local notation "gap" => Input.gapValue observation nontrivial half depth ordinal t
noncomputable def reader : Read old := Generated.reader old c u v alpha beta gap
noncomputable def result := Generated.result old now0 c u v alpha beta gap
noncomputable def trace := Generated.trace old now0 c u v alpha beta gap
theorem trace_source : type_of% (Generated.trace_source old now0 c u v alpha beta gap) := Generated.trace_source old now0 c u v alpha beta gap
theorem equation : type_of% (Generated.equation old now0 c u v alpha beta gap) := Generated.equation old now0 c u v alpha beta gap
theorem paid : type_of% (Generated.paid old now0 c u v alpha beta gap) := Generated.paid old now0 c u v alpha beta gap
noncomputable def tateInput := Generated.tateInput old now0 c u v alpha beta gap
noncomputable def rInput := Generated.rInput old now0 c u v alpha beta gap
noncomputable def forcingInput := Generated.forcingInput old now0 c u v alpha beta gap
theorem actual_output : (result observation nontrivial half depth ordinal t).2.2.1=
    OriginalContactFeedbackSource.generatedContactAction c :=
  (Generated.equation old now0 c u v alpha beta gap).trans
    (recognize c u v alpha beta gap (Input.u_actual observation nontrivial half depth ordinal t)
      (Input.v_actual observation nontrivial half depth ordinal t)
      (Input.alpha_actual observation nontrivial half depth ordinal t)
      (Input.beta_actual observation nontrivial half depth ordinal t)
      (Input.gap_actual observation nontrivial half depth ordinal t))
end OriginalContactSource
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
run_cmd Lean.modifyEnv fun env =>
  Lean.LibrarySuggestions.nameDenyListExt.addEntry env "OriginalContactSource"
