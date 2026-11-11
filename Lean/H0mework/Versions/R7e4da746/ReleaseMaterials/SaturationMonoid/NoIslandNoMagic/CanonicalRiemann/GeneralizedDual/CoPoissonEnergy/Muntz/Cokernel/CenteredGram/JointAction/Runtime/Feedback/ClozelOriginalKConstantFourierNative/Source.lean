import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKConstantFourierNative.Seed
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.TruncatedFourier.Radius.Scaling.Variation.FiniteRank.Source.ConstantFourierEuler

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1200000
set_option pp.deepTerms.threshold 24
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalConstantFourierNativeSource
open BurnolPhysicalState SourceOperationEffects SourceOperationExecution
namespace Root
export OriginalConstantFourierNativeSeed (sourceRoot sourceVisit seedValue seedTrace seed_trace_source seed_value)
end Root
namespace Prog
export OriginalKPaNativePortSourceCalculation (Value Var E)
end Prog
namespace O
export RootGeneratedDebtActivationJointSource.OwnerFree (Raw)
end O
namespace Installed
export RootGeneratedDebtActivationJointSource.OwnerFree.Installation (ResultAt resultAt source_history)
end Installed
namespace Flow
export ConstantFourierEulerVelocity
  (originalSource originalVelocity originalSource_actual originalSource_hasDerivAt
   original_mean_hasDerivAt original_centered_hasDerivAt original_u_hasDerivAt original_v_hasDerivAt)
end Flow
open private result_expression from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKPairedWaveActionSource
open private mp_heq from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKOutsideCorrectionRSource

def window : BurnolL2 →L[ℂ] BurnolL2 := burnolQuarterZeroExtension.comp burnolQuarterRestriction
private def linear (operation : BurnolL2 →L[ℂ] BurnolL2) (body : Prog.E) : Prog.E :=
  .linear operation.toLinearMap.toAddMonoidHom body
noncomputable def normalize (t : ℝ) : BurnolL2 →L[ℂ] BurnolL2 :=
  (Real.exp (-t/2) : ℂ) • ContinuousLinearMap.id ℂ BurnolL2
noncomputable def fourierCode : Prog.E := linear fourierL2.toContinuousLinearEquiv.toContinuousLinearMap (.var (0 : Fin 2))
noncomputable def dilationCode (t : ℝ) : Prog.E :=
  linear (burnolMultiplicativeDilation t).toContinuousLinearEquiv.toContinuousLinearMap fourierCode
noncomputable def windowCode (t : ℝ) : Prog.E := linear window (dilationCode t)
noncomputable def code (t : ℝ) : Prog.E := linear (normalize t) (windowCode t)

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2*(n+1))
variable (half : OriginalKCombCalculation.Half observation) (depth ordinal : Nat)
abbrev sourceRoot := Root.sourceRoot observation nontrivial half depth ordinal
abbrev sourceVisit := Root.sourceVisit observation nontrivial half depth ordinal
private abbrev authority := (sourceRoot observation nontrivial half depth ordinal).toAuthoritativeRoot
private abbrev current := (sourceVisit observation nontrivial half depth ordinal).current
private abbrev occurrence := (sourceRoot observation nontrivial half depth ordinal).emitted
  (current observation nontrivial half depth ordinal)
local notation "auth" => authority observation nontrivial half depth ordinal
local notation "now0" => current observation nontrivial half depth ordinal
local notation "point" => occurrence observation nontrivial half depth ordinal

noncomputable def environment : Env Prog.Value Prog.Var := fun _ _ => Root.seedValue observation nontrivial half depth ordinal

noncomputable def reader (t : ℝ)
    {now : (OriginalWholeDebtRPairedWaveNativeStockConsumer.actualBirthTarget observation nontrivial half depth ordinal).TargetV.Current}
    (_source : (auth).toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt now) :
    O.Raw (Value := Prog.Value) (Var := Prog.Var) (sort := ()) :=
  ⟨environment observation nontrivial half depth ordinal, code t⟩

noncomputable def result (t : ℝ) : Installed.ResultAt auth (reader observation nontrivial half depth ordinal t) point :=
  Installed.resultAt auth (reader observation nontrivial half depth ordinal t) point

private theorem expression (t : ℝ) : type_of% (result_expression auth
    (reader observation nontrivial half depth ordinal t) point) :=
  result_expression auth (reader observation nontrivial half depth ordinal t) point

noncomputable def trace (t : ℝ) : Trace (environment observation nontrivial half depth ordinal) (code t)
    (.const ((result observation nontrivial half depth ordinal t).2.2.1)) :=
  Eq.mp (congrArg (fun expression => Trace (environment observation nontrivial half depth ordinal) (code t) expression)
    (expression observation nontrivial half depth ordinal t)) (result observation nontrivial half depth ordinal t).2.1.2

theorem trace_source (t : ℝ) : type_of% (mp_heq
    (congrArg (fun expression => Trace (environment observation nontrivial half depth ordinal) (code t) expression)
      (expression observation nontrivial half depth ordinal t)) (result observation nontrivial half depth ordinal t).2.1.2) :=
  mp_heq _ _

noncomputable def normalizationInput (t : ℝ) : Σ value : BurnolL2,
    Trace (environment observation nontrivial half depth ordinal) (windowCode t) (.const value) ×
      PLift (normalize t value = (result observation nontrivial half depth ordinal t).2.2.1) :=
  originalInput (trace observation nontrivial half depth ordinal t)
noncomputable def windowInput (t : ℝ) : Σ value : BurnolL2,
    Trace (environment observation nontrivial half depth ordinal) (dilationCode t) (.const value) ×
      PLift (window value = (normalizationInput observation nontrivial half depth ordinal t).1) :=
  originalInput (normalizationInput observation nontrivial half depth ordinal t).2.1
noncomputable def dilationInput (t : ℝ) : Σ value : BurnolL2,
    Trace (environment observation nontrivial half depth ordinal) fourierCode (.const value) ×
      PLift (burnolMultiplicativeDilation t value = (windowInput observation nontrivial half depth ordinal t).1) :=
  originalInput (windowInput observation nontrivial half depth ordinal t).2.1
noncomputable def fourierInput (t : ℝ) : Σ value : BurnolL2,
    Trace (environment observation nontrivial half depth ordinal) (.var (0 : Fin 2) : Prog.E) (.const value) ×
      PLift (fourierL2 value = (dilationInput observation nontrivial half depth ordinal t).1) :=
  originalInput (dilationInput observation nontrivial half depth ordinal t).2.1

theorem input_binding (t : ℝ) : (fourierInput observation nontrivial half depth ordinal t).1 =
    Root.seedValue observation nontrivial half depth ordinal :=
  (fourierInput observation nontrivial half depth ordinal t).2.1.sound.symm

theorem equation (t : ℝ) : (result observation nontrivial half depth ordinal t).2.2.1 =
    (Real.exp (-t/2) : ℂ) • burnolQuarterZeroExtension (burnolQuarterRestriction
      (burnolMultiplicativeDilation t (fourierL2 (Root.seedValue observation nontrivial half depth ordinal)))) :=
  (trace observation nontrivial half depth ordinal t).sound.symm

theorem original_full_value (t : ℝ) : (result observation nontrivial half depth ordinal t).2.2.1 =
    burnolQuarterZeroExtension (Flow.originalSource t) := by
  rw [equation observation nontrivial half depth ordinal t,
    Root.seed_value observation nontrivial half depth ordinal,
    Flow.originalSource_actual t, map_smul]
  rfl

noncomputable def quarterValue (t : ℝ) : BurnolQuarterIntervalL2 :=
  burnolQuarterRestriction (result observation nontrivial half depth ordinal t).2.2.1

theorem original_quarter_value (t : ℝ) : quarterValue observation nontrivial half depth ordinal t = Flow.originalSource t := by
  rw [quarterValue, original_full_value observation nontrivial half depth ordinal t,
    burnolQuarterRestriction_zeroExtension]

theorem paid (t : ℝ) : (result observation nontrivial half depth ordinal t).2.1.2.length = 5 :=
  Installed.source_history auth (reader observation nontrivial half depth ordinal t) point

theorem quarter_hasDerivAt : HasDerivAt (quarterValue observation nontrivial half depth ordinal)
    Flow.originalVelocity 0 :=
  Flow.originalSource_hasDerivAt.congr_of_eventuallyEq
    (Filter.Eventually.of_forall (original_quarter_value observation nontrivial half depth ordinal))

theorem mean_hasDerivAt : HasDerivAt
    (fun t => burnolQuarterMeanCoefficient (quarterValue observation nontrivial half depth ordinal t))
      (burnolQuarterMeanCoefficient Flow.originalVelocity) 0 :=
  Flow.original_mean_hasDerivAt.congr_of_eventuallyEq (Filter.Eventually.of_forall
    (fun t => congrArg burnolQuarterMeanCoefficient (original_quarter_value observation nontrivial half depth ordinal t)))

theorem eta_hasDerivAt : HasDerivAt
    (fun t => OriginalRieszSource.Constructor.zeroMean
      (quarterValue observation nontrivial half depth ordinal t)) OriginalRieszSource.Response.eta 0 :=
  Flow.original_centered_hasDerivAt.congr_of_eventuallyEq (Filter.Eventually.of_forall
    (fun t => congrArg OriginalRieszSource.Constructor.zeroMean
      (original_quarter_value observation nontrivial half depth ordinal t)))

theorem u_hasDerivAt : HasDerivAt
    (fun t => burnolMeanZeroBlockInverse (OriginalRieszSource.Constructor.zeroMean
      (quarterValue observation nontrivial half depth ordinal t))) OriginalRieszSource.Response.u 0 :=
  Flow.original_u_hasDerivAt.congr_of_eventuallyEq (Filter.Eventually.of_forall
    (fun t => congrArg (fun value => burnolMeanZeroBlockInverse (OriginalRieszSource.Constructor.zeroMean value))
      (original_quarter_value observation nontrivial half depth ordinal t)))

theorem v_hasDerivAt : HasDerivAt
    (fun t => burnolMeanZeroTruncatedFourier (burnolMeanZeroBlockInverse (OriginalRieszSource.Constructor.zeroMean
      (quarterValue observation nontrivial half depth ordinal t)))) OriginalRieszSource.Response.v 0 :=
  Flow.original_v_hasDerivAt.congr_of_eventuallyEq (Filter.Eventually.of_forall
    (fun t => congrArg (fun value => burnolMeanZeroTruncatedFourier
      (burnolMeanZeroBlockInverse (OriginalRieszSource.Constructor.zeroMean value)))
      (original_quarter_value observation nontrivial half depth ordinal t)))

end OriginalConstantFourierNativeSource
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot

run_cmd Lean.modifyEnv fun env =>
  Lean.LibrarySuggestions.nameDenyListExt.addEntry env "OriginalConstantFourierNativeSource"
