import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKConstantFourierPrice.Material

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1200000
set_option pp.deepTerms.threshold 24
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalConstantFourierPriceSource
open RootInquiryCompletion BurnolPhysicalState SourceOperationEffects SourceOperationExecution
namespace Root
export OriginalConstantFourierPriceOrigin
  (sourceRoot sourceVisit source_frame_root source_frame_visit originFace seedValue seedTrace seed_actual seed_trace_source)
end Root
namespace Material
export OriginalConstantFourierPriceMaterial
  (bValue sbValue b_actual sb_actual columnTrace column_trace_source column_child_address)
end Material
namespace P
export OriginalConstantFourierPriceProgram
  (code sourceEnvironment programme_equation original_price originalB originalSB priceLift driveCode correctionCode
   sumCode rowCode coefficientACode coefficientBetaCode familyCode seedCode velocityCode etaCode uCode vCode)
end P
namespace M
export OriginalConstantFourierPriceMath (seed scalarRead scalarLift scalar_lift inverse wave)
end M
namespace Prog
export OriginalKPaNativePortSourceCalculation (Value Var E)
end Prog
namespace O
export RootGeneratedDebtActivationJointSource.OwnerFree (Raw)
end O
namespace Installed
export RootGeneratedDebtActivationJointSource.OwnerFree.Installation (ResultAt resultAt source_history source_value)
end Installed
open private result_expression from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKPairedWaveActionSource
open private mp_heq from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKOutsideCorrectionRSource

open private linear linearMap scale from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Material.Calculation.ClozelOriginalKConstantFourierPriceProgram

private theorem row_budget (c:BurnolCompletedMellinCoordinate) (b sb:BurnolL2) (channel:Fin 6) (side:Fin 2) :
    remaining (P.rowCode c b sb channel side)=2*remaining (P.familyCode channel)+13 := by
  dsimp only [P.rowCode,P.coefficientACode,P.coefficientBetaCode,linear,linearMap,scale,P.seedCode,remaining]
  omega
private theorem family_budget (channel:Fin 6) : remaining (P.familyCode channel)=![4,5,5,6,3,1] channel := by
  fin_cases channel <;> rfl
theorem code_budget (c:BurnolCompletedMellinCoordinate) (b sb:BurnolL2) : remaining (P.code c b sb)=269 := by
  simp only [P.code,P.correctionCode,P.driveCode,linear,scale,remaining,P.sumCode,row_budget,family_budget]
  decide

namespace Traced
variable (c:BurnolCompletedMellinCoordinate) (b sb:BurnolL2)
variable {environment:Env Prog.Value Prog.Var} {total:BurnolL2}
variable (actual:Trace environment (P.code c b sb) (.const total))
noncomputable def priceInput := originalInput actual
noncomputable def inverseInput := originalInput (priceInput c b sb actual).2.1
noncomputable def driveSplit := Trace.splitAdd (inverseInput c b sb actual).2.1
noncomputable def negativeInput := originalInput (driveSplit c b sb actual).rightTrace
noncomputable def waveInput := originalInput (negativeInput c b sb actual).2.1
noncomputable def firstDrive := (waveInput c b sb actual).1
noncomputable def secondDrive := (driveSplit c b sb actual).leftValue
noncomputable def firstTrace := (waveInput c b sb actual).2.1
noncomputable def secondTrace := (driveSplit c b sb actual).leftTrace
theorem first_equation : firstDrive c b sb actual=(P.driveCode c b sb 0).eval environment :=
  (firstTrace c b sb actual).sound.symm
theorem second_equation : secondDrive c b sb actual=(P.driveCode c b sb 1).eval environment :=
  (secondTrace c b sb actual).sound.symm
theorem inverse_equation : (priceInput c b sb actual).1=M.inverse ((inverseInput c b sb actual).1) :=
  (inverseInput c b sb actual).2.2.down.symm
theorem price_equation : total=P.priceLift c ((priceInput c b sb actual).1) :=
  (priceInput c b sb actual).2.2.down.symm
theorem full_input_equation : (inverseInput c b sb actual).1=
    secondDrive c b sb actual + (-1:ℂ) • M.wave (firstDrive c b sb actual) :=
  (driveSplit c b sb actual).total_eq.trans
    (congrArg (fun right => secondDrive c b sb actual + right)
      ((negativeInput c b sb actual).2.2.down.symm.trans
        (congrArg (fun value => (-1:ℂ) • value) (waveInput c b sb actual).2.2.down.symm)))
end Traced

private abbrev Read {W:WorldRelationNetwork} {V:Vocabulary}
    (old:SourceNativeAuthoritativeRootClosure W V) :=
  {now:V.Current} → old.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt now →
    O.Raw (Value:=Prog.Value) (Var:=Prog.Var) (sort:=())

namespace Generated
variable {W:WorldRelationNetwork} {V:Vocabulary}
variable (old:SourceNativeAuthoritativeRootClosure W V) (stage:V.Current)
variable (c:BurnolCompletedMellinCoordinate) (seed b sb:BurnolL2)
noncomputable def environment : Env Prog.Value Prog.Var := fun _ _ => seed
noncomputable def reader : Read old := fun {_} _ => ⟨environment seed,P.code c b sb⟩
noncomputable def result : Installed.ResultAt old (reader old c seed b sb) (old.emitted stage) :=
  Installed.resultAt old (reader old c seed b sb) (old.emitted stage)
private theorem expression : type_of% (result_expression old (reader old c seed b sb) (old.emitted stage)) :=
  result_expression old (reader old c seed b sb) (old.emitted stage)
noncomputable def trace : Trace (environment seed) (P.code c b sb) (.const ((result old stage c seed b sb).2.2.1)) :=
  Eq.mp (congrArg (Trace (environment seed) (P.code c b sb)) (expression old stage c seed b sb))
    (result old stage c seed b sb).2.1.2
theorem trace_source : type_of% (mp_heq
    (congrArg (Trace (environment seed) (P.code c b sb)) (expression old stage c seed b sb))
      (result old stage c seed b sb).2.1.2) := mp_heq _ _
theorem equation : (result old stage c seed b sb).2.2.1=(P.code c b sb).eval (environment seed) :=
  Installed.source_value old (reader old c seed b sb) (old.emitted stage)
theorem programme_equation : type_of% ((equation old stage c seed b sb).trans
    (P.programme_equation c b sb (environment seed))) :=
  (equation old stage c seed b sb).trans (P.programme_equation c b sb (environment seed))
theorem paid : (result old stage c seed b sb).2.1.2.length=269 :=
  (Installed.source_history old (reader old c seed b sb) (old.emitted stage)).trans (code_budget c b sb)

noncomputable def priceInput := Traced.priceInput c b sb (trace old stage c seed b sb)
noncomputable def inverseInput := Traced.inverseInput c b sb (trace old stage c seed b sb)
noncomputable def firstDrive := Traced.firstDrive c b sb (trace old stage c seed b sb)
noncomputable def secondDrive := Traced.secondDrive c b sb (trace old stage c seed b sb)
noncomputable def firstTrace := Traced.firstTrace c b sb (trace old stage c seed b sb)
noncomputable def secondTrace := Traced.secondTrace c b sb (trace old stage c seed b sb)
theorem first_equation : type_of% (Traced.first_equation c b sb (trace old stage c seed b sb)) :=
  Traced.first_equation c b sb (trace old stage c seed b sb)
theorem second_equation : type_of% (Traced.second_equation c b sb (trace old stage c seed b sb)) :=
  Traced.second_equation c b sb (trace old stage c seed b sb)
theorem inverse_equation : type_of% (Traced.inverse_equation c b sb (trace old stage c seed b sb)) :=
  Traced.inverse_equation c b sb (trace old stage c seed b sb)
theorem price_equation : type_of% (Traced.price_equation c b sb (trace old stage c seed b sb)) :=
  Traced.price_equation c b sb (trace old stage c seed b sb)
theorem full_input_equation : type_of% (Traced.full_input_equation c b sb (trace old stage c seed b sb)) :=
  Traced.full_input_equation c b sb (trace old stage c seed b sb)
end Generated

variable (observation:GeneratedRiemannZeroObservation)
variable (nontrivial:¬ ∃ n:Nat, observation.coordinate = -2*(n+1))
variable (half:OriginalKCombCalculation.Half observation) (depth ordinal:Nat) (t:ℝ)
local notation "c" => OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half
noncomputable def sourceRoot := Root.sourceRoot observation nontrivial half depth ordinal t
noncomputable def sourceVisit := Root.sourceVisit observation nontrivial half depth ordinal t
private abbrev auth := (sourceRoot observation nontrivial half depth ordinal t).toAuthoritativeRoot
private abbrev current := (sourceVisit observation nontrivial half depth ordinal t).current
local notation "old" => auth observation nontrivial half depth ordinal t
local notation "now0" => current observation nontrivial half depth ordinal t
noncomputable def seedValue := Root.seedValue observation nontrivial half depth ordinal t
noncomputable def bValue := Material.bValue observation nontrivial half depth ordinal t
noncomputable def sbValue := Material.sbValue observation nontrivial half depth ordinal t
local notation "actualSeed" => seedValue observation nontrivial half depth ordinal t
local notation "actualB" => bValue observation nontrivial half depth ordinal t
local notation "actualSB" => sbValue observation nontrivial half depth ordinal t

noncomputable def inputSeedTrace := Root.seedTrace observation nontrivial half depth ordinal t
noncomputable def inputBTrace := Material.columnTrace observation nontrivial half depth ordinal t 0
noncomputable def inputSBTrace := Material.columnTrace observation nontrivial half depth ordinal t 1
theorem input_seed_source : type_of% (Root.seed_trace_source observation nontrivial half depth ordinal t) :=
  Root.seed_trace_source observation nontrivial half depth ordinal t
theorem input_B_source : type_of% (Material.column_trace_source observation nontrivial half depth ordinal t 0) :=
  Material.column_trace_source observation nontrivial half depth ordinal t 0
theorem input_SB_source : type_of% (Material.column_trace_source observation nontrivial half depth ordinal t 1) :=
  Material.column_trace_source observation nontrivial half depth ordinal t 1
theorem source_frame_root : type_of% (Root.source_frame_root observation nontrivial half depth ordinal t) :=
  Root.source_frame_root observation nontrivial half depth ordinal t
theorem source_frame_visit : type_of% (Root.source_frame_visit observation nontrivial half depth ordinal t) :=
  Root.source_frame_visit observation nontrivial half depth ordinal t

noncomputable def environment := Generated.environment actualSeed
noncomputable def reader : Read old := Generated.reader old c actualSeed actualB actualSB
noncomputable def result := Generated.result old now0 c actualSeed actualB actualSB
noncomputable def trace := Generated.trace old now0 c actualSeed actualB actualSB
noncomputable def priceInput := Generated.priceInput old now0 c actualSeed actualB actualSB
noncomputable def inverseInput := Generated.inverseInput old now0 c actualSeed actualB actualSB
noncomputable def firstDrive := Generated.firstDrive old now0 c actualSeed actualB actualSB
noncomputable def secondDrive := Generated.secondDrive old now0 c actualSeed actualB actualSB
noncomputable def firstTrace := Generated.firstTrace old now0 c actualSeed actualB actualSB
noncomputable def secondTrace := Generated.secondTrace old now0 c actualSeed actualB actualSB

theorem trace_source : type_of% (Generated.trace_source old now0 c actualSeed actualB actualSB) :=
  Generated.trace_source old now0 c actualSeed actualB actualSB
theorem equation : type_of% (Generated.programme_equation old now0 c actualSeed actualB actualSB) :=
  Generated.programme_equation old now0 c actualSeed actualB actualSB
theorem paid : type_of% (Generated.paid old now0 c actualSeed actualB actualSB) :=
  Generated.paid old now0 c actualSeed actualB actualSB
theorem first_equation : type_of% (Generated.first_equation old now0 c actualSeed actualB actualSB) :=
  Generated.first_equation old now0 c actualSeed actualB actualSB
theorem second_equation : type_of% (Generated.second_equation old now0 c actualSeed actualB actualSB) :=
  Generated.second_equation old now0 c actualSeed actualB actualSB
theorem inverse_equation : type_of% (Generated.inverse_equation old now0 c actualSeed actualB actualSB) :=
  Generated.inverse_equation old now0 c actualSeed actualB actualSB
theorem price_equation : type_of% (Generated.price_equation old now0 c actualSeed actualB actualSB) :=
  Generated.price_equation old now0 c actualSeed actualB actualSB
theorem full_input_equation : type_of% (Generated.full_input_equation old now0 c actualSeed actualB actualSB) :=
  Generated.full_input_equation old now0 c actualSeed actualB actualSB

private theorem environment_actual : Generated.environment actualSeed=P.sourceEnvironment :=
  congrArg Generated.environment (Root.seed_actual observation nontrivial half depth ordinal t)
theorem actual_output : (result observation nontrivial half depth ordinal t).2.2.1=
    M.scalarLift (OriginalWholeDebtRJointMobiusContactClosureSource.finitePrice c c) :=
  (Generated.equation old now0 c actualSeed actualB actualSB).trans
    ((congrArg (fun environment => (P.code c actualB actualSB).eval environment)
      (environment_actual observation nontrivial half depth ordinal t)).trans
      ((congrArg₂ (fun left right => (P.code c left right).eval P.sourceEnvironment)
        (Material.b_actual observation nontrivial half depth ordinal t)
        (Material.sb_actual observation nontrivial half depth ordinal t)).trans (P.original_price c)))
noncomputable def actualPrice : ℂ := M.scalarRead (result observation nontrivial half depth ordinal t).2.2.1
theorem actual_price : actualPrice observation nontrivial half depth ordinal t=
    OriginalWholeDebtRJointMobiusContactClosureSource.finitePrice c c :=
  (congrArg M.scalarRead (actual_output observation nontrivial half depth ordinal t)).trans (M.scalar_lift _)

end OriginalConstantFourierPriceSource
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end

run_cmd Lean.modifyEnv fun env =>
  Lean.LibrarySuggestions.nameDenyListExt.addEntry env "OriginalConstantFourierPriceSource"
