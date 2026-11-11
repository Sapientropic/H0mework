import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCofinalFullBranchFibre.KernelWrite.NativeDelta.BetaDecoder.Word.Reentry.Action.Pa.Block.TotalSource.Trace
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceInventoryExecutionFeed.SourceWordNative.Reentry.FullRAction.Pa.Block.TotalSource.ActualTrace
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift SourceInventoryExecutionFeed
open MeasureTheory NoIslandNoMagic.CanonicalRiemann NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual BurnolPhysicalState
attribute [local instance] baseGroups originGroups runtimeGroups codeGroups valueGroups valueAddZeroClass valueAddZero nextGroups nextAddZeroClass nextAddZero

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n:Nat,observation.coordinate=-2*(n+1))
variable (half : NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCombCalculation.Half observation)
variable (initial : Nat)
variable (raw : RootGeneratedDebtActivationJointSource.OwnerFree.Raw
 (Value := PairValue (PairValue (Code.F.BaseValue initial))) (Var := Code.F.C.Var) (sort := ()))

variable (environment : Env (Value initial) Code.F.C.Var) (total : Value initial ())
variable (actual : Trace environment (compiled initial raw (Code.sourceCode observation nontrivial half)) (.const total))

def sourcePoint := Two.totalBranches
 (physicalRead initial (inputReceipt observation nontrivial half initial raw environment total actual).value)

theorem source_point_environment :
 sourcePoint observation nontrivial half initial raw environment total actual =
 Two.totalBranches ((inputEnvironment initial raw environment) () ()) :=
 congrArg Two.totalBranches (input_receipt_read observation nontrivial half initial raw environment total actual)

def shellDirections := Two.directions
 (physicalRead initial (actualShell observation nontrivial half initial raw environment total actual).value)

theorem shell_directions :
 shellDirections observation nontrivial half initial raw environment total actual =
 (Two.translatedShell observation nontrivial half Two.sourceShift
    (sourcePoint observation nontrivial half initial raw environment total actual),
  Two.translatedShell observation nontrivial half (-Two.sourceShift)
    (sourcePoint observation nontrivial half initial raw environment total actual)) := by
 unfold shellDirections
 rw [actual_shell_read,Two.shell_ast_value,source_point_environment]
 change
  (Two.translatedShell observation nontrivial half Two.sourceShift
    (((inputEnvironment initial raw environment) () ()).1.1+((inputEnvironment initial raw environment) () ()).1.2)+
   Two.translatedShell observation nontrivial half Two.sourceShift
    (((inputEnvironment initial raw environment) () ()).2.1+((inputEnvironment initial raw environment) () ()).2.2),
   Two.translatedShell observation nontrivial half (-Two.sourceShift)
    (((inputEnvironment initial raw environment) () ()).1.1+((inputEnvironment initial raw environment) () ()).1.2)+
   Two.translatedShell observation nontrivial half (-Two.sourceShift)
    (((inputEnvironment initial raw environment) () ()).2.1+((inputEnvironment initial raw environment) () ()).2.2)) = _
 rw [←map_add,←map_add]
 rfl

theorem signed_shells :
 let c := Two.coordinate observation nontrivial half
 let x := sourcePoint observation nontrivial half initial raw environment total actual
 shellDirections observation nontrivial half initial raw environment total actual =
 ((Two.coefficient c x * fullMellinTranslationCharacter c.value Two.sourceShift) •
   Two.signedUnitResponse c (4*Real.exp (-Two.sourceShift)),
  (Two.coefficient c x * fullMellinTranslationCharacter c.value (-Two.sourceShift)) •
   Two.signedUnitResponse c (4*Real.exp (-(-Two.sourceShift)))) := by
 intro c x
 rw [shell_directions]
 apply Prod.ext
 · change Two.coefficient c x • Two.unitAction c Two.sourceShift = _
   rw [Two.unit_action_signed_shell c Two.sourceShift Two.positive_source_radius_bound,smul_smul]
 · change Two.coefficient c x • Two.unitAction c (-Two.sourceShift) = _
   rw [Two.unit_action_signed_shell c (-Two.sourceShift) Two.negative_source_radius_bound,smul_smul]

private theorem scaled_signed_realizes (coordinate : BurnolCompletedMellinCoordinate)
 (radius : ℝ) (positive : 0<radius) (bounded : radius⁻¹≤4) (coefficient : ℂ)
 (test : SchwartzMap ℝ ℂ) :
 burnolRemainderSourceRead (coefficient • Two.signedUnitSource coordinate radius positive) test =
 (Lp.toTemperedDistributionCLM ℂ volume 2 (coefficient • Two.signedUnitResponse coordinate radius)) test := by
 have paid := Two.signed_unit_realizes coordinate radius positive bounded test
 rw [←burnolRemainderSourceReadCLM_apply,map_smul,map_smul]
 change coefficient * burnolRemainderSourceReadCLM test (Two.signedUnitSource coordinate radius positive) =
  coefficient * (Lp.toTemperedDistributionCLM ℂ volume 2 (Two.signedUnitResponse coordinate radius)) test
 rw [burnolRemainderSourceReadCLM_apply]
 exact congrArg (fun value : ℂ => coefficient*value) paid

/-- Each source coefficient is read from this history's actual input subtrace. -/
def shellSources : BurnolL2 × BurnolL2 :=
 let c := Two.coordinate observation nontrivial half
 let x := sourcePoint observation nontrivial half initial raw environment total actual
 ((Two.coefficient c x * fullMellinTranslationCharacter c.value Two.sourceShift) •
   Two.signedUnitSource c (4*Real.exp (-Two.sourceShift)) (by positivity),
  (Two.coefficient c x * fullMellinTranslationCharacter c.value (-Two.sourceShift)) •
   Two.signedUnitSource c (4*Real.exp (-(-Two.sourceShift))) (by positivity))

theorem shell_sources_realize (test : SchwartzMap ℝ ℂ) :
 burnolRemainderSourceRead (shellSources observation nontrivial half initial raw environment total actual).1 test =
  (Lp.toTemperedDistributionCLM ℂ volume 2
   (shellDirections observation nontrivial half initial raw environment total actual).1) test ∧
 burnolRemainderSourceRead (shellSources observation nontrivial half initial raw environment total actual).2 test =
  (Lp.toTemperedDistributionCLM ℂ volume 2
   (shellDirections observation nontrivial half initial raw environment total actual).2) test := by
 let c := Two.coordinate observation nontrivial half
 let x := sourcePoint observation nontrivial half initial raw environment total actual
 have actual := signed_shells observation nontrivial half initial raw environment total actual
 constructor
 · exact (scaled_signed_realizes c (4*Real.exp (-Two.sourceShift)) (by positivity)
    Two.positive_source_radius_bound
    (Two.coefficient c x * fullMellinTranslationCharacter c.value Two.sourceShift) test).trans
    (congrArg (fun value : BurnolL2 => (Lp.toTemperedDistributionCLM ℂ volume 2 value) test)
     (congrArg Prod.fst actual).symm)
 · exact (scaled_signed_realizes c (4*Real.exp (-(-Two.sourceShift))) (by positivity)
    Two.negative_source_radius_bound
    (Two.coefficient c x * fullMellinTranslationCharacter c.value (-Two.sourceShift)) test).trans
    (congrArg (fun value : BurnolL2 => (Lp.toTemperedDistributionCLM ℂ volume 2 value) test)
     (congrArg Prod.snd actual).symm)

namespace Origin
export SourceInventoryExecutionFeed.SourceWordNative.Reentry.FullRAction.Pa.Block.TotalSource.Origin
 (sourceRaw sourceUpdated sourceEnvironment origin source_raw_read)
end Origin
namespace A
export SourceOperationInquiry.Context.Faces.Execution.Activation (Programme)
namespace M
export SourceOperationInquiry.Context.Faces.Execution.Activation.M (Frame)
end M
end A
namespace R
export SourceGeneratedInquiryReceiptAction (actualMaterial)
end R
namespace Born
export SourceInventoryExecutionFeed.SourceWordNative.Reentry.FullRAction.Pa.Block.TotalSource.Born (oldPaid)
end Born
namespace SN
export SourceInventoryExecutionFeed.SourceWordNative (afterEnvironment)
end SN

section Material
variable (frame : A.M.Frame (Value := PairValue (Code.F.BaseValue initial)) (Var := Code.F.C.Var) (sort := ()))
variable (base : A.Programme (PhysicalValue := PairValue (Code.F.BaseValue initial)) (PhysicalVar := Code.F.C.Var) (sort := ()))
variable (before : Inventory (V := Code.F.BaseValue initial) (X := Code.F.C.Var) (s := ()))
variable (oldEnvironment : Env (Code.F.BaseValue initial) Code.F.C.Var)
variable (admissions : List (AdmissionReceipt.Admission before (ActualNativeRelationTransport.AS.stockScalar frame base)))
variable (sourceFrame : A.M.Frame (Value := PairValue (PairValue (Code.F.BaseValue initial))) (Var := Code.F.C.Var) (sort := ()))
variable (receiver : A.M.Frame (Value := Born.FC.Value initial) (Var := Code.F.C.Var) (sort := ()))

local notation "cfg" => Born.programme initial frame base before oldEnvironment admissions observation nontrivial half sourceFrame
local notation "maternal" => Origin.sourceRaw initial frame base before oldEnvironment admissions
def materialEnvironment : Env (Value initial) Code.F.C.Var := (R.actualMaterial receiver cfg).environment
local notation "env" => materialEnvironment observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame receiver
local notation "paid" => Born.oldPaid initial frame base before oldEnvironment admissions observation nontrivial half sourceFrame receiver
local notation "rho" => Born.actualTrace initial frame base before oldEnvironment admissions observation nontrivial half sourceFrame receiver

def materialShell := actualShell observation nontrivial half initial maternal env paid rho

def materialInput := inputReceipt observation nontrivial half initial maternal env paid rho

def materialSourcePoint := sourcePoint observation nontrivial half initial maternal env paid rho

def materialShellDirections := shellDirections observation nontrivial half initial maternal env paid rho

theorem material_signed_shells : type_of% (signed_shells observation nontrivial half initial maternal env paid rho) :=
 signed_shells observation nontrivial half initial maternal env paid rho

theorem material_unit_positions : type_of% (repeated_unit_positions observation nontrivial half initial maternal env paid rho) :=
 repeated_unit_positions observation nontrivial half initial maternal env paid rho

def materialShellSources := shellSources observation nontrivial half initial maternal env paid rho

theorem material_shell_sources_realize (test : SchwartzMap ℝ ℂ) :
 type_of% (shell_sources_realize observation nontrivial half initial maternal env paid rho test) :=
 shell_sources_realize observation nontrivial half initial maternal env paid rho test

private theorem input_environment_body
 (raw : RootGeneratedDebtActivationJointSource.OwnerFree.Raw
  (Value := PairValue (PairValue (Code.F.BaseValue initial))) (Var := Code.F.C.Var) (sort := ()))
 (middle : Env (Code.Operand.CodeValue initial) Code.F.C.Var) :
 inputEnvironment initial raw (pairEnvironment (pairEnvironment (pairEnvironment middle 0) 0) 0) () () =
 Code.DR.completeRSourceRead initial 2 0 ((Code.Operand.bodyAt initial raw).eval middle) := by
 change Code.CF.collapseValue initial (Code.CF.collapseValue 2 _) =
  Code.DR.sourceCollapseHom initial (Code.DR.sourceCollapseHom 2 _)
 rw [Code.DR.source_collapse_actual,Code.DR.source_collapse_actual]
 rfl

private theorem maternal_body :
 (Code.Operand.bodyAt initial maternal).eval
  (Origin.sourceEnvironment initial frame base before oldEnvironment admissions) =
 (((Origin.origin initial frame base before oldEnvironment admissions).native.raw.eval
   (SN.afterEnvironment frame base),0),0) :=
 (Code.body_updated initial maternal (Origin.sourceUpdated initial frame base before oldEnvironment admissions)).trans
  (congrArg (fun value => (value,0))
   (Origin.source_raw_read initial frame base before oldEnvironment admissions))

theorem material_actual_source_input :
 materialSourcePoint observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame receiver =
 Two.totalBranches (Code.DR.completeRSourceRead initial 2 0
  (((Origin.origin initial frame base before oldEnvironment admissions).native.raw.eval
    (SN.afterEnvironment frame base),0),0)) := by
 apply (source_point_environment observation nontrivial half initial maternal env paid rho).trans
 apply congrArg Two.totalBranches
 have sourceEnv : env=Born.codeEnvironment initial frame base before oldEnvironment admissions :=
  Born.material_environment initial frame base before oldEnvironment admissions observation nontrivial half sourceFrame receiver
 exact (congrArg (fun source : Env (Value initial) Code.F.C.Var => inputEnvironment initial maternal source () ()) sourceEnv).trans
  ((input_environment_body initial maternal
   (Origin.sourceEnvironment initial frame base before oldEnvironment admissions)).trans
   (congrArg (Code.DR.completeRSourceRead initial 2 0)
    (maternal_body initial frame base before oldEnvironment admissions)))

local notation "f" => Born.actualCurrent initial frame base before oldEnvironment admissions observation nontrivial half sourceFrame

/-- The same actual FullR receiver supplies every trace; no second executor appears. -/
def actualShellReceipt := materialShell observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame f

def actualSourcePoint := materialSourcePoint observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame f

theorem actual_signed_shells : type_of% (material_signed_shells observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame f) :=
 material_signed_shells observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame f

theorem actual_unit_positions : type_of% (material_unit_positions observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame f) :=
 material_unit_positions observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame f

def actualShellSources := materialShellSources observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame f

theorem actual_shell_sources_realize (test : SchwartzMap ℝ ℂ) :
 type_of% (material_shell_sources_realize observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame f test) :=
 material_shell_sources_realize observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame f test

theorem actual_source_input : type_of% (material_actual_source_input observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame f) :=
 material_actual_source_input observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame f
end Material

end SourceInventoryExecutionFeed.SourceWordNative.Reentry.FullRAction.Pa.Block.TotalSource.ActualTrace
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
