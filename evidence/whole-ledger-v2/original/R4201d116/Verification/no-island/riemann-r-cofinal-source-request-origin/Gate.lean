import SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCountedPaSource.Initial.BornRNativeGammaInstall.NextReceiptSourceOrigin
import «002-gate.source»
import Lean

set_option autoImplicit false
set_option Elab.async false
set_option maxErrors 1

run_cmd Lean.modifyEnv fun env =>
 Lean.LibrarySuggestions.nameDenyListExt.addEntry env "CofinalSourceRequestOriginCertificate"

namespace CofinalSourceRequestOriginCertificate
open Lean

private def prefixName : String :=
 "SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState.CountedPaInitial."

private structure Binder where
 name : Name
 domain : Expr
 info : BinderInfo
 deriving Inhabited

private def telescope (type : Expr) : Array Binder × Expr := Id.run do
 let mut binders : Array Binder := #[]
 let mut body := type
 while let .forallE name domain next info := body do
  binders := binders.push {name := name, domain := domain, info := info}
  body := next
 return (binders,body)

private def require (ok : Bool) (why : String) : IO Unit :=
 unless ok do throw (IO.userError why)

private def lookup (env : Environment) (name : String) : IO ConstantInfo :=
 match env.find? name.toName with
 | some ci => pure ci
 | none => throw (IO.userError s!"MISSING_CANONICAL_BINDING {name}")

private def instantiate (ci : ConstantInfo) (arguments : Std.HashMap Name Expr)
    (universes : Std.HashMap Name Level) (suffix : Array String) :
    IO (Expr × Expr × Array String) := do
 let levels ← ci.levelParams.mapM fun n =>
  match universes[n]? with
  | some level => pure level
  | none => throw (IO.userError s!"UNMAPPED_CANONICAL_UNIVERSE {ci.name}: {n}")
 let mut value := Expr.const ci.name levels
 let mut target := ci.type.instantiateLevelParams ci.levelParams levels
 let mut binders : Array String := #[]
 while let .forallE name _ body _ := target do
  let some argument := arguments[name]? | break
  value := .app value argument
  target := body.instantiate1 argument
  binders := binders.push name.toString
 require (binders == #["observation","nontrivial","half","depth","ordinal",
  "Parent","Index","Whole","Next","HistoryEnd","History","update","cutoff","method"])
  s!"CANONICAL_GENERIC_BINDER_DRIFT {ci.name}: {binders}"
 let (remaining,_) := telescope target
 require (remaining.map (·.name.toString) == suffix)
  s!"CANONICAL_INDEX_BINDER_DRIFT {ci.name}: {remaining.map (·.name.toString)}"
 return (target,value,binders ++ suffix)

private def write (path : String) (json : Json) : IO Unit :=
 IO.FS.writeFile path (json.pretty ++ "\n")

-- Reuse the raw canonical application from CP505. One literal method is applied to
-- every conclusion, then the conjunction is checked by the kernel without Meta.
private def sameCanonicalMethod (env : Environment) (report current : String) : IO Unit := do
 require (env.header.trustLevel == 0) "CANONICAL_CONTEXT_TRUST_NONZERO"
 let canonical ← lookup env (prefixName ++ "BornRSourcePrice.actual_source_price_method")
 let receipt ← lookup env (prefixName ++ "BornRSourcePrice.SourcePriceMethodReceipt")
 let (binders,result) := telescope canonical.type
 let binderNames := binders.map (·.name.toString)
 require (binderNames == #["observation","nontrivial","half","depth","ordinal","update","N"])
   s!"CANONICAL_BINDER_DRIFT {binderNames}"
 let .const receiptName receiptLevels := result.getAppFn
  | throw (IO.userError "CANONICAL_RESULT_NOT_NOMINAL")
 require (receiptName == receipt.name) "WRONG_NOMINAL_PRICE_RECEIPT"
 let receiptArgs := result.getAppArgs
 let (receiptBinders,_) := telescope receipt.type
 require (receiptArgs.size == receiptBinders.size && receiptArgs.size == 13 &&
          receiptLevels.length == receipt.levelParams.length && receiptLevels.length == 6)
  "CANONICAL_RECEIPT_ARITY_DRIFT"
 let mut arguments : Std.HashMap Name Expr := {}
 for i in [:receiptBinders.size] do
  arguments := arguments.insert receiptBinders[i]!.name receiptArgs[i]!
 let canonicalArgs := (Array.range binders.size).map fun i => Expr.bvar (binders.size-1-i)
 for i in [:binders.size] do
  let name := binders[i]!.name
  arguments := arguments.insert name canonicalArgs[i]!
  if name == `N then arguments := arguments.insert `cutoff canonicalArgs[i]!
 let method := mkAppN (.const canonical.name (canonical.levelParams.map Level.param)) canonicalArgs
 arguments := arguments.insert `method method
 let mut universes : Std.HashMap Name Level := {}
 for (name,level) in receipt.levelParams.zip receiptLevels do
  universes := universes.insert name level
 let f := prefixName ++ "BornRNativeGammaInstall.PhysicalGammaBoundaryFeedback."
 let claims : Array (String × Array String) := #[
   (prefixName ++ "CofinalSourceRequestOriginCertificate.original_source_request_at_literal_next",
    #["requestIndex","stepIndex"]),
   (f ++ "actual_physical_gamma_boundary_feedback", #[])]
 let applications ← claims.mapM fun (name,suffix) => do
  let ci ← lookup env name
  instantiate ci arguments universes suffix
 let mut target := applications.back!.1
 let mut value := applications.back!.2.1
 for (prop,proof,_) in applications.pop.reverse do
  value := mkAppN (.const ``And.intro []) #[prop,target,proof,value]
  target := mkAppN (.const ``And []) #[prop,target]
 for binder in binders.reverse do
  value := .lam binder.name binder.domain value binder.info
  target := .forallE binder.name binder.domain target binder.info
 let name := `CofinalSourceRequestOriginCertificate.direct_same_canonical_method
 require ((env.find? name).isNone) "CANONICAL_CONTROL_ALREADY_INSTALLED"
 let declaration : Declaration := .thmDecl {
  name := name, levelParams := canonical.levelParams, type := target, value := value, all := [name] }
 let started ← IO.monoMsNow
 write current <| Json.mkObj [("phase",toJson "kernel-start"),("CI",toJson name.toString),
  ("monotonic_ms",toJson started)]
 IO.eprintln "CP530_CANONICAL_KERNEL_START"
 match env.toKernelEnv.addDeclCore 0 0 declaration (cancelTk? := none) with
 | .error error =>
  write current <| Json.mkObj [("phase",toJson "kernel-error"),("CI",toJson name.toString),
   ("elapsed_ms",toJson ((← IO.monoMsNow)-started))]
  throw (IO.userError (← error.toMessageData {} |>.toString))
 | .ok checked =>
  let elapsed := (← IO.monoMsNow)-started
  let some actual := checked.find? name | throw (IO.userError "CANONICAL_CHECKED_CI_MISSING")
  require (actual.type == target && actual.value? (allowOpaque := true) == some value &&
    actual.levelParams == canonical.levelParams) "CANONICAL_CI_CHANGED"
  write current <| Json.mkObj [("phase",toJson "kernel-done"),("CI",toJson name.toString),
   ("elapsed_ms",toJson elapsed)]
  write report <| Json.mkObj [("schema",toJson "cp530-canonical-shared-method-application/v1"),
   ("accepted",toJson true),("CI",toJson name.toString),("canonical",toJson canonical.name.toString),
   ("conjoined_claims",toJson (claims.map (·.1))),("canonical_binders",toJson binderNames),
   ("receipt_argument_binders",toJson (receiptBinders.map (·.name.toString))),
   ("receipt_universe_params",toJson (receipt.levelParams.map Name.toString)),
   ("canonical_universe_params",toJson (canonical.levelParams.map Name.toString)),
   ("application_binders",toJson (applications.map (·.2.2))),
   ("same_literal_method_expr_hash",toJson ((hash method).toNat)),
   ("type_expr_hash",toJson ((hash target).toNat)),("value_expr_hash",toJson ((hash value).toNat)),
   ("value_dependencies",toJson (value.getUsedConstants.map Name.toString)),
   ("canonical_kernel_ms",toJson elapsed),("Meta_calls",toJson (0:Nat)),
   ("new_proof_premises",toJson (0:Nat)),("kernel_add_decl_calls",toJson (1:Nat))]
  IO.eprintln s!"CP530_CANONICAL_KERNEL_PASS {elapsed}ms"

end CofinalSourceRequestOriginCertificate


noncomputable section
universe uParent uIndex uWhole uNext uHistoryEnd uHistory

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace CountedPaInitial.CofinalSourceRequestOriginCertificate

open SourceOperationEffects SourceOperationExecution SourceOperationScalarRelations
open CofinalHistorySettlement CenteredGram.IntegralGraphJointAction
open BornRNativeGammaInstall.PhysicalGammaNextReceiptPosition
open private selectedActualInput PositionIn.position PositionIn.word PositionIn.lower PositionIn.upper PositionIn.actual from «002-gate.source»

local notation "slot" => CompletedSourceRCalculation.Slot.branches
local instance originGateGroups (grade : Nat) : ∀ t, AddCommGroup (Cfa.Value A.W grade t) :=
  Cfa.groups A.W grade

private theorem no_extra_slot {read forward : Nat} (same : read = forward) :
    read ≠ forward + 1 := by omega

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2*(n+1))
variable (half : OriginalKCombCalculation.Half observation) (depth ordinal : Nat)
variable {Parent : Sort uParent} {Index : Sort uIndex} {Whole : Sort uWhole}
variable {Next : Sort uNext} {HistoryEnd : Sort uHistoryEnd} {History : Sort uHistory}
variable {update cutoff : Nat}
variable (method : BornRSourcePrice.SourcePriceMethodReceipt (Parent := Parent) (Index := Index)
  (Whole := Whole) (Next := Next) (HistoryEnd := HistoryEnd) (History := History)
  observation nontrivial half depth ordinal update cutoff)

local notation "factory" => A.fixedRFactory observation nontrivial half
local notation "initial" => H.receiver observation nontrivial half depth ordinal
local notation "programme" => H.methodProgramme observation nontrivial half depth ordinal
local notation "site" => Cfa.packetAt factory initial programme rfl
local notation "current" => site (update+2)
local notation "birth" => N.actualBirth observation nontrivial half depth ordinal method
local notation "requests" => B.requests factory current birth
local notation "selected" => Cfa.selected factory current
set_option quotPrecheck false in
local notation "base" => (Cfa.nativePacket factory current).2.2.1
local notation "decoder" => Cfa.stockDecodedEnvironment selected base

run_cmd IO.eprintln "CP530_CONTROL + original_source_request_at_literal_next"
set_option cleanup.letToHave false in
set_option backward.isDefEq.respectTransparency false in
theorem original_source_request_at_literal_next (requestIndex : Fin (requests).length)
    (stepIndex : Fin (P.words (F.receipt decoder ((requests).get requestIndex))).length) :
    let input := selectedActualInput observation nontrivial half depth ordinal method requestIndex stepIndex
    let found := actualPosition observation nontrivial half depth ordinal method
      (PositionIn.position input) (PositionIn.word input) (PositionIn.lower input)
      (PositionIn.upper input) (PositionIn.actual input)
    let origin := actualSourceRequest observation nontrivial half depth ordinal method
      (PositionIn.position input) (PositionIn.word input) (PositionIn.lower input)
      (PositionIn.upper input) (PositionIn.actual input)
    let forward := R.atBirth factory current (birth).stock (birth).installed
      ((birth).step origin.origin.sourceIndex) origin.origin.supportIndex
    let consumed := actual_position_consumption observation nontrivial half depth ordinal method
      (PositionIn.position input) (PositionIn.word input) (PositionIn.lower input)
      (PositionIn.upper input) (PositionIn.actual input)
    found.nativeExecution.request = forward.request ∧
    found.nativeExecution.segment.before.length = forward.segment.before.length ∧
    found.nativeExecution.segment.before.length ≠ forward.segment.before.length + 1 ∧
    (type_of% (origin.origin.prefix_eq)) ∧ (type_of% (origin.action_eq)) ∧ (type_of% consumed) := by
  let input := selectedActualInput observation nontrivial half depth ordinal method requestIndex stepIndex
  let origin := actualSourceRequest observation nontrivial half depth ordinal method
    (PositionIn.position input) (PositionIn.word input) (PositionIn.lower input)
      (PositionIn.upper input) (PositionIn.actual input)
  let consumed := actual_position_consumption observation nontrivial half depth ordinal method
    (PositionIn.position input) (PositionIn.word input) (PositionIn.lower input)
      (PositionIn.upper input) (PositionIn.actual input)
  exact ⟨origin.request_eq, origin.address_eq, no_extra_slot origin.address_eq,
    origin.origin.prefix_eq, origin.action_eq, consumed⟩

end CountedPaInitial.CofinalSourceRequestOriginCertificate
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end

open Lean Elab Command in
run_cmd do
 let some report ← liftIO <| IO.getEnv "CP530_CANONICAL_REPORT"
  | throwError "set CP530_CANONICAL_REPORT for the same canonical method check"
 let some current ← liftIO <| IO.getEnv "CP530_CANONICAL_CURRENT"
  | throwError "set CP530_CANONICAL_CURRENT for the canonical kernel marker"
 let env ← getEnv
 liftIO <| CofinalSourceRequestOriginCertificate.sameCanonicalMethod env report current
