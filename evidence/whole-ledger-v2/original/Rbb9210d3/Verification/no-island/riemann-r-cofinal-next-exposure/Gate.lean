import SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCountedPaSource.Initial.BornRNativeGammaInstall.NextReceipt
import Lean

set_option autoImplicit false
set_option Elab.async false
set_option maxErrors 1

run_cmd Lean.modifyEnv fun env =>
 Lean.LibrarySuggestions.nameDenyListExt.addEntry env "CofinalNextExposureCertificate"

namespace CofinalNextExposureCertificate
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
 let r := prefixName ++ "BornRNativeGammaInstall.PhysicalGammaNextReceipt."
 let claims : Array (String × Array String) := #[
   (r ++ "actualStep_literal", #["index"]),
   (r ++ "actualNextReceipt_position", #["index","item"]),
   (r ++ "actualNextReceipt_segment_position", #["index","item"]),
   (r ++ "actual_next_receipt_completion", #["index","item"]),
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
 let name := `CofinalNextExposureCertificate.direct_same_canonical_method
 require ((env.find? name).isNone) "CANONICAL_CONTROL_ALREADY_INSTALLED"
 let declaration : Declaration := .thmDecl {
  name := name, levelParams := canonical.levelParams, type := target, value := value, all := [name] }
 let started ← IO.monoMsNow
 write current <| Json.mkObj [("phase",toJson "kernel-start"),("CI",toJson name.toString),
  ("monotonic_ms",toJson started)]
 IO.eprintln "CP514_CANONICAL_KERNEL_START"
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
  write report <| Json.mkObj [("schema",toJson "cp514-canonical-shared-method-application/v1"),
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
  IO.eprintln s!"CP514_CANONICAL_KERNEL_PASS {elapsed}ms"

end CofinalNextExposureCertificate


noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace CofinalNextExposureCertificate

open SourceOperationEffects SourceOperationExecution CofinalHistorySettlement

namespace Feed
export SourceInventoryExecutionFeed (Inventory Request requests receipt executionBranches)
export SourceInventoryExecutionFeed.ReceiptOccurrence (fromSplit fromSplit_before_length)
end Feed
namespace P
export SourceOperationPaidRelations (events exposure events_trace words complete_steps)
end P

private abbrev DuplicateValue : Unit → Type := fun _ => ℤ
private abbrev DuplicateVariable : Unit → Type := fun _ => Unit
private def duplicateEnvironment : Env DuplicateValue DuplicateVariable := fun _ _ => 0
private def duplicateExpression : Expr DuplicateValue DuplicateVariable () :=
  .add (.const 2) (.const 3)
private def duplicateInventory : Feed.Inventory (V := DuplicateValue) (X := DuplicateVariable) (s := ()) :=
  .occur (.generator duplicateExpression) (.cons (.zero (.generator duplicateExpression)) .nil)
private def firstRequest : Feed.Request (V := DuplicateValue) (X := DuplicateVariable) (s := ()) :=
  ⟨0, .generator duplicateExpression, duplicateExpression, 1⟩
private def secondRequest : Feed.Request (V := DuplicateValue) (X := DuplicateVariable) (s := ()) :=
  ⟨1, .generator duplicateExpression, duplicateExpression, 1⟩
private theorem first_split :
    Feed.requests duplicateInventory = [] ++ firstRequest :: [secondRequest] := rfl
private theorem second_split :
    Feed.requests duplicateInventory = [firstRequest] ++ secondRequest :: [] := rfl

private def firstExposure :=
  Feed.fromSplit duplicateEnvironment duplicateInventory [] [secondRequest] firstRequest first_split
private def secondExposure :=
  Feed.fromSplit duplicateEnvironment duplicateInventory [firstRequest] [] secondRequest second_split

private theorem first_offset : firstExposure.before.length = 2 :=
  (Feed.fromSplit_before_length duplicateEnvironment duplicateInventory [] [secondRequest]
    firstRequest first_split).trans (by rfl)

private theorem second_offset : secondExposure.before.length = 4 :=
  (Feed.fromSplit_before_length duplicateEnvironment duplicateInventory [firstRequest] []
    secondRequest second_split).trans (by rfl)

run_cmd IO.eprintln "CP514_CONTROL duplicate_generators_keep_requests_and_full_exposures"
theorem duplicate_generators_keep_requests_and_full_exposures :
    Feed.requests duplicateInventory = [firstRequest, secondRequest] ∧
    firstRequest.expression = secondRequest.expression ∧
    firstRequest.expression.eval duplicateEnvironment = 5 ∧
    secondRequest.expression.eval duplicateEnvironment = 5 ∧
    firstRequest.position = 0 ∧ secondRequest.position = 1 ∧
    firstExposure.before.length = 2 ∧ secondExposure.before.length = 4 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, first_offset, second_offset⟩

run_cmd IO.eprintln "CP514_CONTROL counter_same_content_cannot_select_second_offset"
theorem counter_same_content_cannot_select_second_offset :
    firstRequest.position ≠ secondRequest.position ∧
    firstExposure.before.length ≠ secondExposure.before.length := by
  constructor
  · change (0 : Nat) ≠ 1
    decide
  · rw [first_offset, second_offset]
    decide

namespace A
export ActualCofinalSourceAction (packetTransport)
export ActualCofinalSourceAction.AS (AdmissionPacket)
export ActualCofinalSourceAction.SF (Factory)
export ActualCofinalSourceAction.L (Value groups)
export ActualCofinalSourceAction.D (packetAt packetAt_successor_grade)
end A
namespace R
export ActualCofinalSourceAction.SourceReceiptOccurrence (ExecutionAt)
export ActualCofinalSourceAction.SourceReceiptOccurrence.ExecutionAt (reindex reindex_positions)
end R

variable {Sorts : Type u} {W X : Sorts → Type u} [∀ target, AddCommGroup (W target)] {s : Sorts}
local instance levelGroups (grade : Nat) (target : Sorts) :
    AddCommGroup (A.Value W grade target) := A.groups W grade target

section Cofinal
variable (factory : A.Factory W X s)
variable (initial : ActualCofinalSourceAction.A.M.Frame (Value := W) (Var := X) (sort := s))
variable (configuration : ActualCofinalSourceAction.A.Programme (PhysicalValue := W) (PhysicalVar := X) (sort := s))
variable (language : configuration.LowVar = X)
local notation "site" => A.packetAt factory initial configuration language

run_cmd IO.eprintln "CP514_CONTROL counter_current_packet_cannot_be_literal_next"
theorem counter_current_packet_cannot_be_literal_next (ordinal : Nat) :
    site ordinal ≠ site (ordinal+1) := by
  intro same
  have grades := congrArg (fun packet : A.AdmissionPacket (W := W) (X := X) (s := s) => packet.1) same
  rw [A.packetAt_successor_grade factory initial configuration language ordinal] at grades
  exact (Nat.ne_of_lt (Nat.lt_succ_self _)) grades

end Cofinal

run_cmd IO.eprintln "CP514_CONTROL reindexed_receiver_has_entire_paid_exposure"
theorem reindexed_receiver_has_entire_paid_exposure {Y Z : Sorts → Type u}
    (source : A.AdmissionPacket (W := W) (X := Y) (s := s))
    (target : A.AdmissionPacket (W := W) (X := Z) (s := s))
    (language : Y = Z) (recognition : A.packetTransport language source = target)
    (execution : R.ExecutionAt source) :
    let output := R.reindex source target language recognition execution
    target.2.1.1.inventory = some output.stock ∧
      target.2.1.1.activeEnvironment = output.decoder ∧
      output.stock.trace = output.segment.before ++ (P.exposure output.paid).trace ++ output.segment.after ∧
      output.request.position = execution.request.position ∧
      output.segment.before.length = execution.segment.before.length := by
  let output := R.reindex source target language recognition execution
  exact ⟨output.installed, output.decoder_source, output.segment.trace_eq,
    R.reindex_positions source target language recognition execution⟩

end CofinalNextExposureCertificate
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end

open Lean Elab Command in
run_cmd do
 let some report ← liftIO <| IO.getEnv "CP514_CANONICAL_REPORT"
  | throwError "set CP514_CANONICAL_REPORT for the same canonical method check"
 let some current ← liftIO <| IO.getEnv "CP514_CANONICAL_CURRENT"
  | throwError "set CP514_CANONICAL_CURRENT for the canonical kernel marker"
 let env ← getEnv
 liftIO <| CofinalNextExposureCertificate.sameCanonicalMethod env report current
