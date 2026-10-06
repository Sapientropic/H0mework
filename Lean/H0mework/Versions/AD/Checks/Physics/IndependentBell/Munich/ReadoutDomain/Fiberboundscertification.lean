import H0mework.Physics.Bell.ReadoutFiberBounds
import H0mework.Versions.AD.Physics.Bell.ReadoutIdentification
import Lean.Util.FoldConsts

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.Bell.FiberBoundsCertification

open ProofFreeRicherAnholonomicSource StageNineHolonomicField Stage9C.Revision
open ReadoutIdentification ReadoutFiberBounds

noncomputable section

def localEffect (family : SettingFamily) (side setting : Bool) : CompactReadoutEffect :=
  if side then family.bob setting else family.alice setting

def Strict (family : SettingFamily) : Prop :=
  ∀ side setting, 0 < (localEffect family side setting).u ^ 2 ∧
    0 < (localEffect family side setting).z ^ 2

theorem effectCapacity (effect : CompactReadoutEffect) :
    effect.u ^ 2 + effect.z ^ 2 ≤ (1 - |effect.mu|) ^ 2 := by
  by_cases positive : 0 ≤ effect.mu
  · simpa only [abs_of_nonneg positive] using effect.norm_minus
  · simpa only [abs_of_nonpos (le_of_not_ge positive), sub_neg_eq_add] using effect.norm_plus

def sourceSystem (family : SettingFamily) (side : Bool) (strict : Strict family) : PositiveConeSystem where
  a := fun i => (localEffect family side i).u ^ 2
  b := fun i => (localEffect family side i).z ^ 2
  c := fun i => (1 - |(localEffect family side i).mu|) ^ 2
  p := fun j => (localEffect family (!side) j).u ^ 2
  q := fun j => (localEffect family (!side) j).z ^ 2
  d := fun j => (1 - |(localEffect family (!side) j).mu|) ^ 2
  a_positive := fun i => (strict side i).1
  b_positive := fun i => (strict side i).2
  c_positive := fun i => by
    have cap := effectCapacity (localEffect family side i)
    linarith only [cap, (strict side i).1, (strict side i).2]
  p_positive := fun j => (strict (!side) j).1
  q_positive := fun j => (strict (!side) j).2
  d_positive := fun j => by
    have cap := effectCapacity (localEffect family (!side) j)
    linarith only [cap, (strict (!side) j).1, (strict (!side) j).2]

def coordinate (side : Bool) (scale : ℝ) : ℝ := if side then 1 / scale ^ 2 else scale ^ 2

theorem scaledFeasible (family : SettingFamily) (side : Bool) (strict : Strict family)
    (s t : ℝ) (valid : AdmissibleScales family s t) :
    Feasible (sourceSystem family side strict) (coordinate side s) (coordinate side t) := by
  cases side
  · refine ⟨?_, ?_, ?_, ?_⟩
    · exact sq_pos_of_ne_zero valid.s_nonzero
    · exact sq_pos_of_ne_zero valid.t_nonzero
    · intro i
      simpa [sourceSystem, localEffect, coordinate, scaledFamily, mul_pow, mul_comm] using
        effectCapacity ((scaledFamily family s t valid).alice i)
    · intro j
      simpa [sourceSystem, localEffect, coordinate, scaledFamily, div_pow] using
        effectCapacity ((scaledFamily family s t valid).bob j)
  · refine ⟨?_, ?_, ?_, ?_⟩
    · exact one_div_pos.mpr (sq_pos_of_ne_zero valid.s_nonzero)
    · exact one_div_pos.mpr (sq_pos_of_ne_zero valid.t_nonzero)
    · intro i
      simpa [sourceSystem, localEffect, coordinate, scaledFamily, div_eq_mul_inv, mul_pow, inv_pow] using
        effectCapacity ((scaledFamily family s t valid).bob i)
    · intro j
      simpa [sourceSystem, localEffect, coordinate, scaledFamily, mul_pow, div_div, mul_comm] using
        effectCapacity ((scaledFamily family s t valid).alice j)

theorem scaledGainObjective (family : SettingFamily) (side setting : Bool) (strict : Strict family)
    (s t : ℝ) (valid : AdmissibleScales family s t) :
    (sourceSystem family side strict).a setting * coordinate side s +
      (sourceSystem family side strict).b setting * coordinate side t =
        (localEffect (scaledFamily family s t valid) side setting).gain ^ 2 := by
  rw [CompactReadoutEffect.gain_sq]
  cases side <;>
    simp [sourceSystem, localEffect, coordinate, scaledFamily, mul_pow, div_eq_mul_inv, inv_pow, mul_comm]

/-- This consumer couples the generic bound to the original legal source scale family. -/
theorem sourceScaledUniformBound (family : SettingFamily) (side setting : Bool) (strict : Strict family)
    (sigma rS rT : ℝ) (theta lambda : Bool → ℝ)
    (theta_nonnegative : ∀ i, 0 ≤ theta i) (lambda_nonnegative : ∀ j, 0 ≤ lambda j)
    (C_nonnegative : 0 ≤ dualC (sourceSystem family side strict)
      ((sourceSystem family side strict).a setting) sigma theta)
    (D_nonnegative : 0 ≤ dualD (sourceSystem family side strict)
      ((sourceSystem family side strict).b setting) sigma theta)
    (rS_nonnegative : 0 ≤ rS) (rT_nonnegative : 0 ≤ rT)
    (rS_square : rS ^ 2 ≤ dualC (sourceSystem family side strict)
      ((sourceSystem family side strict).a setting) sigma theta * dualP (sourceSystem family side strict) lambda)
    (rT_square : rT ^ 2 ≤ dualD (sourceSystem family side strict)
      ((sourceSystem family side strict).b setting) sigma theta * dualQ (sourceSystem family side strict) lambda)
    (s t : ℝ) (valid : AdmissibleScales family s t) :
    2 * (rS + rT) - dualK (sourceSystem family side strict) theta lambda ≤
      sigma * (localEffect (scaledFamily family s t valid) side setting).gain ^ 2 := by
  have bound := dual_certificate_bound (sourceSystem family side strict)
    ((sourceSystem family side strict).a setting) ((sourceSystem family side strict).b setting)
    sigma (coordinate side s) (coordinate side t) rS rT theta lambda theta_nonnegative lambda_nonnegative
    C_nonnegative D_nonnegative rS_nonnegative rT_nonnegative rS_square rT_square
    (scaledFeasible family side strict s t valid)
  rw [scaledGainObjective family side setting strict s t valid] at bound
  exact bound

theorem completeFirstScale (system : PositiveConeSystem) (S : ℝ) :
    (∃ T, Feasible system S T) ↔ Projected system S := feasible_iff_projected system S

theorem generatedSecondScale (system : PositiveConeSystem) (S : ℝ) (projected : Projected system S) :
    Feasible system S (system.selectedT S) := projected_generates_feasible system S projected

theorem completeOriginalRegularFiber (original other : SettingFamily) (regular : Regular original) :
    SameLaw other original ↔ Nonempty (RegularFiber original other) :=
  sameOccurrenceIdentification.completeRegularFiber original other regular

theorem originalSourceCurrentNext (family : SettingFamily) (s t : ℝ)
    (valid : AdmissibleScales family s t) (point : BasePoint) (plus a b x y : Bool) :
    (scaledFamily family s t valid).sourceProbability point plus a b x y = family.sourceProbability point plus a b x y ∧
    (scaledFamily family s t valid).currentProbability point plus a b x y = family.currentProbability point plus a b x y ∧
    (scaledFamily family s t valid).nextProbability point plus a b x y = family.nextProbability point plus a b x y :=
  ⟨sameOccurrenceIdentification.scaleSource family s t valid point plus a b x y,
    sameOccurrenceIdentification.scaleCurrent family s t valid point plus a b x y,
    sameOccurrenceIdentification.scaleNext family s t valid point plus a b x y⟩

end
end SaturationMonoid.PhysicsCore.Stage10.Bell.FiberBoundsCertification

open Lean Elab Command in
set_option maxHeartbeats 0 in
run_cmd do
  let env := (← getEnv).setExporting false
  let paidText ← match (← IO.getEnv "BELL_FIBER_PAID_NAMES") with
    | some paidPath => IO.FS.readFile paidPath
    | none => pure "[]"
  let paidJson ← ofExcept (Json.parse paidText)
  let paidArray ← ofExcept paidJson.getArr?
  let mut paid : NameSet := {}
  for entry in paidArray do
    let spelling ← ofExcept entry.getStr?
    paid := paid.insert spelling.toName
  let candidates : Array Name := #[`H0mework.Physics.Bell.ReadoutFiberBounds]
  let ownerOf := fun name : Name =>
    match env.getModuleIdxFor? name with
    | some index => env.allImportedModuleNames[index.toNat]!
    | none => env.mainModule
  let mut own : Array Name := #[]
  let mut compilerOnly : Array Name := #[]
  for module in candidates do
    let some candidateIndex := env.getModuleIdx? module | throwError "candidate module absent: {module}"
    for (name, moduleIndex) in env.const2ModIdx.toList do
      if moduleIndex == candidateIndex then
        if (env.find? name).isSome then own := own.push name
        else compilerOnly := compilerOnly.push name
  let consumerPrefix := `SaturationMonoid.PhysicsCore.Stage10.Bell.FiberBoundsCertification
  let consumers := env.constants.toList.toArray.filterMap fun (name, _) =>
    if consumerPrefix.isPrefixOf name then some name else none
  if own.isEmpty || consumers.isEmpty then throwError "empty candidate or independent consumer"
  let mut pending := own ++ consumers
  let mut index := 0
  let mut seen : NameSet := {}
  for name in pending do seen := seen.insert name
  let mut closure : Array Json := #[]
  let mut boundaries : Array Json := #[]
  while index < pending.size do
    let name := pending[index]!
    index := index + 1
    let some info := env.find? name | throwError "missing dependency: {name}"
    let kind := match info with
      | .axiomInfo _ => "axiom"
      | .defnInfo value => if value.safety == .safe then "definition" else "unsafe-definition"
      | .thmInfo _ => "theorem"
      | .opaqueInfo _ => "opaque"
      | .quotInfo _ => "quotient"
      | .inductInfo _ => "inductive"
      | .ctorInfo _ => "constructor"
      | .recInfo _ => "recursor"
    let dependencies := info.getUsedConstantsAsSet.toList.toArray
    let entry := Json.mkObj [("name", .str name.toString),
      ("module", .str (ownerOf name).toString), ("kind", .str kind),
      ("dependencies", .arr (dependencies.map fun dependency => .str dependency.toString))]
    if paid.contains name then boundaries := boundaries.push entry
    else
      closure := closure.push entry
      for dependency in dependencies do
        if !seen.contains dependency then
          seen := seen.insert dependency
          pending := pending.push dependency
  let publicNames : Array Name := #[
    `SaturationMonoid.PhysicsCore.Stage10.Bell.ReadoutFiberBounds.reciprocal_amgm,
    `SaturationMonoid.PhysicsCore.Stage10.Bell.ReadoutFiberBounds.projected_generates_feasible,
    `SaturationMonoid.PhysicsCore.Stage10.Bell.ReadoutFiberBounds.feasible_iff_projected,
    `SaturationMonoid.PhysicsCore.Stage10.Bell.ReadoutFiberBounds.dual_certificate_bound,
    `SaturationMonoid.PhysicsCore.Stage10.Bell.FiberBoundsCertification.sourceScaledUniformBound]
  let mut mouths : Array Json := #[]
  for name in publicNames do
    let some info := env.find? name | throwError "missing public mouth: {name}"
    let pretty ← liftTermElabM <| Meta.ppExpr info.type
    mouths := mouths.push (Json.mkObj [("name", .str name.toString), ("type", .str pretty.pretty)])
  let report := Json.mkObj [
    ("candidate_modules", .arr (candidates.map fun name => .str name.toString)),
    ("imported_modules", .arr (env.allImportedModuleNames.map fun name => .str name.toString)),
    ("owned_declarations", .arr (own.map fun name => .str name.toString)),
    ("compiler_only_module_symbols", .arr (compilerOnly.map fun name => .str name.toString)),
    ("independent_consumers", .arr (consumers.map fun name => .str name.toString)),
    ("dependency_delta", .arr closure), ("paid_boundary", .arr boundaries),
    ("public_mouths", .arr mouths)]
  logInfo m!"BELL_FIBER_KERNEL_AUDIT|{report.compress}"
