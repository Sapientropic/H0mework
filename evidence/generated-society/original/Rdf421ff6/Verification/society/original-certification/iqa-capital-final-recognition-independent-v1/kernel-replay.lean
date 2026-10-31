import SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.Completion.Complete
import SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.Consumers.Complete
import SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.Recognition.Family
import SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.Recognition.Installed
import SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.Recognition.Submission
import SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.Recognition.WholeLedger

import Lean.Replay
import Lean.Elab.Command
import Lean.Util.FoldConsts
open Lean Elab Command
set_option maxRecDepth 100000

private partial def collect (env : Environment) (pending : List Name) (seen : NameSet := {}) : NameSet :=
  match pending with
  | [] => seen
  | name :: rest =>
    if seen.contains name then collect env rest seen
    else match env.find? name with
      | none => collect env rest (seen.insert name)
      | some info => collect env (info.getUsedConstantsAsSet.toList ++ rest) (seen.insert name)

elab "#check_final_recognition_kernel" : command => do
  let env ← getEnv
  let owned := #[`SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.Completion.Complete,
    `SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.Consumers.Complete,
    `SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.Recognition.Family,
    `SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.Recognition.Installed,
    `SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.Recognition.Submission,
    `SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.Recognition.WholeLedger,
    `SaturationMonoid.NoIslandNoMagic.Authority.InverseReconstruction.SourceGeneratedTemporalVisit]
  let ownedEntries := env.constants.toList.filter fun (name, _) =>
    ((env.getModuleIdxFor? name).map fun i => env.header.moduleNames[i.toNat]!).any owned.contains
  let roots := ownedEntries.filterMap fun (name, info) =>
    if !info.isUnsafe && !info.isPartial then some name else none
  let excluded := ownedEntries.filterMap fun (name, info) =>
    if info.isUnsafe || info.isPartial then some name else none
  liftIO <| IO.FS.writeFile "runtime/audit-tmp/iqa-capital-final-recognition-independent-v1/excluded-ir.txt" (String.intercalate "\n" (excluded.map Name.toString))
  if roots.isEmpty then throwError "empty FinalRecognition audit"
  let closure := collect env roots
  let mut inventory : Std.HashMap Name ConstantInfo := {}
  let mut axioms : Array Name := #[]
  let mut privateCount := 0
  for name in closure do
    let some info := env.find? name | throwError "missing dependency {name}"
    if info.isUnsafe || info.isPartial then throwError "unsafe or partial logical dependency {name}"
    inventory := inventory.insert name info
    if (privateToUserName? name).isSome then privateCount := privateCount + 1
    if info matches .axiomInfo _ then axioms := axioms.push name
  for axiomName in axioms do
    unless #[`propext, `Classical.choice, `Quot.sound].contains axiomName do
      throwError "unauthorized axiom {axiomName}"
  liftIO <| IO.FS.writeFile "runtime/audit-tmp/iqa-capital-final-recognition-independent-v1/kernel-inventory.txt" (String.intercalate "\n" ((inventory.toList.map fun (name, _) => name.toString).mergeSort (· ≤ ·)))
  logInfo m!"KERNEL REPLAY START: roots={roots.length}, closure={inventory.size}, private={privateCount}, excludedIR={excluded.length}, axioms={axioms}"
  let fresh ← liftIO (mkEmptyEnvironment 0)
  let _ ← liftIO (Environment.replay inventory fresh)
  logInfo m!"KERNEL REPLAY PASS: roots={roots.length}, closure={inventory.size}, private={privateCount}, excludedIR={excluded.length}, axioms={axioms}"

#check_final_recognition_kernel
