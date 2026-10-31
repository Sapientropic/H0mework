import SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.Completion.Complete
import SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.Consumers.Complete
import SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.Recognition.Family
import SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.Recognition.Installed
import SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.Recognition.Submission
import SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.Recognition.WholeLedger
import Lean.Elab.Command
open Lean Elab Command

elab "#priority_public_inventory" : command => do
  let env ← getEnv
  let owned := #[`SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.Completion.Complete,`SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.Consumers.Complete,`SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.Recognition.Family,`SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.Recognition.Installed,`SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.Recognition.Submission,`SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.Recognition.WholeLedger]
  let names := env.constants.toList.filterMap fun (name, info) =>
    if (((env.getModuleIdxFor? name).map fun i => env.header.moduleNames[i.toNat]!).any owned.contains) &&
        !info.isUnsafe && !info.isPartial && (privateToUserName? name).isNone then some name.toString else none
  liftIO <| IO.FS.writeFile "runtime/audit-tmp/iqa-capital-final-recognition-independent-v1/fresh-public-names.txt" (String.intercalate "\n" (names.mergeSort (· ≤ ·)))
#priority_public_inventory
