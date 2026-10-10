import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockResponse.SourceActualThreeParticleCutoffFamilyDifference
import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockResponse.SourceActualThreeParticleCutoffSharp
import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockResponse.SourceActualFourBlockSharpCausalMass
import Lean
set_option autoImplicit false
open Lean Elab Command
run_cmd do
  let env ← getEnv
  for (text, owner) in [("LowEnergy.FullYDynamicSourceNext.oriented_causal_limit", "H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceFullYUncutRetardedKernel"), ("LowEnergy.FullYDynamicSourceNext.causal_apply", "H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceFullYUncutRetardedKernel"), ("LowEnergy.FullYDynamicSourceNext.time_negative", "H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceFullYUncutRetardedKernel"), ("LowEnergy.FourGradeOutputParseval.baseline_time_square_integrable", "H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceFullYPositiveOutputParseval"), ("LowEnergy.FourGradeOutputParseval.baseline_frequency_square_integrable", "H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceFullYPositiveOutputParseval"), ("LowEnergy.FourGradeOutputParseval.baseline_square_mass", "H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceFullYPositiveOutputParseval"), ("LowEnergy.FourGradeOutputParseval.positive_output_parseval", "H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceFullYPositiveOutputParseval"), ("LowEnergy.FourGradeOutputParseval.square_pair_integrable", "H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceFullYPositiveOutputParseval"), ("LowEnergy.FourGradeOutputParseval.one_sided_positive_parseval", "H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceFullYPositiveOutputParseval"), ("LowEnergy.ActualFourBlockSharpCausalMass.polynomial_wave_square_integrable", "H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockResponse.SourceActualFourBlockSharpCausalMass")] do
    let wanted := text.toName
    let candidates := env.constants.toList.filter fun (name,_) => privateToUserName name == wanted && name.toString.startsWith ("_private." ++ owner ++ ".")
    unless candidates.length == 1 do throwError "Expected unique original payer {wanted} / {owner}"
    let (name,info) := candidates[0]!
    let some index := env.getModuleIdxFor? name | throwError "No module {name}"
    unless env.header.moduleNames[index]!.toString == owner do throwError "Wrong owner {name}"
    unless (info.value? true).isSome do throwError "Missing checked value {name}"
    logInfo m!"OWNER {wanted} = {name} MODULE {env.header.moduleNames[index]!}"
    logInfo m!"TYPE {name} = {info.type}"
