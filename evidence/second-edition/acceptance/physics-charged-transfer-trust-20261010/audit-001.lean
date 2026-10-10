import H0mework.Papers.SecondEditionPhysicsChargedTransfer
import Lean

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 0
open Lean Elab Command
private def releaseName (value : String) : Name :=
  (value.splitOn ".").foldl Name.str .anonymous

private def completeRefs (info : ConstantInfo) : NameSet := Id.run do
  let mut refs := info.type.getUsedConstantsAsSet ++ info.getUsedConstantsAsSet
  if let some value := info.value? true then refs := refs ++ value.getUsedConstantsAsSet
  match info with
  | .defnInfo val => for name in val.all do refs := refs.insert name
  | .thmInfo val => for name in val.all do refs := refs.insert name
  | .opaqueInfo val => for name in val.all do refs := refs.insert name
  | .inductInfo val =>
      for name in val.all ++ val.ctors do refs := refs.insert name
  | .ctorInfo val => refs := refs.insert val.induct
  | .recInfo val =>
      for name in val.all do refs := refs.insert name
      for rule in val.rules do
        refs := refs.insert rule.ctor
        refs := refs ++ rule.rhs.getUsedConstantsAsSet
  | _ => pure ()
  return refs

private partial def recoveryClosure (env : Environment) (pending : List Name)
    (seen : NameSet := {}) : NameSet :=
  match pending with
  | [] => seen
  | name :: rest =>
      if seen.contains name then recoveryClosure env rest seen
      else
        let children := match env.checked.get.find? name with
          | some info => (completeRefs info).toArray.toList
          | none => []
        recoveryClosure env (children ++ rest) (seen.insert name)

run_cmd do
  let env ← getEnv
  let roots : List (String × String) := [("LowEnergy.ActualFourBlockElastic.actual_imaginary_canonical_bra_value", "H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceActualFourBlockElasticNonzero"),
    ("LowEnergy.ActualFourBlockElastic.actual_imaginary_coherent_bra_value", "H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceActualFourBlockElasticNonzero"),
    ("LowEnergy.ActualFourBlockElastic.actual_imaginary_coherent_candidate_nonzero", "H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceActualFourBlockElasticNonzero"),
    ("LowEnergy.ActualFourBlockHilbertOperator.actual_causal_return", "H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceActualFourBlockHilbertOperator"),
    ("LowEnergy.ActualFourBlockHilbertOperator.actual_operator_bound", "H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceActualFourBlockHilbertOperator"),
    ("LowEnergy.ActualFourBlockHilbertOperator.actual_operator_core", "H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceActualFourBlockHilbertOperator"),
    ("LowEnergy.ActualFourBlockHilbertOperator.actual_output_difference_bound", "H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceActualFourBlockHilbertOperator"),
    ("LowEnergy.ActualFourBlockHilbertOperator.actual_output_difference_integral_bound", "H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceActualFourBlockHilbertOperator"),
    ("LowEnergy.ActualFourBlockHilbertOperator.actual_output_return", "H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceActualFourBlockHilbertOperator"),
    ("LowEnergy.ActualFourBlockHilbertOperator.operator", "H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceActualFourBlockHilbertOperator"),
    ("LowEnergy.ActualFourBlockProfileFamily.actual_generated_source_profile_family", "H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceActualFourBlockProfileFamily"),
    ("LowEnergy.ActualFourBlockRealTransfer.DenominatorIndex", "H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceActualFourBlockRealTransferDenominators"),
    ("LowEnergy.ActualFourBlockRealTransfer.actual_amplitude_analytic_I", "H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceActualFourBlockRealTransferAmplitude"),
    ("LowEnergy.ActualFourBlockRealTransfer.actual_amplitude_meromorphic", "H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceActualFourBlockRealTransferAmplitude"),
    ("LowEnergy.ActualFourBlockRealTransfer.actual_canonical_numerator_analytic", "H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceActualFourBlockRealTransferCanonicalNumerator"),
    ("LowEnergy.ActualFourBlockRealTransfer.actual_denominator_analytic", "H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceActualFourBlockRealTransferDenominators"),
    ("LowEnergy.ActualFourBlockRealTransfer.actual_denominator_imaginary_nonzero", "H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceActualFourBlockRealTransferDenominators"),
    ("LowEnergy.ActualFourBlockRealTransfer.actual_denominators_regular", "H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceActualFourBlockRealTransferDenominators"),
    ("LowEnergy.ActualFourBlockRealTransfer.actual_real_transfer_source_window", "H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceActualFourBlockRealTransferWindow"),
    ("LowEnergy.ActualFourBlockRealTransfer.punctured_real_regular_of_imaginary_witness", "H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceActualFourBlockRealTransferRegular"),
    ("LowEnergy.ActualFourBlockRealTransfer.sourceDenominator", "H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceActualFourBlockRealTransferDenominators"),
    ("LowEnergy.ActualFourBlockRealTransferPositive.actual_generated_source_real_transfer_positive", "H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceActualFourBlockRealTransferPositive"),
    ("LowEnergy.ActualFourBlockRetarded.actual_causal_integrable", "H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceActualFourBlockRetarded"),
    ("LowEnergy.ActualFourBlockRetarded.actual_causal_readout", "H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceActualFourBlockRetarded"),
    ("LowEnergy.ActualFourBlockRetarded.actual_cofinal_four_block_moment_measure", "H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceActualFourBlockRetarded"),
    ("LowEnergy.ActualFourBlockRetarded.actual_coherent_gram", "H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceActualFourBlockRetarded"),
    ("LowEnergy.ActualFourBlockRetarded.actual_coherent_output", "H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceActualFourBlockRetarded"),
    ("LowEnergy.ActualFourBlockRetarded.actual_density_integrable", "H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceActualFourBlockRetarded"),
    ("LowEnergy.ActualFourBlockRetarded.actual_gram_integrable", "H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceActualFourBlockRetarded"),
    ("LowEnergy.ActualFourBlockRetarded.actual_output_fourier", "H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceActualFourBlockRetarded"),
    ("LowEnergy.ActualFourBlockRetarded.actual_spectrum_bands", "H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceActualFourBlockRetarded"),
    ("LowEnergy.ActualFourBlockRetarded.blockOutput", "H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceActualFourBlockRetarded"),
    ("LowEnergy.ActualFourBlockRetarded.causalOutput", "H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceActualFourBlockRetarded"),
    ("LowEnergy.ActualFourBlockRetarded.density", "H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceActualFourBlockRetarded"),
    ("LowEnergy.ActualFourBlockRetarded.frequencyScale", "H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceActualFourBlockRetarded"),
    ("LowEnergy.ActualFourBlockRetarded.output", "H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceActualFourBlockRetarded"),
    ("LowEnergy.ActualFourBlockRetarded.spectrum", "H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceActualFourBlockRetarded"),
    ("LowEnergy.ActualFourBlockSharpCausalMass.actual_absolute_output_mass", "H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceActualFourBlockSharpCausalMass"),
    ("LowEnergy.ActualFourBlockSharpCausalMass.actual_causal_spectrum_mass", "H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceActualFourBlockSharpCausalMass"),
    ("LowEnergy.ActualFourBlockSharpCausalMass.actual_output_fourier_mass_return", "H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceActualFourBlockSharpCausalMass"),
    ("LowEnergy.ActualFourBlockSharpCausalMass.actual_output_positive_mass", "H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceActualFourBlockSharpCausalMass"),
    ("LowEnergy.ActualFourBlockSharpCausalMass.actual_source_output_parseval", "H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceActualFourBlockSharpCausalMass"),
    ("LowEnergy.ActualFourBlockSharpCausalMass.actual_source_wave_square_integrable", "H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceActualFourBlockSharpCausalMass"),
    ("LowEnergy.ActualFourBlockSignedSector.actual_coherent_neutral_point", "H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceActualFourBlockSignedSector"),
    ("LowEnergy.ActualFourBlockSignedSector.actual_coherent_occupation", "H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceActualFourBlockSignedSector"),
    ("LowEnergy.ActualFourBlockSignedSector.actual_generated_source_dynamic_selection", "H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceActualFourBlockSignedSector"),
    ("LowEnergy.ActualFourBlockSignedSector.actual_neutral_frequency", "H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceActualFourBlockSignedSector"),
    ("LowEnergy.ActualFourBlockSignedSector.actual_neutral_frequency_point", "H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceActualFourBlockSignedSector"),
    ("LowEnergy.ActualFourBlockSignedSector.actual_neutral_measure", "H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceActualFourBlockSignedSector"),
    ("LowEnergy.ActualFourBlockSignedSector.actual_neutral_time_point", "H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceActualFourBlockSignedSector"),
    ("LowEnergy.ActualFourBlockSignedSector.neutralFrequency", "H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceActualFourBlockSignedSector"),
    ("LowEnergy.ActualFourBlockSignedSector.neutralMeasure", "H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceActualFourBlockSignedSector"),
    ("LowEnergy.ActualFourBlockSource.Kinematics", "H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.MixedSpectatorFourBlockSource"),
    ("LowEnergy.ActualFourBlockSource.actual_block_candidate_neutral", "H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.MixedSpectatorFourBlockSource"),
    ("LowEnergy.ActualFourBlockSource.actual_block_source_point", "H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.MixedSpectatorFourBlockSource"),
    ("LowEnergy.ActualFourBlockSource.actual_coherent_candidate_neutral", "H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.MixedSpectatorFourBlockSource"),
    ("LowEnergy.ActualFourBlockSource.actual_coherent_source_point", "H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.MixedSpectatorFourBlockSource"),
    ("LowEnergy.ActualFourBlockSource.block", "H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.MixedSpectatorFourBlockSource"),
    ("LowEnergy.ActualFourBlockSource.blockFiber", "H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.MixedSpectatorFourBlockSource"),
    ("LowEnergy.ActualFourBlockSource.blockSource", "H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.MixedSpectatorFourBlockSource"),
    ("LowEnergy.ActualFourBlockSource.coherentSource", "H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.MixedSpectatorFourBlockSource"),
    ("LowEnergy.ActualFourBlockSource.coherentTree", "H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.MixedSpectatorFourBlockSource"),
    ("LowEnergy.GeneralThreeParticleYukawaOptical.actual_generated_candidate_signed_current", "H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceGeneralThreeParticleYukawaOptical"),
    ("LowEnergy.GeneralThreeParticleYukawaOptical.actual_originalY_band", "H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceGeneralThreeParticleYukawaOptical"),
    ("LowEnergy.GeneralThreeParticleYukawaOptical.actual_originalY_band_measure", "H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceGeneralThreeParticleYukawaOptical"),
    ("LowEnergy.GeneralThreeParticleYukawaOptical.actual_originalY_integrable", "H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceGeneralThreeParticleYukawaOptical"),
    ("LowEnergy.GeneralThreeParticleYukawaOptical.actual_originalY_pointwise", "H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceGeneralThreeParticleYukawaOptical"),
    ("LowEnergy.GeneralThreeParticleYukawaOptical.originalYCurrent", "H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceGeneralThreeParticleYukawaOptical"),
    ("LowEnergy.MixedSpectatorCandidate.actual_candidate_test_Y_nonzero", "H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.MixedSpectatorYukawaNonzero"),
    ("LowEnergy.MixedSpectatorCandidate.actual_candidate_vacuum_Y_nonzero", "H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.MixedSpectatorYukawaNonzero"),
    ("LowEnergy.MixedSpectatorCandidate.actual_generated_candidate_Y_source", "H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.MixedSpectatorYukawaNonzero"),
    ("LowEnergy.MixedSpectatorCandidate.actual_generated_candidate_bounded_Y_source", "H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.MixedSpectatorYukawaNonzero"),
    ("LowEnergy.MixedSpectatorCandidate.actual_vacuum_primal_entry_nonzero", "H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.MixedSpectatorYukawaNonzero"),
    ("LowEnergy.YukawaResolventDetection.actual_Y_correction_integral_pos", "H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceYukawaPositiveCorrection"),
    ("LowEnergy.YukawaResolventDetection.actual_Y_correction_measure_pos", "H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceYukawaPositiveCorrection"),
    ("LowEnergy.YukawaResolventDetection.actual_Y_correction_nonzero", "H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceYukawaPositiveCorrection"),
    ("LowEnergy.YukawaResolventDetection.actual_generated_candidate_Y_excess", "H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceYukawaPositiveCorrection"),
    ("LowEnergy.YukawaResolventDetection.actual_unforced_strict_excess", "H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceYukawaPositiveCorrection")]
  for (decl, owner) in roots do
    let name := releaseName decl
    unless (env.checked.get.find? name).isSome do throwError "MISSING_DECLARATION {name}"
    let some index := env.getModuleIdxFor? name | throwError "MISSING_DECLARATION_MODULE {name}"
    unless env.header.moduleNames[index]! == releaseName owner do
      throwError "WRONG_DECLARATION_MODULE {name} expected={owner} actual={env.header.moduleNames[index]!}"
  let closure := recoveryClosure env (roots.map fun item => releaseName item.1)
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut axioms : NameSet := {}
  let mut edges := 0
  for name in closure.toArray do
    let some info := env.checked.get.find? name | throwError "UNCHECKED_CONSTANT {name}"
    if info.isUnsafe || info.isPartial then throwError "UNSAFE_PARTIAL {name}"
    edges := edges + (completeRefs info).size
    match info with
    | .axiomInfo _ =>
        unless allowed.contains name do throwError "UNAPPROVED_AXIOM {name}"
        axioms := axioms.insert name
    | .defnInfo _ | .thmInfo _ | .opaqueInfo _ =>
        unless (info.value? true).isSome do throwError "MISSING_CONSTANT_VALUE {name}"
    | _ => pure ()
  let report := Json.mkObj [
    ("token", toJson "bacc95870e3a1b1d28ee4b3361305e9a888dccd8c9817b0bf8bba8a25738de4a"), ("roots", toJson roots.length),
    ("constants", toJson closure.size), ("edges", toJson edges),
    ("axioms", toJson (axioms.toArray.toList.map Name.toString)),
    ("unsafe", toJson (0 : Nat)), ("partial", toJson (0 : Nat)),
    ("full_metadata", toJson true)]
  logInfo m!"FIRST_RELEASE_TRUST {report.compress}"
