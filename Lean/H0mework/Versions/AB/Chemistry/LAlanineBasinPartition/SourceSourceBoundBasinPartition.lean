import H0mework.Versions.AB.Chemistry.LAlanineBasinPartition.SourceParsing

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinPartition.Source

open Lean Elab Term Command Inertia.SourceParsing SourceData SourceReification

private def declareReadout (suffix : Name) (value : Expr) : TermElabM Unit := do
  let value ← instantiateMVars value
  let type ← Meta.inferType value
  let name := (← getCurrNamespace) ++ suffix
  addDecl (.defnDecl { name, levelParams := [], type, value, hints := .regular 0, safety := .safe })
  modifyEnv (addNoncomputable · name)

elab "generateBasinReadouts" : command => liftTermElabM do
  let (packet, ledger) ← SourceParsing.verifiedData
  let account ← field packet "accounting"
  let blocks ← decode (Array Json) (← field account "blocks")
  let global ← field account "global"
  let (counts, integrals) ← bucketCubes blocks
  declareReadout `bucketCounts counts
  declareReadout `bucketIntegrals integrals
  for (name, key) in [(`blockPointSums, "whole_integer_sums"), (`blockFloatSums, "whole_float_integral_scaled"),
      (`blockPointRoundingResidual, "point_rounding_residual")] do
    declareReadout name (← blockFieldExpr blocks key)
  declareReadout `blockGridToOldXcResidual (← blockWidthExpr blocks "grid_to_old_xc_residual" 3 ``blockXcRead)
  declareReadout `blockBucketGaugeResidual (← blockWidthExpr blocks "bucket_gauge_residuals" 20 ``blockBucketRead)
  for (name, key) in [(`globalPointSums, "point_integer_sums"), (`globalFloatSums, "whole_float_integral_scaled"),
      (`globalPointRoundingResidual, "point_rounding_residual")] do
    declareReadout name (← fieldVectorExpr (← field global key))
  declareReadout `globalBucketIntegrals (← bucketFieldExpr (← field global "bucket_integer_sums"))
  declareReadout `globalBucketGaugeResidual (← integerVectorExpr (← field global "bucket_gauge_residuals") 20 ``bucketVectorRead)
  let globalCounts ← decode (Array Nat) (← field global "bucket_counts")
  unless globalCounts.size == 20 do throwError "Basin global count census"
  declareReadout `globalBucketCounts (← Meta.mkAppM ``bucketCountRead #[toExpr globalCounts])
  let old ← field account "old_ledger_account"
  let mapped ← decode (Array Json) (← field old "mapped_fields")
  let residuals ← mapped.mapM fun row => do decode Int (← field row "grid_to_old_residual")
  declareReadout `gridToOldResidual (← Meta.mkAppM ``oldFieldRead #[toExpr residuals])
  for (name, key) in [(`gridElectronicIntegral, "electronic_grid_integral_scaled"),
      (`gridWithNuclearRepulsion, "with_original_nuclear_repulsion_scaled"),
      (`totalGridToOldResidual, "total_grid_to_old_residual")] do
    declareReadout name (toExpr (← decode Int (← field old key)))
  for (name, key) in [(`globalGaugeResidual, "whole_gauge_residual"),
      (`gridToSourceElectronResidual, "grid_to_source_electron_residual")] do
    declareReadout name (toExpr (← decode Int (← field global key)))
  declareReadout `oldGridElectronIntegral (toExpr (← decode Int (← field (← field ledger "electron_balance") "grid_integral_nano")))
  declareReadout `sourceElectronCount (toExpr (← decode Nat (← field global "source_electron_count")))
  let flow ← field packet "flow"
  for (name, key) in [(`stablePointCount, "stable_point_count"), (`residualPointCount, "typed_residual_point_count"),
      (`endpointDisagreements, "two_track_endpoint_disagreements"), (`zeroWeightPointCount, "source_zero_weight_points"),
      (`nearestDisagreementCount, "nearest_nucleus_disagreement_count")] do
    declareReadout name (toExpr (← decode Nat (← field flow key)))
  let examples ← decode (Array Json) (← field flow "nearest_nucleus_counterexamples")
  let examples ← examples.mapM fun row => do
    return (← decode Nat (← field row "source_row"), ← decode Nat (← field row "nearest_nucleus"),
      ← decode Nat (← field row "generated_basin"))
  declareReadout `nearestCounterexamples (toExpr examples)
  let attractors ← decode (Array Json) (← field packet "attractors")
  for (name, key) in [(`attractorDensityNano, "density_nano"),
      (`attractorSourceDistanceUpper, "source_nucleus_distance_upper_nanobohr"),
      (`attractorOtherDistanceLower, "nearest_other_nucleus_distance_lower_nanobohr")] do
    declareReadout name (← attractorScalarExpr attractors key)
  for (name, key) in [(`attractorGershgorinUpper, "gershgorin_upper_nano"),
      (`attractorGradientUpperFemto, "gradient_absolute_upper_femto")] do
    declareReadout name (← attractorVectorExpr attractors key)
  let hessians ← attractors.mapM fun row => do decode (Array (Array Int)) (← field row "hessian_nano")
  unless hessians.all (fun matrix => matrix.size == 3 && matrix.all (fun row => row.size == 3)) do
    throwError "Basin Hessian census"
  declareReadout `attractorHessianNano (← Meta.mkAppM ``atomMatrixRead #[toExpr hessians])

set_option maxRecDepth 4096 in
generateBasinReadouts

def sourcePacketText : String := SourceParsing.sourceText

end LAlanine40K2025.BasinPartition.Source
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
