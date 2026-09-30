import H0mework.Chemistry.LAlanineRefinementGeometry.Data

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.Geometry.Parsing

open Lean Elab Term Inertia.SourceParsing
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Closure.Empirical.Manifest

def sourceArtifactSha256 : String := "cf46fad3d849b801551bf5edaf231e727b9ba0b20dd92b98b3430c6489ba646b"
def sourceRawArchiveSha256 : String := "04f01e6761a0a4d63740170bea43037a3734dd6312816ceaa550d3457fa41699"
def sourceText : String := include_str "../../../../evidence/biomedical/calculations/lalanine40k-target-erased-quantum-bond-density/inertia/basin_refinement/source/geometry.json"

def array (value : Json) (count : Nat) : TermElabM (Array Json) := do
  let rows ← decode (Array Json) value
  unless rows.size == count do throwError "Refinement source array census {count}"
  pure rows

def ints (value : Json) (count : Nat) : TermElabM (Array Int) := do
  let rows ← decode (Array Int) value
  unless rows.size == count do throwError "Refinement source integer census {count}"
  pure rows

def nats (value : Json) (count : Nat) : TermElabM (Array Nat) := do
  let rows ← decode (Array Nat) value
  unless rows.size == count do throwError "Refinement source count census {count}"
  pure rows

def integer (value : Json) (key : String) : TermElabM Expr := return toExpr (← decode Int (← field value key))
def natural (value : Json) (key : String) : TermElabM Expr := return toExpr (← decode Nat (← field value key))

def positiveHexDyadic (value : String) : TermElabM (Int × Nat) := do
  let [mantissa, exponent] := value.splitOn "p" | throwError "Refinement dyadic exponent"
  unless mantissa.startsWith "0x" do throwError "Refinement positive dyadic mantissa"
  let some exponent := exponent.toInt? | throwError "Refinement dyadic signed exponent"
  let [whole, fraction] := (mantissa.drop 2).toString.splitOn "." | throwError "Refinement dyadic fraction"
  let mut numerator : Nat := 0
  for c in (whole ++ fraction).toList do
    let digit := if '0' ≤ c && c ≤ '9' then c.toNat - '0'.toNat else
      if 'a' ≤ c && c ≤ 'f' then c.toNat - 'a'.toNat + 10 else 16
    unless digit < 16 do throwError "Refinement hexadecimal digit"
    numerator := 16 * numerator + digit
  if exponent < 0 then
    pure (numerator, 16 ^ fraction.length * 2 ^ (-exponent).toNat)
  else pure ((numerator : Int) * 2 ^ exponent.toNat, 16 ^ fraction.length)

def domain (value : Json) : TermElabM Expr := do
  let buckets ← array (← field value "bucket_point_integrals") 20
  let buckets ← buckets.mapM (ints · 8)
  Meta.mkAppM ``Data.DomainReceipt.mk #[← natural value "row_count",
    toExpr (← nats (← field value "bucket_counts") 20), toExpr buckets,
    toExpr (← ints (← field value "point_integrals") 8), toExpr (← ints (← field value "float_integrals") 8),
    toExpr (← ints (← field value "point_rounding_residual") 8),
    ← integer value "parameter_jacobian_quadrature_measure_pico", ← integer value "sampled_jacobian_min_floor",
    ← natural value "endpoint_disagreements", toExpr (← decode (Option Nat) (← field value "whole_slab_basin_label"))]

def face (value : Json) : TermElabM Expr := do
  Meta.mkAppM ``Data.FaceReceipt.mk #[← natural value "segment", ← natural value "axis", ← natural value "side",
    ← natural value "row_count", ← integer value "point_flux", ← integer value "float_flux",
    ← integer value "point_rounding_residual", ← integer value "absolute_flux_ceil",
    ← integer value "sampled_normal_ratio_ceil", toExpr (← nats (← field value "bucket_counts") 20),
    ← natural value "endpoint_disagreements"]

def seam (value : Json) : TermElabM Expr := do
  Meta.mkAppM ``Data.SeamReceipt.mk #[← natural value "knot", ← natural value "left_face", ← natural value "right_face",
    ← integer value "point_sum", ← integer value "float_sum"]

def account (value : Json) : TermElabM Expr := do
  Meta.mkAppM ``Data.AccountReceipt.mk #[← integer value "band_laplacian_zepto",
    ← integer value "band_laplacian_pico_resolution_residual", ← integer value "point_boundary_flux",
    ← integer value "float_boundary_flux", ← integer value "boundary_point_rounding_residual",
    ← integer value "band_divergence_residual", ← integer value "cap_point_flux", ← integer value "side_point_flux",
    ← integer value "seam_point_flux", ← integer value "outer_v_point_flux",
    toExpr (← ints (← field value "three_slabs_to_whole_point_residual") 8),
    toExpr (← ints (← field value "three_slabs_to_whole_float_residual") 8)]

def run (value : Json) : TermElabM Expr := do
  let domains ← array (← field value "domains") 4
  for i in [:4] do
    unless (← decode Nat (← field domains[i]! "part")) == i do throwError "Refinement source slab incidence"
  let faces ← array (← field value "faces") 48
  for i in [:48] do
    unless (← decode Nat (← field faces[i]! "index")) == i do throwError "Refinement source face incidence"
  let seams ← array (← field value "seams") 7
  Meta.mkAppM ``Data.RunReceipt.mk #[← natural value "rk4_steps", toExpr (← decode String (← field value "epsilon_hex")),
    ← Meta.mkArrayLit (mkConst ``Data.DomainReceipt) (← domains.toList.mapM domain),
    ← Meta.mkArrayLit (mkConst ``Data.FaceReceipt) (← faces.toList.mapM face),
    ← Meta.mkArrayLit (mkConst ``Data.SeamReceipt) (← seams.toList.mapM seam),
    ← account (← field value "accounts"), toExpr (← nats (← field value "lower_side_counts") 20),
    toExpr (← nats (← field value "upper_side_counts") 20),
    ← integer value "sampled_curved_normal_ratio_ceil", ← integer value "sampled_curved_absolute_flux_ceil"]

def verifiedPacket : TermElabM Json := do
  unless Sha256.hex sourceText == sourceArtifactSha256 do throwError "Refinement source changed"
  let packet ← parse sourceText
  let parent ← parse BasinPartition.SourceParsing.sourceText
  let join ← field packet "source_join"
  let parentJoin ← field parent "source_join"
  unless (← decode String (← field packet "schema")) == "lalanine40k-source-generated-curved-basin-refinement/v1" &&
      (← decode String (← field join "basin_packet_sha256")) == BasinPartition.SourceParsing.sourceArtifactSha256 &&
      (← decode String (← field join "basin_raw_archive_sha256")) == BasinPartition.SourceParsing.sourceRawArchiveSha256 &&
      (← field join "parent_source_join") == parentJoin do throwError "Refinement wrong actual basin parent"
  unless (← decode String (← field join "parent_runtime_current")) ==
      "LAlanine40K2025.BasinPartition.Runtime.basinRuntimeAfterFirst" do throwError "Refinement wrong runtime"
  for key in ["whole_ledger_row", "claim", "time"] do
    unless (← field join key) == (← field parentJoin key) do throwError "Refinement source join {key}"
  unless rationalRead (← rationalPair (← field join "physical_elapsed_time")) == 0 do throwError "Refinement extra physical time"
  unless (← decode (Array String) (← field packet "field_names")) == BasinPartition.SourceData.fieldNames do
    throwError "Refinement changed field meanings"
  let protocol ← field packet "protocol"
  for (key, expected) in [("field_scale", 1000000000000), ("flux_scale", 1000000000000000000000),
      ("receipt_scale", 1000000000000000)] do
    unless (← decode Nat (← field protocol key)) == expected do throwError "Refinement source scale"
  for key in ["finite_RK4_map_not_exact_ODE", "full_parameter_Jacobian_not_gradient_substitution",
      "flow_parameter_is_not_physical_time", "mixed_band_has_no_basin_label",
      "sampled_Jacobian_is_not_continuous_injectivity", "continuous_boundary_placement_and_uncovered_region_retained"] do
    unless (← decode Bool (← field protocol key)) do throwError "Refinement geometric interpretation {key}"
  let runtime ← field packet "runtime"
  for key in ["new_scf_or_md", "pilot_result_input", "nearest_nucleus_assignment"] do
    unless !(← decode Bool (← field runtime key)) do throwError "Refinement forbidden source shortcut"
  pure packet

end LAlanine40K2025.BasinRefinement.Geometry.Parsing
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
