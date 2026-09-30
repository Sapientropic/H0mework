import H0mework.Chemistry.LAlanineSignedEvaluator.Contraction
import H0mework.Chemistry.LAlanineRefinementSource.FiniteData

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.SourceRectangle

open Lean Elab Term Command SourceGaussianModel SourceSignedEvaluator SourceExponential SourceFiniteData
open SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Inertia.SourceParsing

abbrev Field := Fin 17
abbrev Group := Fin 94
abbrev Jet := Fin 20
abbrev Leaf := Fin 188

structure GroupData where
  atom : Nat
  exponent : Int × Nat
  centre : Array (Int × Nat)
  members : Array (Nat × Nat)
  deriving Inhabited, ToExpr

def rectangleText : String := include_str "../../../../evidence/biomedical/calculations/lalanine40k-target-erased-quantum-bond-density/inertia/basin_refinement/continuous/source/rectangle-jet-cell16.json"
def fieldText : String := include_str "../../../../evidence/biomedical/calculations/lalanine40k-target-erased-quantum-bond-density/inertia/basin_refinement/continuous/source/rk4-cell16-run0.json"

private def declare (suffix : Name) (value : Expr) : TermElabM Unit := do
  let type ← Meta.inferType value
  let name := (← getCurrNamespace) ++ suffix
  addDecl (.defnDecl { name, levelParams := [], type, value, hints := .regular 0, safety := .safe })
  modifyEnv (addNoncomputable · name)

private def readRational (value : Json) : TermElabM (Int × Nat) := do
  let row ← decode (Array Json) value
  unless row.size == 2 do throwError "source rational pair"
  let numerator ← decode Int row[0]!
  let denominator ← decode Nat row[1]!
  unless denominator > 0 do throwError "source rational denominator"
  pure (numerator, denominator)

private def integerPair (value : Json) : TermElabM (Int × Int) := do
  let row ← decode (Array Int) value
  unless row.size == 2 && row[0]! ≤ row[1]! do throwError "ordered source integer interval"
  pure (row[0]!, row[1]!)

private def integerRows (value : Json) (width : Nat) : TermElabM (Array (Int × Int)) := do
  let row ← decode (Array Json) value
  unless row.size == width do throwError "source interval census"
  row.mapM integerPair

elab "generateActualRectangle" : command => liftTermElabM do
  let hash := SaturationMonoid.NoIslandNoMagic.Consciousness.Closure.Empirical.Manifest.Sha256.hex
  unless hash rectangleText == "db80f45167d86dc293673f0bea526273d353403c5f377addb0822ed27248fb5f" &&
      hash fieldText == "a366023f2256f1e53c045b6fe9ae951b78876fca4679d7b3ead3e7ca9167c011" &&
      hash SourceFiniteData.sourceText == "704198fc5fb94e27e32ff770d5b1c1e41918fb5aa1fc27a4d8035dba3f499451" do
    throwError "fixed actual rectangle source changed"
  let rectangle ← parse rectangleText
  let fieldPacket ← parse fieldText
  let gaussian ← parse SourceFiniteData.sourceText
  let source ← field rectangle "source"
  let nextSource ← field fieldPacket "source"
  for key in ["root_current", "same_physical_event", "gaussian_packet_sha256", "geometry_packet_sha256",
      "same_original_parent_join", "physical_raw_sha256"] do
    unless (← field source key) == (← field nextSource key) do throwError "rectangle and RK4 source join {key}"
  unless (← decode String (← field source "gaussian_packet_sha256")) == hash SourceFiniteData.sourceText &&
      (← decode String (← field source "geometry_packet_sha256")) ==
        "cf46fad3d849b801551bf5edaf231e727b9ba0b20dd92b98b3430c6489ba646b" &&
      (← decode String (← field nextSource "rectangle_packet_sha256")) == hash rectangleText do
    throwError "same Gaussian and geometry occurrence"
  let gaussianSource ← field gaussian "source"
  unless (← field source "same_original_parent_join") == (← field gaussianSource "parent_join") &&
      (← field source "physical_raw_sha256") == (← field gaussianSource "reentry_raw_sha256") do
    throwError "original M3 source identity"
  unless (← decode String (← field source "root_current")) == "BasinRefinement.Runtime.refinementRuntimeAfterFirst" do
    throwError "fixed current"
  let arithmetic ← field rectangle "arithmetic"
  unless (← field fieldPacket "arithmetic") == arithmetic &&
      (← decode Nat (← field arithmetic "scale_bits")) == 160 &&
      (← decode Nat (← field arithmetic "taylor_terms")) == 16 do throwError "source arithmetic protocol"
  let indices ← decode (Array (Array Nat)) (← field arithmetic "multiindices")
  let originalIndices ← decode (Array (Array Nat)) (← field (← field gaussian "generated_bounds") "multiindices")
  unless indices == originalIndices.extract 0 20 do throwError "source derivative prefix incidence"
  declare `rawJetIndices (toExpr indices)
  let actual ← field fieldPacket "actual_scope"
  unless (← decode Nat (← field actual "cell")) == 16 &&
      (← decode Nat (← field actual "source_segment")) == 4 &&
      (← decode Nat (← field actual "source_subsegment")) == 0 &&
      (← decode Nat (← field actual "source_run")) == 0 &&
      (← decode Nat (← field actual "rk4_steps")) == 4 do throwError "actual restricted parameter occurrence"
  let coefficientSource ← field gaussian "gaussian_source"
  let centres ← decode (Array Json) (← field coefficientSource "centres")
  let terms ← decode (Array (Array Json)) (← field coefficientSource "terms")
  unless centres.size == 13 && terms.size == 98 do throwError "original source basis census"
  let groups ← decode (Array Json) (← field rectangle "gaussian_groups")
  unless groups.size == 94 && (← field fieldPacket "gaussian_groups") == (← field rectangle "gaussian_groups") do
    throwError "same Gaussian group census"
  let mut groupData : Array GroupData := #[]
  let mut seen : Array (Nat × Nat) := #[]
  for g in [:94] do
    let row := groups[g]!
    unless (← decode Nat (← field row "index")) == g &&
        (← decode (Array Nat) (← field row "exp_leaf_indices")) == #[2*g, 2*g+1] do
      throwError "group/leaf incidence"
    let atom ← decode Nat (← field row "atom")
    unless atom < 13 do throwError "source nucleus incidence"
    let exponent ← readRational (← field row "exponent")
    let members ← decode (Array (Array Nat)) (← field row "term_members")
    unless members.size > 0 do throwError "empty Gaussian group"
    let mut addresses : Array (Nat × Nat) := #[]
    for member in members do
      unless member.size == 2 && member[0]! < 98 && member[1]! < terms[member[0]!]!.size do
        throwError "actual source term address"
      let address := (member[0]!, member[1]!)
      unless !seen.contains address do throwError "repeated source term"
      let term := (terms[member[0]!]!)[member[1]!]!
      unless (← decode Nat (← field term "atom")) == atom &&
          (← readRational (← field term "exponent")) == exponent do throwError "term/group source incidence"
      seen := seen.push address
      addresses := addresses.push address
    let point ← decode (Array Json) centres[atom]!
    unless point.size == 3 do throwError "source centre dimension"
    groupData := groupData.push ⟨atom, exponent, ← point.mapM readRational, addresses⟩
  unless seen.size == 208 && terms.foldl (fun count row => count + row.size) 0 == 208 do
    throwError "complete source term registration"
  declare `rawGroups (toExpr groupData)
  let fields ← decode (Array Json) (← field fieldPacket "source_fields")
  unless fields.size == 17 do throwError "full four-step/final-field census"
  let mut boxes : Array (Array (Int × Int)) := #[]
  let mut arguments : Array (Array (Int × Int)) := #[]
  let mut reductions : Array (Array (Nat × Nat)) := #[]
  let mut exponentials : Array (Array (Int × Int)) := #[]
  let mut leafInitial : Array (Array (Int × Int)) := #[]
  let mut leafResult : Array (Array (Int × Int)) := #[]
  let mut density : Array (Array (Int × Int)) := #[]
  for f in [:17] do
    let row := fields[f]!
    unless (← decode Nat (← field row "call")) == f do throwError "field call incidence"
    boxes := boxes.push (← integerRows (← field row "box_integer_intervals") 3)
    density := density.push (← integerRows (← field row "density_integer_intervals") 20)
    let leaves ← decode (Array Json) (← field row "exp_leaves")
    unless leaves.size == 188 do throwError "complete source exponential leaf census"
    leafInitial := leafInitial.push (← leaves.mapM fun leaf => do integerPair (← field leaf "initial_integer_interval"))
    leafResult := leafResult.push (← leaves.mapM fun leaf => do integerPair (← field leaf "result_integer_interval"))
    let mut args : Array (Int × Int) := #[]
    let mut levels : Array (Nat × Nat) := #[]
    let mut results : Array (Int × Int) := #[]
    for g in [:94] do
      let left := leaves[2*g]!
      let right := leaves[2*g+1]!
      unless (← decode Nat (← field left "terms")) == 16 &&
          (← decode Nat (← field right "terms")) == 16 do throwError "same source Taylor order"
      args := args.push (← decode Int (← field left "argument_integer"), ← decode Int (← field right "argument_integer"))
      levels := levels.push (← decode Nat (← field left "range_reduction"), ← decode Nat (← field right "range_reduction"))
      let lv ← integerPair (← field left "result_integer_interval")
      let rv ← integerPair (← field right "result_integer_interval")
      results := results.push (lv.1, rv.2)
    arguments := arguments.push args
    reductions := reductions.push levels
    exponentials := exponentials.push results
  let first ← field rectangle "evaluation"
  for key in ["call", "box_integer_intervals", "exp_leaves", "density_integer_intervals"] do
    unless (← field first key) == (← field fields[0]! key) do throwError "first actual field changed {key}"
  let aoRows ← decode (Array Json) (← field first "ao_integer_intervals")
  unless aoRows.size == 20 do throwError "source orbital jet census"
  let ao ← aoRows.mapM (integerRows · 98)
  for (name, value) in [(`rawBoxes, toExpr boxes), (`rawArguments, toExpr arguments),
      (`rawReductions, toExpr reductions), (`rawExponentials, toExpr exponentials),
      (`rawDensity, toExpr density), (`rawOrbital, toExpr ao),
      (`rawLeafInitial, toExpr leafInitial), (`rawLeafResult, toExpr leafResult)] do
    declare name value

generateActualRectangle

noncomputable section

abbrev source_terms : Basis → List SourceGaussianModel.Term := SourceFiniteData.sourceTerms
abbrev source_matrix : Basis → Basis → ℚ := SourceFiniteData.densityMatrix

def integerInterval (p : Int × Int) : Pair := ((p.1 : ℚ) / scale, (p.2 : ℚ) / scale)
def actualBox (f : Field) : Rectangle := fun axis => integerInterval ((rawBoxes[f.val]!)[axis.val]!)
def groupExponent (g : Group) : ℚ := SourceFiniteData.ratRead (rawGroups[g.val]!).exponent
def groupCentre (g : Group) (axis : Fin 3) : ℚ :=
  SourceFiniteData.ratRead ((rawGroups[g.val]!).centre[axis.val]!)

def groupMatches (term : SourceGaussianModel.Term) (group : GroupData) : Bool :=
  decide (term.exponent = SourceFiniteData.ratRead group.exponent ∧
    term.centre 0 = SourceFiniteData.ratRead group.centre[0]! ∧
    term.centre 1 = SourceFiniteData.ratRead group.centre[1]! ∧
    term.centre 2 = SourceFiniteData.ratRead group.centre[2]!)

def groupForTerm (term : SourceGaussianModel.Term) : Nat := rawGroups.findIdx (groupMatches term)
def steps (f : Field) (term : SourceGaussianModel.Term) : Nat × Nat := (rawReductions[f.val]!)[groupForTerm term]!
def groupSteps (f : Field) (g : Group) : Nat × Nat := (rawReductions[f.val]!)[g.val]!

private def zeroTerm : SourceGaussianModel.Term := ⟨0, 0, fun _ => 0, fun _ => 0⟩
def groupTerm (g : Group) : SourceGaussianModel.Term :=
  let address := (rawGroups[g.val]!).members[0]!
  ((source_terms ⟨address.1 % 98, Nat.mod_lt _ (by decide)⟩)[address.2]?).getD zeroTerm

def reportedArgument (f : Field) (g : Group) : Pair := integerInterval ((rawArguments[f.val]!)[g.val]!)
def reportedExp (f : Field) (g : Group) : Pair := integerInterval ((rawExponentials[f.val]!)[g.val]!)
def reportedAO (jet : Jet) (basis : Basis) : Pair := integerInterval ((rawOrbital[jet.val]!)[basis.val]!)
def reportedDensity (f : Field) (jet : Jet) : Pair := integerInterval ((rawDensity[f.val]!)[jet.val]!)
def reportedLeafInitial (f : Field) (leaf : Leaf) : Pair := integerInterval ((rawLeafInitial[f.val]!)[leaf.val]!)
def reportedLeafResult (f : Field) (leaf : Leaf) : Pair := integerInterval ((rawLeafResult[f.val]!)[leaf.val]!)
def leafArgument (f : Field) (leaf : Leaf) : ℚ :=
  let ends := (rawArguments[f.val]!)[leaf.val / 2]!
  (if leaf.val % 2 = 0 then (ends.1 : ℚ) else (ends.2 : ℚ)) / scale
def leafReduction (f : Field) (leaf : Leaf) : Nat :=
  let ends := (rawReductions[f.val]!)[leaf.val / 2]!
  if leaf.val % 2 = 0 then ends.1 else ends.2
def jetIndex (jet : Jet) : SourceFiniteData.JetIndex := ⟨jet.val, Nat.lt_trans jet.isLt (by decide)⟩
def multiindex (jet : Jet) : MultiIndex := fun axis => (rawJetIndices[jet.val]!)[axis.val]!

theorem same_original_terms : source_terms = SourceFiniteData.sourceTerms := rfl
theorem same_original_matrix : source_matrix = SourceFiniteData.densityMatrix := rfl

end
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.SourceRectangle
