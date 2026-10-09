import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025.Source.Raw

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025.Assay

def decimal? (text : String) : Option ℚ := do
  let (negative,word) := match text.toList with
    | '–' :: tail | '-' :: tail => (true,tail)
    | '+' :: tail => (false,tail)
    | tail => (false,tail)
  let value ← LMNACorrection2021.Histology.decimalChars? word
  pure (if negative then -value else value)
def number? (text : Option String) : Option ℚ := text.bind decimal?
def mean? (values : List (Option ℚ)) : Option ℚ := do
  if values.isEmpty then none else do
    let xs ← values.mapM id
    pure (xs.sum / xs.length)
def row (i : Nat) : AssayRow := Source.assays[i]!
def treated (i : Nat) : List (Option ℚ) := (row i).values.take 3
def control (i : Nat) : List (Option ℚ) := (row i).values.drop 3 |>.take 3
def net? (i : Nat) : Option ℚ := do pure ((← mean? (treated i)) - (← mean? (control i)))
def reported? (i : Nat) : Option ℚ := ((row i).values[6]?).bind id
def residual? (i : Nat) : Option ℚ := do pure ((← net? i) - (← reported? i))

theorem complete_original_table :
    Source.assays.length = 23 ∧
    Source.assays.all (fun r => r.rawNumbers.length == 7 && r.values == r.rawNumbers.map number?) = true ∧
    Source.assays.all (fun r => (r.values.take 6).all (fun v => v.isNone ||
      ((v.getD 0) ≥ 0 && (v.getD 0) ≤ 100))) = true := by decide +kernel

theorem original_missing_and_unreported_controls :
    ((List.range 23).filter (fun i => (treated i).all Option.isNone)) = [6,12,14,15,19] ∧
    control 0 = [none,none,none] ∧ reported? 0 = none ∧ net? 0 = none ∧
    ((List.range 23).filter (fun i => (net? i).isSome)).length = 17 := by decide +kernel

theorem original_insert_response :
    treated 0 = [some (6362/100),some (5859/100),some (6140/100)] ∧
    mean? (treated 0) = some (18361/300) ∧
    (treated 0).all (fun x => 50 < x.getD 0 && x.getD 0 < 65) = true := by decide +kernel

theorem original_WT_and_off_target_responses :
    (row 1).columns[0]! = "chr2:210591871" ∧ net? 1 = some (143/50) ∧
    (row 10).columns[0]! = "chr13:51941585" ∧ net? 10 = some (113/300) ∧
    reported? 10 = some (38/100) ∧ residual? 10 = some (-1/300) := by decide +kernel

theorem every_reported_net_retains_rounding_residual :
    (List.range 23).all (fun i => match net? i,reported? i with
      | some actual,some printed => -1/100 ≤ actual-printed && actual-printed ≤ 1/100
      | none,none => true
      | _,_ => false) = true := by decide +kernel

end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025.Assay
