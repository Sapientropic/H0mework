import Lean.Elab.Term
import Lean.Meta.AppBuilder
import Lean.ToExpr
import Lean.Data.Json
import H0mework.Chemistry.LAlanineInertia.InterfaceSourceNativeInertialStep
import H0mework.Chemistry.LAlanineForce.BoundForceUpdate

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Inertia.SourceParsing

open Lean Elab Term
open Force.Interface

def field (value : Json) (key : String) : TermElabM Json :=
  match value.getObjVal? key with
  | .ok value => pure value
  | .error error => throwError "Inertial source field {key}: {error}"

def decode (α : Type) [FromJson α] (value : Json) : TermElabM α :=
  match fromJson? value with
  | .ok value => pure value
  | .error error => throwError "Inertial source decoder: {error}"

def parse (text : String) : TermElabM Json :=
  match Json.parse text with
  | .ok value => pure value
  | .error error => throwError "Inertial source JSON: {error}"

def rationalPair (value : Json) : TermElabM (Int × Nat) := do
  let numerator ← decode Int (← field value "numerator")
  let denominator ← decode Nat (← field value "denominator")
  unless denominator > 0 do throwError "Nonpositive rational denominator"
  pure (numerator, denominator)

def rationalRead (value : Int × Nat) : ℚ := (value.1 : ℚ) / value.2

def coordinateRead (rows : Array (Array (Int × Nat))) : Mechanics.Coordinates :=
  fun atom axis => rationalRead ((rows[atom.val]!)[axis.val]!)

def massRead (rows : Array (Int × Nat)) : Mechanics.Masses :=
  fun atom => rationalRead (rows[atom.val]!)

def rationalExpr (value : Json) : TermElabM Expr := do
  Meta.mkAppM ``rationalRead #[toExpr (← rationalPair value)]

def coordinates (value : Json) : TermElabM Expr := do
  let raw ← decode (Array Json) value
  unless raw.size == 13 do throwError "Changed nuclear coordinate carrier"
  let mut rows : Array (Array (Int × Nat)) := #[]
  for row in raw do
    let rawRow ← decode (Array Json) row
    unless rawRow.size == 3 do throwError "Changed spatial coordinate carrier"
    rows := rows.push (← rawRow.mapM rationalPair)
  Meta.mkAppM ``coordinateRead #[toExpr rows]

def masses (value : Json) : TermElabM Expr := do
  let raw ← decode (Array Json) value
  unless raw.size == 13 do throwError "Changed mass carrier"
  Meta.mkAppM ``massRead #[toExpr (← raw.mapM rationalPair)]

def integerCoordinates (value : Json) : TermElabM (Array (Array Int)) := do
  let rows ← decode (Array (Array Int)) value
  unless rows.size == 13 && rows.all (fun row => row.size == 3) do
    throwError "Changed integer nuclear incidence"
  pure rows

def integerCoordinateExpr (value : Json) : TermElabM Expr := do
  Meta.mkAppM ``Force.Source.coordinateRead #[toExpr (← integerCoordinates value)]

def nuclearRows (value : Json) : TermElabM (Expr × Expr) := do
  let rows ← decode (Array Json) value
  unless rows.size == 13 do throwError "Changed nuclear inventory"
  let mut inventory : Array (String × Nat) := #[]
  let mut positions : Array (Array Int) := #[]
  for index in [:13] do
    let row := rows[index]!
    unless (← decode Nat (← field row "atom_index")) == index do
      throwError "Changed nuclear address"
    inventory := inventory.push
      (← decode String (← field row "label"), ← decode Nat (← field row "charge"))
    let position ← decode (Array Int) (← field row "position_picobohr")
    unless position.size == 3 do throwError "Changed nuclear position"
    positions := positions.push position
  return (toExpr inventory, ← Meta.mkAppM ``Force.Source.coordinateRead #[toExpr positions])

def negativeCoordinates (values : Mechanics.Coordinates) : Mechanics.Coordinates :=
  fun atom axis => -values atom axis

def frame (value : Json) : TermElabM Expr := do
  let gradient ← coordinates (← field value "gradient_au")
  Meta.mkAppM ``Interface.NuclearFrame.mk
    #[← coordinates (← field value "positions_bohr"),
      ← coordinates (← field value "momenta_au"),
      ← Meta.mkAppM ``negativeCoordinates #[gradient],
      ← rationalExpr (← field value "nuclear_kinetic_hartree"),
      ← rationalExpr (← field value "potential_hartree"),
      ← rationalExpr (← field value "total_energy_hartree")]

def gradientComponents (force : Json) : TermElabM Expr := do
  let components ← field force "gradient_components_picohartree_per_bohr"
  let mut rows : Array (Array (Array Int)) := #[]
  for name in ["one_electron", "coulomb", "xc_basis", "pulay", "xc_grid_response", "nuclear_repulsion"] do
    rows := rows.push (← integerCoordinates (← field components name))
  pure (toExpr rows)

end LAlanine40K2025.Inertia.SourceParsing
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
