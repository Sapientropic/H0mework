import H0mework.Chemistry.LAlanineInertia.SourceSourceBoundLAlanine40KInertialStep
import Lean.Elab.Command

/-!
# Original isotope-mass preparation

Read the mass convention and decimal quantities from the already bound inertial source.
The unused integer table is retained as an independent recognition readout. It does not
select the mass used by the dynamics or the mass-number decoder.
-/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.AtomicMass.Source

open Lean Elab Term Inertia.SourceParsing Force.Interface
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Closure.Empirical.Manifest

/-- Source decimals are exact rationals; binary multiplication error remains downstream. -/
structure MassPreparation where
  convention : String
  conversion : ℚ
  massAmu : Inertia.Mechanics.Masses
  defaultMassNumber : Atom → Int

private def sourceText : String :=
  include_str "../../../../evidence/biomedical/calculations/lalanine40k-target-erased-quantum-bond-density/inertia/source/lalanine40k-inertial-next.json"

private def decimalPair (value : Json) : TermElabM (Int × Nat) := do
  match value with
  | .num value => pure (value.mantissa, 10 ^ value.exponent)
  | _ => throwError "Original mass preparation requires a JSON decimal"

def integerRead (rows : Array Int) : Atom → Int := fun atom => rows[atom.val]!

elab "lalanineOriginalMassPreparation%" : term => do
  unless Sha256.hex sourceText == Inertia.Source.sourceArtifactSha256 do
    throwError "Original inertial mass source changed"
  let source ← parse sourceText
  let preparation ← field source "preparation"
  let convention ← decode String (← field preparation "mass_convention")
  let conversion ← decimalPair (← field preparation "amu_to_electron_mass")
  let masses ← decode (Array Json) (← field preparation "mass_amu")
  let defaults ← decode (Array Int) (← field preparation "parent_unused_ISOTOPE_MAIN_amu")
  unless masses.size == 13 && defaults.size == 13 do
    throwError "Original mass preparation changed its atom carrier"
  Meta.mkAppM ``MassPreparation.mk
    #[toExpr convention,
      ← Meta.mkAppM ``rationalRead #[toExpr conversion],
      ← Meta.mkAppM ``massRead #[toExpr (← masses.mapM decimalPair)],
      ← Meta.mkAppM ``integerRead #[toExpr defaults]]

/-- The same preparation that generated the masses inherited by M3. -/
noncomputable def preparation : MassPreparation := lalanineOriginalMassPreparation%

theorem preparation_convention : preparation.convention =
    "PySCF 2.10.0 COMMON_ISOTOPE_MASSES; model choice, not isotope observation" := rfl

theorem preparation_conversion : preparation.conversion =
    (18228884858012984 : ℚ) / 10000000000000 := rfl

end LAlanine40K2025.AtomicMass.Source
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
