import H0mework.Versions.R9c73a630.Chemistry.LAlanineBandHighJet.Check
import H0mework.Versions.R9c73a630.Chemistry.LAlanineBandHighJet.MatrixCheck
import H0mework.Versions.R9c73a630.Chemistry.LAlanineBandHighJet.Material

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandGenerated.HighJet.Assembly
open Lean Elab Command

private def emit (text : String) : CommandElabM Unit := do
  match Parser.runParserCategory (← getEnv) `command text with
  | .error error => throwError "{error}"
  | .ok command => elabCommand command

elab "assembleHighJetMaterial " mode:num : command => do
  let scope := mode.getNat
  unless scope < 2 do throwError "original source scope"
  let branches := fun n stem => String.intercalate "\n" ((List.range n).map fun k => s!"    · exact {stem}{k}")
  emit s!"theorem groupCalculations (g : SourceRectangle.Group) : HighJet.GroupComputed localBox localReductions material g := by
    fin_cases g
{branches 94 "group"}"
  emit s!"theorem orbitalCalculations (b : SourceFiniteData.Basis) : HighJet.OrbitalComputed countBound HighJet.registeredProgram material b := by
    fin_cases b
{branches 98 "orbital"}"
  emit s!"theorem actual_density (j : Fin (HighJet.jetCount {scope})) (x : SourceGaussianModel.Point)
      (inside : SourceSignedEvaluator.InRectangle localBox x) :
      SourceSignedEvaluator.Holds (SourceIntegerGrid.grid (densityRows j))
        (Taylor.sourceJet (HighJet.prefixJet (HighJet.count_le {scope}) j) x) :=
    HighJet.material_density {scope} localBox localReductions material matrixRows groupCalculations
      orbitalCalculations matrixCertificate densityRows densityComputed j x inside"

end LAlanine40K2025.BasinRefinement.WholeBandGenerated.HighJet.Assembly
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
