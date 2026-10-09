import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockElastic.SourceActualFourBlockRealTransferCanonicalSelectionRows0
import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockElastic.SourceActualFourBlockRealTransferCanonicalSelectionRows1
set_option autoImplicit false
set_option maxRecDepth 8192
noncomputable section
namespace LowEnergy.ActualFourBlockRealTransfer
open MixedSpectatorCanonical79Data
open SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair

def canonicalInverseSelector (a b : Fin 79) : Option (Fin 526 × Fin 10) :=
  match a.val with
  | 0 => canonicalInverseSelectorRow0 b
  | 1 => canonicalInverseSelectorRow1 b
  | 2 => canonicalInverseSelectorRow2 b
  | 3 => canonicalInverseSelectorRow3 b
  | 4 => canonicalInverseSelectorRow4 b
  | 5 => canonicalInverseSelectorRow5 b
  | 6 => canonicalInverseSelectorRow6 b
  | 7 => canonicalInverseSelectorRow7 b
  | 8 => canonicalInverseSelectorRow8 b
  | 9 => canonicalInverseSelectorRow9 b
  | 10 => canonicalInverseSelectorRow10 b
  | 11 => canonicalInverseSelectorRow11 b
  | 12 => canonicalInverseSelectorRow12 b
  | 13 => canonicalInverseSelectorRow13 b
  | 14 => canonicalInverseSelectorRow14 b
  | 15 => canonicalInverseSelectorRow15 b
  | 16 => canonicalInverseSelectorRow16 b
  | 17 => canonicalInverseSelectorRow17 b
  | 18 => canonicalInverseSelectorRow18 b
  | 19 => canonicalInverseSelectorRow19 b
  | 20 => canonicalInverseSelectorRow20 b
  | 21 => canonicalInverseSelectorRow21 b
  | 22 => canonicalInverseSelectorRow22 b
  | 23 => canonicalInverseSelectorRow23 b
  | 24 => canonicalInverseSelectorRow24 b
  | 25 => canonicalInverseSelectorRow25 b
  | 26 => canonicalInverseSelectorRow26 b
  | 27 => canonicalInverseSelectorRow27 b
  | 28 => canonicalInverseSelectorRow28 b
  | 29 => canonicalInverseSelectorRow29 b
  | 30 => canonicalInverseSelectorRow30 b
  | 31 => canonicalInverseSelectorRow31 b
  | 32 => canonicalInverseSelectorRow32 b
  | 33 => canonicalInverseSelectorRow33 b
  | 34 => canonicalInverseSelectorRow34 b
  | 35 => canonicalInverseSelectorRow35 b
  | 36 => canonicalInverseSelectorRow36 b
  | 37 => canonicalInverseSelectorRow37 b
  | 38 => canonicalInverseSelectorRow38 b
  | 39 => canonicalInverseSelectorRow39 b
  | 40 => canonicalInverseSelectorRow40 b
  | 41 => canonicalInverseSelectorRow41 b
  | 42 => canonicalInverseSelectorRow42 b
  | 43 => canonicalInverseSelectorRow43 b
  | 44 => canonicalInverseSelectorRow44 b
  | 45 => canonicalInverseSelectorRow45 b
  | 46 => canonicalInverseSelectorRow46 b
  | 47 => canonicalInverseSelectorRow47 b
  | 48 => canonicalInverseSelectorRow48 b
  | 49 => canonicalInverseSelectorRow49 b
  | 50 => canonicalInverseSelectorRow50 b
  | 51 => canonicalInverseSelectorRow51 b
  | 52 => canonicalInverseSelectorRow52 b
  | 53 => canonicalInverseSelectorRow53 b
  | 54 => canonicalInverseSelectorRow54 b
  | 55 => canonicalInverseSelectorRow55 b
  | 56 => canonicalInverseSelectorRow56 b
  | 57 => canonicalInverseSelectorRow57 b
  | 58 => canonicalInverseSelectorRow58 b
  | 59 => canonicalInverseSelectorRow59 b
  | 60 => canonicalInverseSelectorRow60 b
  | 61 => canonicalInverseSelectorRow61 b
  | 62 => canonicalInverseSelectorRow62 b
  | 63 => canonicalInverseSelectorRow63 b
  | 64 => canonicalInverseSelectorRow64 b
  | 65 => canonicalInverseSelectorRow65 b
  | 66 => canonicalInverseSelectorRow66 b
  | 67 => canonicalInverseSelectorRow67 b
  | 68 => canonicalInverseSelectorRow68 b
  | 69 => canonicalInverseSelectorRow69 b
  | 70 => canonicalInverseSelectorRow70 b
  | 71 => canonicalInverseSelectorRow71 b
  | 72 => canonicalInverseSelectorRow72 b
  | 73 => canonicalInverseSelectorRow73 b
  | 74 => canonicalInverseSelectorRow74 b
  | 75 => canonicalInverseSelectorRow75 b
  | 76 => canonicalInverseSelectorRow76 b
  | 77 => canonicalInverseSelectorRow77 b
  | 78 => canonicalInverseSelectorRow78 b
  | _ => none

theorem actual_canonical_inverse_selection (x : ℂ) (a b : Fin 79) :
    axialInverse x 0 a b = scaling a *
      selectedCanonicalInverse x (canonicalInverseSelector a b) * scaling b / (lapse : ℂ) := by
  fin_cases a
  · exact actual_canonical_inverse_row0 x b
  · exact actual_canonical_inverse_row1 x b
  · exact actual_canonical_inverse_row2 x b
  · exact actual_canonical_inverse_row3 x b
  · exact actual_canonical_inverse_row4 x b
  · exact actual_canonical_inverse_row5 x b
  · exact actual_canonical_inverse_row6 x b
  · exact actual_canonical_inverse_row7 x b
  · exact actual_canonical_inverse_row8 x b
  · exact actual_canonical_inverse_row9 x b
  · exact actual_canonical_inverse_row10 x b
  · exact actual_canonical_inverse_row11 x b
  · exact actual_canonical_inverse_row12 x b
  · exact actual_canonical_inverse_row13 x b
  · exact actual_canonical_inverse_row14 x b
  · exact actual_canonical_inverse_row15 x b
  · exact actual_canonical_inverse_row16 x b
  · exact actual_canonical_inverse_row17 x b
  · exact actual_canonical_inverse_row18 x b
  · exact actual_canonical_inverse_row19 x b
  · exact actual_canonical_inverse_row20 x b
  · exact actual_canonical_inverse_row21 x b
  · exact actual_canonical_inverse_row22 x b
  · exact actual_canonical_inverse_row23 x b
  · exact actual_canonical_inverse_row24 x b
  · exact actual_canonical_inverse_row25 x b
  · exact actual_canonical_inverse_row26 x b
  · exact actual_canonical_inverse_row27 x b
  · exact actual_canonical_inverse_row28 x b
  · exact actual_canonical_inverse_row29 x b
  · exact actual_canonical_inverse_row30 x b
  · exact actual_canonical_inverse_row31 x b
  · exact actual_canonical_inverse_row32 x b
  · exact actual_canonical_inverse_row33 x b
  · exact actual_canonical_inverse_row34 x b
  · exact actual_canonical_inverse_row35 x b
  · exact actual_canonical_inverse_row36 x b
  · exact actual_canonical_inverse_row37 x b
  · exact actual_canonical_inverse_row38 x b
  · exact actual_canonical_inverse_row39 x b
  · exact actual_canonical_inverse_row40 x b
  · exact actual_canonical_inverse_row41 x b
  · exact actual_canonical_inverse_row42 x b
  · exact actual_canonical_inverse_row43 x b
  · exact actual_canonical_inverse_row44 x b
  · exact actual_canonical_inverse_row45 x b
  · exact actual_canonical_inverse_row46 x b
  · exact actual_canonical_inverse_row47 x b
  · exact actual_canonical_inverse_row48 x b
  · exact actual_canonical_inverse_row49 x b
  · exact actual_canonical_inverse_row50 x b
  · exact actual_canonical_inverse_row51 x b
  · exact actual_canonical_inverse_row52 x b
  · exact actual_canonical_inverse_row53 x b
  · exact actual_canonical_inverse_row54 x b
  · exact actual_canonical_inverse_row55 x b
  · exact actual_canonical_inverse_row56 x b
  · exact actual_canonical_inverse_row57 x b
  · exact actual_canonical_inverse_row58 x b
  · exact actual_canonical_inverse_row59 x b
  · exact actual_canonical_inverse_row60 x b
  · exact actual_canonical_inverse_row61 x b
  · exact actual_canonical_inverse_row62 x b
  · exact actual_canonical_inverse_row63 x b
  · exact actual_canonical_inverse_row64 x b
  · exact actual_canonical_inverse_row65 x b
  · exact actual_canonical_inverse_row66 x b
  · exact actual_canonical_inverse_row67 x b
  · exact actual_canonical_inverse_row68 x b
  · exact actual_canonical_inverse_row69 x b
  · exact actual_canonical_inverse_row70 x b
  · exact actual_canonical_inverse_row71 x b
  · exact actual_canonical_inverse_row72 x b
  · exact actual_canonical_inverse_row73 x b
  · exact actual_canonical_inverse_row74 x b
  · exact actual_canonical_inverse_row75 x b
  · exact actual_canonical_inverse_row76 x b
  · exact actual_canonical_inverse_row77 x b
  · exact actual_canonical_inverse_row78 x b

end LowEnergy.ActualFourBlockRealTransfer
