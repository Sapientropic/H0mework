import H0mework.Chemistry.LAlaninePropagation.NativeElectronicPropagation
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Dense.Gram.B00
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Dense.Gram.B01
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Dense.Gram.B02
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Dense.Gram.B03
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Dense.Gram.B04
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Dense.Gram.B05
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Dense.Gram.B06
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Dense.Gram.B07
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Dense.Gram.B08
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Dense.Gram.B09
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Dense.Gram.B10
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Dense.Gram.B11
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Dense.Gram.B12
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.Spectral.Rows

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Dense
open Spectral Propagation.Interface
open scoped Matrix BigOperators

def densityGramRows : List (List Int) := [gramRow0,gramRow1,gramRow2,gramRow3,gramRow4,gramRow5,gramRow6,gramRow7,gramRow8,gramRow9,gramRow10,gramRow11,gramRow12,gramRow13,gramRow14,gramRow15,gramRow16,gramRow17,gramRow18,gramRow19,gramRow20,gramRow21,gramRow22,gramRow23,gramRow24,gramRow25,gramRow26,gramRow27,gramRow28,gramRow29,gramRow30,gramRow31,gramRow32,gramRow33,gramRow34,gramRow35,gramRow36,gramRow37,gramRow38,gramRow39,gramRow40,gramRow41,gramRow42,gramRow43,gramRow44,gramRow45,gramRow46,gramRow47,gramRow48,gramRow49,gramRow50,gramRow51,gramRow52,gramRow53,gramRow54,gramRow55,gramRow56,gramRow57,gramRow58,gramRow59,gramRow60,gramRow61,gramRow62,gramRow63,gramRow64,gramRow65,gramRow66,gramRow67,gramRow68,gramRow69,gramRow70,gramRow71,gramRow72,gramRow73,gramRow74,gramRow75,gramRow76,gramRow77,gramRow78,gramRow79,gramRow80,gramRow81,gramRow82,gramRow83,gramRow84,gramRow85,gramRow86,gramRow87,gramRow88,gramRow89,gramRow90,gramRow91,gramRow92,gramRow93,gramRow94,gramRow95,gramRow96,gramRow97]

theorem densityGramRows_length : densityGramRows.length=98 := by rfl

theorem densityGramRows_lengths (i : Basis) : (Rows.rowAt densityGramRows i).length=98 := by
  fin_cases i
  · exact gramRow0_length
  · exact gramRow1_length
  · exact gramRow2_length
  · exact gramRow3_length
  · exact gramRow4_length
  · exact gramRow5_length
  · exact gramRow6_length
  · exact gramRow7_length
  · exact gramRow8_length
  · exact gramRow9_length
  · exact gramRow10_length
  · exact gramRow11_length
  · exact gramRow12_length
  · exact gramRow13_length
  · exact gramRow14_length
  · exact gramRow15_length
  · exact gramRow16_length
  · exact gramRow17_length
  · exact gramRow18_length
  · exact gramRow19_length
  · exact gramRow20_length
  · exact gramRow21_length
  · exact gramRow22_length
  · exact gramRow23_length
  · exact gramRow24_length
  · exact gramRow25_length
  · exact gramRow26_length
  · exact gramRow27_length
  · exact gramRow28_length
  · exact gramRow29_length
  · exact gramRow30_length
  · exact gramRow31_length
  · exact gramRow32_length
  · exact gramRow33_length
  · exact gramRow34_length
  · exact gramRow35_length
  · exact gramRow36_length
  · exact gramRow37_length
  · exact gramRow38_length
  · exact gramRow39_length
  · exact gramRow40_length
  · exact gramRow41_length
  · exact gramRow42_length
  · exact gramRow43_length
  · exact gramRow44_length
  · exact gramRow45_length
  · exact gramRow46_length
  · exact gramRow47_length
  · exact gramRow48_length
  · exact gramRow49_length
  · exact gramRow50_length
  · exact gramRow51_length
  · exact gramRow52_length
  · exact gramRow53_length
  · exact gramRow54_length
  · exact gramRow55_length
  · exact gramRow56_length
  · exact gramRow57_length
  · exact gramRow58_length
  · exact gramRow59_length
  · exact gramRow60_length
  · exact gramRow61_length
  · exact gramRow62_length
  · exact gramRow63_length
  · exact gramRow64_length
  · exact gramRow65_length
  · exact gramRow66_length
  · exact gramRow67_length
  · exact gramRow68_length
  · exact gramRow69_length
  · exact gramRow70_length
  · exact gramRow71_length
  · exact gramRow72_length
  · exact gramRow73_length
  · exact gramRow74_length
  · exact gramRow75_length
  · exact gramRow76_length
  · exact gramRow77_length
  · exact gramRow78_length
  · exact gramRow79_length
  · exact gramRow80_length
  · exact gramRow81_length
  · exact gramRow82_length
  · exact gramRow83_length
  · exact gramRow84_length
  · exact gramRow85_length
  · exact gramRow86_length
  · exact gramRow87_length
  · exact gramRow88_length
  · exact gramRow89_length
  · exact gramRow90_length
  · exact gramRow91_length
  · exact gramRow92_length
  · exact gramRow93_length
  · exact gramRow94_length
  · exact gramRow95_length
  · exact gramRow96_length
  · exact gramRow97_length

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Dense
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
