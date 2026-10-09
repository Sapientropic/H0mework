import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.InputProducts.SystemMiddle.Values
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.InputProducts.SystemFinal.Values
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.InputProducts.BathMiddle.Values
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.InputProducts.BathFinal.Values
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.InputProducts.ProductAlgebra

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.InputProducts
open Spectral Propagation.Interface
open scoped Matrix BigOperators Matrix.Norms.L2Operator
noncomputable section

def systemMiddleR : Matrix Basis Basis Int := Rows.rowMatrix Products.systemMiddleRRows
def systemMiddleI : Matrix Basis Basis Int := Rows.rowMatrix Products.systemMiddleIRows
def systemMiddle : Matrix Basis Basis ℂ := scaledMatrix systemMiddleR systemMiddleI (10^24)

def systemR : Matrix Basis Basis Int := Rows.rowMatrix Products.systemRRows
def systemI : Matrix Basis Basis Int := Rows.rowMatrix Products.systemIRows
def system : Matrix Basis Basis ℂ := scaledMatrix systemR systemI (10^24)

def bathMiddleR : Matrix Basis Basis Int := Rows.rowMatrix Products.bathMiddleRRows
def bathMiddleI : Matrix Basis Basis Int := Rows.rowMatrix Products.bathMiddleIRows
def bathMiddle : Matrix Basis Basis ℂ := scaledMatrix bathMiddleR bathMiddleI (10^24)

def bathR : Matrix Basis Basis Int := Rows.rowMatrix Products.bathRRows
def bathI : Matrix Basis Basis Int := Rows.rowMatrix Products.bathIRows
def bath : Matrix Basis Basis ℂ := scaledMatrix bathR bathI (10^24)


end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.InputProducts
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
