import H0mework.Chemistry.LAlanineElectronicFrame.SourceElectronicFrameParsing

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.ElectronicFrame.Source

open Lean Elab Term
open Propagation.Interface
open LAlanine40K2025.ElectronicFrame.SourceParsing

elab "lalanineCrossInput%" : term => do
  Meta.mkAppM ``matrixRead #[toExpr (← crossRows (← verifiedPacket))]

elab "lalanineTargetFrame%" : term => do
  targetSourceExpr (← verifiedPacket)

noncomputable def crossNumerator : Matrix Basis Basis Int := lalanineCrossInput%

noncomputable def crossMatrix : Matrix Basis Basis ℂ :=
  fun left right => (crossNumerator left right : ℂ) / 1000000000000000

noncomputable def currentElectronicSource : ElectronicPropagationSource := Propagation.Source.electronicSource

noncomputable def targetElectronicSource : ElectronicPropagationSource := lalanineTargetFrame%

theorem currentElectronicSource_eq_parent :
    currentElectronicSource = Propagation.Source.electronicSource := rfl

end LAlanine40K2025.ElectronicFrame.Source
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
