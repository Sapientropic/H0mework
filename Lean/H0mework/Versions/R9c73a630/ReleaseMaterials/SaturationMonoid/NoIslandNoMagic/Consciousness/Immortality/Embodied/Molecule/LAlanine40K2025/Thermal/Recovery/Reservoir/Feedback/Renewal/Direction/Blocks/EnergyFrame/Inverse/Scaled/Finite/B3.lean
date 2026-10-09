import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Constants

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite
open Propagation.Interface Load.Source Scaled.Order
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section

def block3 : Matrix (Fin 4) (Fin 4) ℂ :=
  !![(-3891080159059689583770132866141139290702359862394716286377929636663145691012311252164504702610165040256941093523016744658859174771997213913045742087/1663478637624633646628464728140170303644678153764820352314334410909925458341684948143623613024281753378255076321811784405999840823080562500000000000),0,0,0;
     0,(-432342171074507562964645175636153686433553740213908836928801227014417300143696647902257086879207178913285199491923735517651019419110801545893971343/184830959736070405180940525348907811516075350418313372479370490101102828704631660904847068113809083708695008480201309378444426758120062500000000000),1,0;
     0,1,(-564122883810422290513203409860798683413003554865075581749260814843294774328941355877257476561601533500430940879393175846859493125836088913045742087/1663478637624633646628464728140170303644678153764820352314334410909925458341684948143623613024281753378255076321811784405999840823080562500000000000),0;
     0,0,0,(-62680251602366752602764124938338063401403039377282091970060246812211642734433326092562950651589011495895182531521116760762165902870676545893971343/184830959736070405180940525348907811516075350418313372479370490101102828704631660904847068113809083708695008480201309378444426758120062500000000000)]

theorem source_block3 : diagonalOrdinary (Donor.calculatedEnergy 96)=block3.submatrix (finProdFinEquiv : Fin 2 × Fin 2 ≃ Fin 4) (finProdFinEquiv : Fin 2 × Fin 2 ≃ Fin 4) := by
  unfold diagonalOrdinary diagonalLoaded diagonalHpc
  simp only [numericEnvironmentRead,numericDonorEnergy,Donor.calculatedTop]
  rw [energy_96_exact,energy_97_exact,sine_hat_exact]
  ext ⟨c,e⟩ ⟨d,f⟩
  fin_cases c <;> fin_cases e <;> fin_cases d <;> fin_cases f <;>
    norm_num [block3,tripleIndex,Powered.Dynamics.totalHamiltonian,Powered.Dynamics.bareHamiltonian,Powered.Dynamics.controllerHamiltonian,smallExchange,controllerEnvironmentExchange,donorProjection,Matrix.submatrix_apply,Matrix.add_apply,Matrix.sub_apply,Matrix.smul_apply,Matrix.mul_apply,Matrix.kronecker,Matrix.kroneckerMap_apply,Matrix.single_apply,Fintype.sum_prod_type,Fin.sum_univ_two,finProdFinEquiv,Complex.real_smul]

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
