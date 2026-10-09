import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Constants

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite
open Propagation.Interface Load.Source Scaled.Order
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section

def block2 : Matrix (Fin 4) (Fin 4) ℂ :=
  !![(-607370321186894494646236001695259923824846778872378763726877129200180511660026504531219950673615916452484677006167368345810576907206943157679296578857/13307829100997069173027717825121362429157425230118562818514675287279403666733479585148988904194254027026040610574494275247998726584644500000000000000),0,0,0;
     0,(-67485590692420169167725487934659319435827085474291385521636375605768154638030463684762935923115279223576186957933527038423397434134104795297699619873/1478647677888563241447524202791262492128602803346506979834963920808822629637053287238776544910472669669560067841610475027555414064960500000000000000),1,0;
     0,1,(-580754662984900356300180566045017198966531928412141638089847778625621704326559545360921972865227408398432595785018379795314579454037654157679296578857/13307829100997069173027717825121362429157425230118562818514675287279403666733479585148988904194254027026040610574494275247998726584644500000000000000),0;
     0,0,0,(-64528295336643042684830439529076794451569879867598371561966447764150509378756357110285382833294333884237066822250306088368286606004183795297699619873/1478647677888563241447524202791262492128602803346506979834963920808822629637053287238776544910472669669560067841610475027555414064960500000000000000)]

theorem source_block2 : diagonalOrdinary (Donor.calculatedEnergy 0)=block2.submatrix (finProdFinEquiv : Fin 2 × Fin 2 ≃ Fin 4) (finProdFinEquiv : Fin 2 × Fin 2 ≃ Fin 4) := by
  unfold diagonalOrdinary diagonalLoaded diagonalHpc
  simp only [numericEnvironmentRead,numericDonorEnergy,Donor.calculatedTop]
  rw [energy_0_exact,energy_97_exact,sine_hat_exact]
  ext ⟨c,e⟩ ⟨d,f⟩
  fin_cases c <;> fin_cases e <;> fin_cases d <;> fin_cases f <;>
    norm_num [block2,tripleIndex,Powered.Dynamics.totalHamiltonian,Powered.Dynamics.bareHamiltonian,Powered.Dynamics.controllerHamiltonian,smallExchange,controllerEnvironmentExchange,donorProjection,Matrix.submatrix_apply,Matrix.add_apply,Matrix.sub_apply,Matrix.smul_apply,Matrix.mul_apply,Matrix.kronecker,Matrix.kroneckerMap_apply,Matrix.single_apply,Fintype.sum_prod_type,Fin.sum_univ_two,finProdFinEquiv,Complex.real_smul]

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
