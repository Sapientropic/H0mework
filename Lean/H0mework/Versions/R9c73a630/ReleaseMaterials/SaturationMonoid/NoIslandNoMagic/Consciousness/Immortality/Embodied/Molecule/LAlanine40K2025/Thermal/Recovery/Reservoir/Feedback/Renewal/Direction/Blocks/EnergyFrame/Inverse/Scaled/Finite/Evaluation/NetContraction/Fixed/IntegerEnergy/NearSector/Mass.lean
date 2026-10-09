import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.MidSector.Mass
set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 0
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
open Propagation.Interface Load.Source Collision
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section

/-! Nine original unordered near addresses, with both source orientations retained. -/

def nearSlot (k : Fin 9) : Basis × Basis :=
  ![(0,1),(0,2),(0,3),(0,4),(0,5),(1,2),(1,3),(1,4),(1,5)] k

def nearA (k : Fin 9) : Basis := (nearSlot k).1
def nearB (k : Fin 9) : Basis := (nearSlot k).2

theorem near_ordered (k : Fin 9) : nearA k < nearB k := by
  fin_cases k <;> decide

def nearSectorEmbedding (s : Fin 9 × Fin 2) :
    PairSector (fun p => nearCond p.1 p.2) :=
  ⟨if s.2=0 then (nearA s.1,nearB s.1) else (nearB s.1,nearA s.1), by
    rcases s with ⟨k,o⟩
    fin_cases k <;> fin_cases o <;> decide⟩

theorem near_sector_embedding_bijective : Function.Bijective nearSectorEmbedding := by
  decide +kernel

def nearSectorPair (k : Fin 9) : Matrix (Fin 2) (Fin 2) ℂ :=
  Field.computedPair.submatrix (pairAddress (nearA k) (nearB k))
    (pairAddress (nearA k) (nearB k))

def nearSectorBody (k : Fin 9) : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  Matrix.kronecker (nearSectorPair k) environmentState

theorem near_sector_body_positive (k : Fin 9) : (nearSectorBody k).PosSemidef :=
  (computed_pair_positive.submatrix _).kronecker environmentState_positive

theorem near_sector_body_trace (k : Fin 9) :
    (nearSectorBody k).trace.re = (nearSectorPair k).trace.re := by
  rw [nearSectorBody]
  simp only [Matrix.kronecker,Matrix.trace_kronecker,environmentState_trace,mul_one]

theorem near_sector_body_mass_sum :
    (∑ k : Fin 9, (nearSectorBody k).trace.re) = nearComputedMass := by
  have sum (f : Basis × Basis → ℝ) := Fintype.sum_bijective nearSectorEmbedding
    near_sector_embedding_bijective (fun s => f (nearSectorEmbedding s).val)
    (fun p => f p.val) (fun _ => rfl)
  simp only [near_sector_body_trace]
  change _ = ∑ p : PairSector (fun p => nearCond p.1 p.2), (Field.computedPair p.val p.val).re
  rw [← sum (fun p : Basis × Basis => (Field.computedPair p p).re)]
  simp [nearSectorPair,Matrix.trace,Matrix.diag,Fintype.sum_prod_type,
    Fin.sum_univ_two,nearSectorEmbedding,pairAddress]

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
