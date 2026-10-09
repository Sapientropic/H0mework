import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1Deformation.EnergyDefs

set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 100000

namespace CPS1Deformation
noncomputable section
open CPS1ElectronicSource MeasureTheory
open scoped BigOperators InnerProductSpace Matrix
variable {frame : CPS1Recycling.Frame}

theorem primitive_nuclear_star (left right nuclear : Point) (i j : Nat) :
    star (CPS1MolecularFrame.primitiveNuclearIntegral left right i j nuclear 0 0) =
      CPS1MolecularFrame.primitiveNuclearIntegral right left j i nuclear 0 0 := by
  unfold CPS1MolecularFrame.primitiveNuclearIntegral
  rw [Complex.star_def,← integral_conj]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by
    simp only [map_mul,Complex.conj_ofReal,Complex.conj_conj]
    ring

theorem primitive_pair_star (first second third fourth : Point) (i j k l : Nat) :
    star (CPS1MolecularFrame.primitivePairIntegral first second third fourth i j k l 0 0 0 0) =
      CPS1MolecularFrame.primitivePairIntegral second first fourth third j i l k 0 0 0 0 := by
  unfold CPS1MolecularFrame.primitivePairIntegral
  rw [Complex.star_def,← integral_conj]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun z => by
    simp only [map_mul,Complex.conj_ofReal,Complex.conj_conj]
    ring

theorem primitive_pair_swap (first second third fourth : Point) (i j k l : Nat) :
    CPS1MolecularFrame.primitivePairIntegral first second third fourth i j k l 0 0 0 0 =
      CPS1MolecularFrame.primitivePairIntegral third fourth first second k l i j 0 0 0 0 := by
  unfold CPS1MolecularFrame.primitivePairIntegral
  rw [← integral_prod_swap]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun z => by
    dsimp only [Prod.swap]
    rw [CPS1ElectronicSource.coulomb_kernel_sub_comm z.2 z.1]
    ring

theorem raw_nuclear_star (source : CPS1ElectronicSource.State frame) (positions : NuclearConfiguration source)
    (p q : CPS1MolecularFrame.PrimitiveIndex source) (spin : Bool) (nuclear : Point) :
    star (rawNuclearIntegralAt source positions p q 0 0 spin nuclear) =
      rawNuclearIntegralAt source positions q p 0 0 spin nuclear := by
  unfold rawNuclearIntegralAt
  by_cases present : p.2 = spin ∧ q.2 = spin
  · rw [if_pos present,if_pos ⟨present.2,present.1⟩]
    exact primitive_nuclear_star _ _ _ _ _
  · have absent : ¬ (q.2 = spin ∧ p.2 = spin) := fun matched => present ⟨matched.2,matched.1⟩
    rw [if_neg present,if_neg absent,star_zero]

theorem raw_pair_star (source : CPS1ElectronicSource.State frame) (positions : NuclearConfiguration source)
    (p q r s : CPS1MolecularFrame.PrimitiveIndex source) (spin secondSpin : Bool) :
    star (rawPairIntegralAt source positions p q r s spin secondSpin) =
      rawPairIntegralAt source positions q p s r spin secondSpin := by
  unfold rawPairIntegralAt
  by_cases present : p.2 = spin ∧ q.2 = spin ∧ r.2 = secondSpin ∧ s.2 = secondSpin
  · rw [if_pos present,if_pos ⟨present.2.1,present.1,present.2.2.2,present.2.2.1⟩]
    exact primitive_pair_star _ _ _ _ _ _ _ _
  · have absent : ¬ (q.2 = spin ∧ p.2 = spin ∧ s.2 = secondSpin ∧ r.2 = secondSpin) :=
      fun matched => present ⟨matched.2.1,matched.1,matched.2.2.2,matched.2.2.1⟩
    rw [if_neg present,if_neg absent,star_zero]

theorem raw_pair_swap (source : CPS1ElectronicSource.State frame) (positions : NuclearConfiguration source)
    (p q r s : CPS1MolecularFrame.PrimitiveIndex source) (spin secondSpin : Bool) :
    rawPairIntegralAt source positions p q r s spin secondSpin =
      rawPairIntegralAt source positions r s p q secondSpin spin := by
  unfold rawPairIntegralAt
  by_cases present : p.2 = spin ∧ q.2 = spin ∧ r.2 = secondSpin ∧ s.2 = secondSpin
  · rw [if_pos present,if_pos ⟨present.2.2.1,present.2.2.2,present.1,present.2.1⟩]
    exact primitive_pair_swap _ _ _ _ _ _ _ _
  · have absent : ¬ (r.2 = secondSpin ∧ s.2 = secondSpin ∧ p.2 = spin ∧ q.2 = spin) :=
      fun matched => present ⟨matched.2.2.1,matched.2.2.2,matched.1,matched.2.1⟩
    rw [if_neg present,if_neg absent]

theorem nuclear_integral_star (source : CPS1ElectronicSource.State frame) (positions : NuclearConfiguration source)
    (i j : CPS1MolecularFrame.ActualIndex source) (nuclear : Point) :
    star (nuclearIntegralAt source positions i j nuclear) = nuclearIntegralAt source positions j i nuclear := by
  simp only [nuclearIntegralAt,star_sum,star_mul,star_star,raw_nuclear_star]
  apply Finset.sum_congr rfl
  intro spin _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro q _
  ring

theorem pair_integral_star (source : CPS1ElectronicSource.State frame) (positions : NuclearConfiguration source)
    (i j k l : CPS1MolecularFrame.ActualIndex source) (spin secondSpin : Bool) :
    star (pairIntegralAt source positions i j k l spin secondSpin) =
      pairIntegralAt source positions j i l k spin secondSpin := by
  simp only [pairIntegralAt,star_sum,star_mul,star_star,raw_pair_star]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro q _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r _
  apply Finset.sum_congr rfl
  intro s _
  ring

theorem sum_four_blocks {I : Type*} [Fintype I] (field : I → I → I → I → ℂ) :
    (∑ p, ∑ q, ∑ r, ∑ s, field p q r s) = ∑ r, ∑ s, ∑ p, ∑ q, field p q r s := by
  calc
    _ = ∑ p, ∑ r, ∑ q, ∑ s, field p q r s := by
      apply Finset.sum_congr rfl
      intro p _
      rw [Finset.sum_comm]
    _ = ∑ r, ∑ p, ∑ q, ∑ s, field p q r s := by rw [Finset.sum_comm]
    _ = ∑ r, ∑ p, ∑ s, ∑ q, field p q r s := by
      apply Finset.sum_congr rfl
      intro r _
      apply Finset.sum_congr rfl
      intro p _
      rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro r _
      rw [Finset.sum_comm]

theorem pair_integral_swap (source : CPS1ElectronicSource.State frame) (positions : NuclearConfiguration source)
    (i j k l : CPS1MolecularFrame.ActualIndex source) (spin secondSpin : Bool) :
    pairIntegralAt source positions i j k l spin secondSpin =
      pairIntegralAt source positions k l i j secondSpin spin := by
  simp only [pairIntegralAt]
  rw [sum_four_blocks]
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro q _
  apply Finset.sum_congr rfl
  intro r _
  apply Finset.sum_congr rfl
  intro s _
  rw [raw_pair_swap source positions r s p q spin secondSpin]
  ring

theorem two_body_star (source : CPS1ElectronicSource.State frame) (positions : NuclearConfiguration source)
    (i j k l : CPS1MolecularFrame.ActualIndex source) :
    star (twoBodyAt source positions i j k l) = twoBodyAt source positions k l i j := by
  simp only [twoBodyAt,star_sum,pair_integral_star]

theorem two_body_swap (source : CPS1ElectronicSource.State frame) (positions : NuclearConfiguration source)
    (i j k l : CPS1MolecularFrame.ActualIndex source) :
    twoBodyAt source positions i j k l = twoBodyAt source positions j i l k := by
  simp only [twoBodyAt,pair_integral_swap]
  rw [Finset.sum_comm]

theorem kinetic_star (source : CPS1ElectronicSource.State frame) (positions : NuclearConfiguration source)
    (i j : CPS1MolecularFrame.ActualIndex source) :
    star (kineticAt source positions i j) = kineticAt source positions j i := by
  unfold kineticAt
  simp only [Complex.star_def,map_mul,map_sum,Complex.conj_ofReal]
  apply congrArg (fun z : ℂ => ((1/(2*source.geometry.electronInertia) : ℝ) : ℂ)*z)
  apply Finset.sum_congr rfl
  intro axis _
  exact inner_conj_symm _ _

theorem core_hermitian (source : CPS1ElectronicSource.State frame) (positions : NuclearConfiguration source) :
    (coreAt source positions).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  have attraction : star (attractionAt source positions j i) = attractionAt source positions i j := by
    simp only [attractionAt,List.sum_ofFn,star_sum,star_mul,star_neg,
      nuclear_integral_star,star_intCast]
    apply Finset.sum_congr rfl
    intro nuclear _
    ring
  simp only [coreAt,star_add,kinetic_star,attraction]

theorem physical_fock_hermitian (source : CPS1ElectronicSource.State frame)
    (positions : NuclearConfiguration source) (occupied : OccupiedConfiguration source) :
    (physicalFockAt source positions occupied).IsHermitian := by
  classical
  apply Matrix.IsHermitian.ext
  intro i k
  have coreStar : star (coreAt source positions k i) = coreAt source positions i k :=
    (core_hermitian source positions).apply i k
  have densityStar (j l : CPS1MolecularFrame.ActualIndex source) :
      star (densityAt source occupied l j) = densityAt source occupied j l :=
    (Matrix.isHermitian_mul_conjTranspose_self occupied).apply j l
  simp only [physicalFockAt,star_add,star_sum,star_mul,star_sub,coreStar,densityStar,two_body_star]
  rw [Finset.sum_comm]
  apply congrArg (fun z : ℂ => coreAt source positions i k+z)
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro l _
  rw [two_body_swap source positions j i k l]
  ring

end
end CPS1Deformation
