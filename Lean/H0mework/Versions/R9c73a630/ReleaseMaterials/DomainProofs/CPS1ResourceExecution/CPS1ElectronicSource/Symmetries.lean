import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1ElectronicSource.Integrals
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Prod

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace CPS1ElectronicSource
noncomputable section
open MeasureTheory
open SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement
open scoped BigOperators InnerProductSpace Matrix
variable {frame : CPS1Recycling.Frame}

theorem nuclear_star (centre : Point) (n : Nat) (i j : Fin n) (nucleus : Point) :
    star (nuclearIntegral centre n i j nucleus) = nuclearIntegral centre n j i nucleus := by
  unfold nuclearIntegral
  rw [Complex.star_def,← integral_conj]
  apply integral_congr_ae
  filter_upwards [] with x
  simp only [map_mul,Complex.conj_ofReal,Complex.conj_conj]
  ring

theorem pair_star (centre : Point) (n : Nat) (i j k l : Fin n) :
    star (pairIntegral centre n i j k l) = pairIntegral centre n j i l k := by
  unfold pairIntegral
  rw [Complex.star_def,← integral_conj]
  apply integral_congr_ae
  filter_upwards [] with z
  simp only [map_mul,Complex.conj_ofReal,Complex.conj_conj]
  ring

theorem pair_swap (centre : Point) (n : Nat) (i j k l : Fin n) :
    pairIntegral centre n i j k l = pairIntegral centre n k l i j := by
  unfold pairIntegral
  rw [← integral_prod_swap (fun z : Point × Point =>
    (SourceCoulomb.kernel (z.1-z.2) : ℂ) *
      star (spatialValue centre n i 0 z.1) * spatialValue centre n j 0 z.1 *
      star (spatialValue centre n k 0 z.2) * spatialValue centre n l 0 z.2)]
  apply integral_congr_ae
  filter_upwards [] with z
  change (SourceCoulomb.kernel (z.2-z.1) : ℂ) *
      star (spatialValue centre n i 0 z.2) * spatialValue centre n j 0 z.2 *
      star (spatialValue centre n k 0 z.1) * spatialValue centre n l 0 z.1 =
    (SourceCoulomb.kernel (z.1-z.2) : ℂ) *
      star (spatialValue centre n k 0 z.1) * spatialValue centre n l 0 z.1 *
      star (spatialValue centre n i 0 z.2) * spatialValue centre n j 0 z.2
  rw [coulomb_kernel_sub_comm z.2 z.1]
  ring

theorem kinetic_star (geometry : Geometry frame) (i j : SpatialIndex geometry) :
    star (kinetic geometry i j) = kinetic geometry j i := by
  unfold kinetic
  simp only [Complex.star_def,map_mul,map_sum,Complex.conj_ofReal]
  apply congrArg (fun z : ℂ => ((1/(2*geometry.electronInertia) : ℝ) : ℂ) * z)
  apply Finset.sum_congr rfl
  intro axis _
  exact inner_conj_symm _ _

theorem attraction_star (geometry : Geometry frame) (i j : SpatialIndex geometry) :
    star (attraction geometry i j) = attraction geometry j i := by
  unfold attraction
  induction geometry.nuclei with
  | nil => simp
  | cons nucleus rest ih =>
    simp only [List.map_cons,List.sum_cons,star_add,star_mul,star_neg]
    rw [ih,nuclear_star]
    have realCharge : star (nucleus.particle.charge : ℂ) = (nucleus.particle.charge : ℂ) := by simp
    rw [realCharge]
    ring

theorem core_hermitian (geometry : Geometry frame) : (core geometry).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  by_cases same : i.2 = j.2
  · simp only [core,if_pos same,if_pos same.symm,star_add,kinetic_star,attraction_star]
  · simp only [core,if_neg same,if_neg (Ne.symm same),star_zero]

theorem twoBody_star (geometry : Geometry frame) (i j k l : SpinIndex geometry) :
    star (twoBody geometry i j k l) = twoBody geometry k l i j := by
  by_cases same : i.2 = k.2 ∧ j.2 = l.2
  · have reversed : k.2 = i.2 ∧ l.2 = j.2 := ⟨same.1.symm,same.2.symm⟩
    simp only [twoBody,if_pos same,if_pos reversed,pair_star]
  · have reversed : ¬(k.2 = i.2 ∧ l.2 = j.2) := fun h => same ⟨h.1.symm,h.2.symm⟩
    simp only [twoBody,if_neg same,if_neg reversed,star_zero]

theorem twoBody_swap (geometry : Geometry frame) (i j k l : SpinIndex geometry) :
    twoBody geometry i j k l = twoBody geometry j i l k := by
  by_cases same : i.2 = k.2 ∧ j.2 = l.2
  · have reversed : j.2 = l.2 ∧ i.2 = k.2 := ⟨same.2,same.1⟩
    simp only [twoBody,if_pos same,if_pos reversed]
    exact pair_swap _ _ _ _ _ _
  · have reversed : ¬(j.2 = l.2 ∧ i.2 = k.2) := fun h => same ⟨h.2,h.1⟩
    simp only [twoBody,if_neg same,if_neg reversed]

theorem fock_hermitian (geometry : Geometry frame)
    (density : Matrix (SpinIndex geometry) (SpinIndex geometry) ℂ) (hermitian : density.IsHermitian) :
    (fock geometry density).IsHermitian := by
  classical
  apply Matrix.IsHermitian.ext
  intro i k
  have coreStar : star (core geometry k i) = core geometry i k := (core_hermitian geometry).apply i k
  have densityStar (j l : SpinIndex geometry) : star (density l j) = density j l := hermitian.apply j l
  simp only [fock,star_add,star_sum,star_mul,star_sub,coreStar,densityStar,twoBody_star]
  rw [Finset.sum_comm]
  apply congrArg (fun z : ℂ => core geometry i k + z)
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro l _
  rw [twoBody_swap geometry j i k l]
  ring

end
end CPS1ElectronicSource
