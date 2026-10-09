import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1ElectronicSource.Coulomb
import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1ElectronicSource.Orbitals

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace CPS1ElectronicSource
noncomputable section
open MeasureTheory
open SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement
open scoped BigOperators

theorem normalized_nuclear_integrable (centre : Point) (n : Nat) (i j : Fin n) (nuclear : Point)
    (jetI jetJ : Fin 3 → Nat) :
    Integrable (fun x : Point => SourceCoulomb.kernel (x-nuclear) •
      (star (spatialValue centre n i jetI x) * spatialValue centre n j jetJ x)) (volume : Measure Point) := by
  classical
  have each (a b : Fin n) : Integrable (fun x : Point =>
      (star (coefficients centre n a i) * coefficients centre n b j) *
        (SourceCoulomb.kernel (x-nuclear) •
          (star (orbitalValue centre a.val jetI x) * orbitalValue centre b.val jetJ x)))
      (volume : Measure Point) :=
    (primitive_nuclear_integrable centre a.val b.val nuclear jetI jetJ).const_mul _
  have total := integrable_finsetSum Finset.univ (fun b _ =>
    integrable_finsetSum Finset.univ (fun a _ => each a b))
  convert! total using 1
  funext x
  simp only [spatialValue,star_sum,star_mul,Algebra.smul_def,Finset.sum_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro a _
  ring

theorem normalized_pair_integrable (centre : Point) (n : Nat) (i j k l : Fin n) :
    Integrable (fun z : Point × Point =>
      (SourceCoulomb.kernel (z.1-z.2) : ℂ) *
        star (spatialValue centre n i 0 z.1) * spatialValue centre n j 0 z.1 *
        star (spatialValue centre n k 0 z.2) * spatialValue centre n l 0 z.2)
      ((volume : Measure Point).prod volume) := by
  classical
  have each (a b c d : Fin n) : Integrable (fun z : Point × Point =>
      (star (coefficients centre n a i) * coefficients centre n b j *
        star (coefficients centre n c k) * coefficients centre n d l) *
        ((SourceCoulomb.kernel (z.1-z.2) : ℂ) *
          star (orbitalValue centre a.val 0 z.1) * orbitalValue centre b.val 0 z.1 *
          star (orbitalValue centre c.val 0 z.2) * orbitalValue centre d.val 0 z.2))
      ((volume : Measure Point).prod volume) :=
    (primitive_pair_integrable centre a.val b.val c.val d.val).const_mul _
  have total := integrable_finsetSum Finset.univ (fun d _ =>
    integrable_finsetSum Finset.univ (fun c _ =>
      integrable_finsetSum Finset.univ (fun b _ =>
        integrable_finsetSum Finset.univ (fun a _ => each a b c d))))
  convert! total using 1
  funext z
  simp only [spatialValue,star_sum,star_mul,Finset.sum_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d _
  apply Finset.sum_congr rfl
  intro c _
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro a _
  ring

end
end CPS1ElectronicSource
