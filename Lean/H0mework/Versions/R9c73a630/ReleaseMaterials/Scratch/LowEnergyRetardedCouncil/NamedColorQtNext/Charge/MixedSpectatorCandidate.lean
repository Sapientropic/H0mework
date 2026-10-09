import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.NamedColorQtNext.Charge.MixedSpectatorGram
import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceNamedMatterColorEpsilon
set_option autoImplicit false
noncomputable section
namespace LowEnergy.MixedSpectatorCandidate
open SourceQuantumConfigurationHilbert SourceQuantumFockGauge
open scoped BigOperators InnerProductSpace

def epsilon (dual : Bool) (spins : Fin 3 → Fin 4) : FockFiber :=
  ∑ p : Fin 6, NamedMatterWedgeQt.colorSign p •
    orderedTriple dual (spins 0, NamedMatterWedgeQt.colorPerm p 0, 0)
      (spins 1, NamedMatterWedgeQt.colorPerm p 1, 0)
      (spins 2, NamedMatterWedgeQt.colorPerm p 2, 1)

/-- A concrete source CAR vector: two color-hyperPlus factors and one
color-weak0 factor, with their original mother CAR phases. -/
def candidate (dual : Bool) : FockFiber :=
  (1/3 : ℂ) • (epsilon dual ![0,1,2] - epsilon dual ![0,0,3])

private theorem epsilon_pair (dual : Bool) (s t : Fin 3 → Fin 4) :
    inner ℂ (epsilon dual s) (epsilon dual t) =
      ∑ p : Fin 6, ∑ q : Fin 6,
        star (NamedMatterWedgeQt.colorSign p) * NamedMatterWedgeQt.colorSign q *
          tripleGram (s 0, NamedMatterWedgeQt.colorPerm p 0, 0)
            (s 1, NamedMatterWedgeQt.colorPerm p 1, 0)
            (s 2, NamedMatterWedgeQt.colorPerm p 2, 1)
            (t 0, NamedMatterWedgeQt.colorPerm q 0, 0)
            (t 1, NamedMatterWedgeQt.colorPerm q 1, 0)
            (t 2, NamedMatterWedgeQt.colorPerm q 2, 1) := by
  simp only [epsilon, sum_inner, inner_sum, inner_smul_left, inner_smul_right,
    actual_ordered_triple_pair, starRingEnd_apply, Finset.mul_sum, ←mul_assoc]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro q _
  ring

theorem actual_candidate_norm_sq (dual : Bool) :
    inner ℂ (candidate dual) (candidate dual) = 2 := by
  simp only [candidate, inner_smul_left, inner_smul_right, inner_sub_left,
    inner_sub_right, epsilon_pair]
  norm_num [Fin.sum_univ_succ, NamedMatterWedgeQt.colorSign,
    NamedMatterWedgeQt.colorPerm, tripleGram, delta, Prod.mk.injEq]
  simp +decide
  norm_num [starRingEnd_apply]

theorem actual_candidate_nonzero (dual : Bool) : candidate dual ≠ 0 := by
  intro h
  have hn := actual_candidate_norm_sq dual
  rw [h, inner_zero_left] at hn
  norm_num at hn

end LowEnergy.MixedSpectatorCandidate
