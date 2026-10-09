import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceNamedMatterQt

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.NamedMatterWedgeQt
open SourceQuantumConfigurationHilbert SourceQuantumFockGauge
open SaturationMonoid.PhysicsCore QuantizationCheck.Fermion
open scoped BigOperators InnerProductSpace
attribute [local instance] SourceRealScalarFock.branchOrder
local instance : DecidableEq Mode := SourceRealScalarFock.branchOrder.toDecidableEq

abbrev SpinTriple := {s : Fin 3 → Fin 4 // s 0 ≤ s 1 ∧ s 1 ≤ s 2}

theorem actual_spin_triple_card : Fintype.card SpinTriple = 20 := by decide

def colorPerm (p : Fin 6) (i : Fin 3) : Fin 3 :=
  match p.val, i.val with
  | 0, 0 => 0 | 0, 1 => 1 | 0, _ => 2
  | 1, 0 => 0 | 1, 1 => 2 | 1, _ => 1
  | 2, 0 => 1 | 2, 1 => 0 | 2, _ => 2
  | 3, 0 => 1 | 3, 1 => 2 | 3, _ => 0
  | 4, 0 => 2 | 4, 1 => 0 | 4, _ => 1
  | _, 0 => 2 | _, 1 => 1 | _, _ => 0

def colorSign (p : Fin 6) : ℂ :=
  if p = 0 ∨ p = 3 ∨ p = 4 then 1 else -1

def epsilonTerm (dual : Bool) (s : SpinTriple) (p : Fin 6) : FockFiber :=
  orderedTriple dual (s.val 0, colorPerm p 0) (s.val 1, colorPerm p 1)
    (s.val 2, colorPerm p 2)

def epsilonFiber (dual : Bool) (s : SpinTriple) : FockFiber :=
  ∑ p : Fin 6, colorSign p • epsilonTerm dual s p

theorem actual_epsilon_term_source (dual : Bool) (s : SpinTriple) (p : Fin 6) :
    epsilonTerm dual s p =
      (sign (rootMode dual (s.val 1, colorPerm p 1))
          {rootMode dual (s.val 2, colorPerm p 2)} *
        sign (rootMode dual (s.val 0, colorPerm p 0))
          {rootMode dual (s.val 1, colorPerm p 1), rootMode dual (s.val 2, colorPerm p 2)}) •
      occupationFiber dual {(s.val 0, colorPerm p 0), (s.val 1, colorPerm p 1),
        (s.val 2, colorPerm p 2)} := by
  unfold epsilonTerm
  apply actual_ordered_triple
  all_goals
    intro h
    have e := congrArg (fun a : NamedMode => a.2.val) h
    fin_cases p <;> norm_num [colorPerm] at e

theorem actual_epsilon_three_particle (dual : Bool) (s : SpinTriple) (v : Occupation)
    (hv : v.card ≠ 3) : epsilonFiber dual s v = 0 := by
  classical
  simp only [epsilonFiber, WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply]
  apply Finset.sum_eq_zero
  intro p _
  rw [actual_epsilon_term_source]
  have hn : v ≠ occupation dual
      {(s.val 0, colorPerm p 0), (s.val 1, colorPerm p 1), (s.val 2, colorPerm p 2)} := by
    intro h
    apply hv
    rw [h, occupation_card]
    fin_cases p <;> simp [colorPerm, Prod.mk.injEq]
  simp [occupationFiber, EuclideanSpace.single, hn]

end LowEnergy.NamedMatterWedgeQt
