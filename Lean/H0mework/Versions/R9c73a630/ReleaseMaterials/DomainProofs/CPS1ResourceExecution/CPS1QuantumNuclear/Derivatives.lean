import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1QuantumNuclear.Integral
import Mathlib.Analysis.Complex.RealDeriv

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace CPS1QuantumNuclear
noncomputable section
open CPS1ElectronicSource
open SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025
open BasinRefinement SourceGaussianModel ReceiverBody.NuclearCoulomb
open scoped BigOperators

def primitiveGradient (left right : Nat) (centre nucleus : Point) (axis : Fin 3) : ℝ :=
  primitiveAttraction (primitive left) (primitive right) (raise 0 axis) 0 (centre-nucleus) (centre-nucleus) +
    primitiveAttraction (primitive right) (primitive left) (raise 0 axis) 0 (centre-nucleus) (centre-nucleus)

theorem primitive_rate_linear (left right : Nat) (centre nucleus direction : Point) :
    primitiveAttractionRate (primitive left) (primitive right) 0 0
      (centre-nucleus) (centre-nucleus) (-direction) (-direction) =
      ∑ axis : Fin 3, direction axis * primitiveGradient left right centre nucleus axis := by
  simp only [primitiveAttractionRate,Pi.neg_apply,neg_mul,Finset.sum_neg_distrib,neg_neg,primitiveGradient,mul_add,
    Finset.sum_add_distrib]

def nuclearRate (centre : Point) (n : Nat) (i j : Fin n) (nucleus direction : Point) : ℂ :=
  ∑ b : Fin n, ∑ a : Fin n, (star (coefficients centre n a i) * coefficients centre n b j) *
    (primitiveAttractionRate (primitive a.val) (primitive b.val) 0 0
      (centre-nucleus) (centre-nucleus) (-direction) (-direction) : ℂ)

def nuclearGradient (centre : Point) (n : Nat) (i j : Fin n) (nucleus : Point) (axis : Fin 3) : ℂ :=
  ∑ b : Fin n, ∑ a : Fin n, (star (coefficients centre n a i) * coefficients centre n b j) *
    (primitiveGradient a.val b.val centre nucleus axis : ℂ)

theorem nuclear_rate_linear (centre : Point) (n : Nat) (i j : Fin n) (nucleus direction : Point) :
    nuclearRate centre n i j nucleus direction =
      ∑ axis : Fin 3, (direction axis : ℂ) * nuclearGradient centre n i j nucleus axis := by
  unfold nuclearRate nuclearGradient
  simp only [primitive_rate_linear,Complex.ofReal_sum,Complex.ofReal_mul,Finset.mul_sum]
  calc
    _ = ∑ b : Fin n, ∑ axis : Fin 3, ∑ a : Fin n,
        (star (coefficients centre n a i) * coefficients centre n b j) *
          ((direction axis : ℂ) * (primitiveGradient a.val b.val centre nucleus axis : ℂ)) := by
      apply Finset.sum_congr rfl
      intro b _
      rw [Finset.sum_comm]
    _ = ∑ axis : Fin 3, ∑ b : Fin n, ∑ a : Fin n,
        (star (coefficients centre n a i) * coefficients centre n b j) *
          ((direction axis : ℂ) * (primitiveGradient a.val b.val centre nucleus axis : ℂ)) := by
      rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro axis _
      apply Finset.sum_congr rfl
      intro b _
      apply Finset.sum_congr rfl
      intro a _
      ring

theorem normalized_nuclear_line (centre : Point) (n : Nat) (i j : Fin n) (nucleus direction : Point) :
    HasDerivAt (fun time : ℝ => nuclearIntegral centre n i j (nucleus+time • direction))
      (nuclearRate centre n i j nucleus direction) 0 := by
  have generated := HasDerivAt.fun_sum (u := Finset.univ) (fun b _ =>
    HasDerivAt.fun_sum (u := Finset.univ) (fun a _ =>
      ((primitive_nuclear_line a.val b.val centre nucleus direction).ofReal_comp).const_mul
        (star (coefficients centre n a i) * coefficients centre n b j)))
  have same : (fun time : ℝ => nuclearIntegral centre n i j (nucleus+time • direction)) =
      fun time => ∑ b : Fin n, ∑ a : Fin n,
        (star (coefficients centre n a i) * coefficients centre n b j) *
          (primitiveAttraction (primitive a.val) (primitive b.val) 0 0
            (centre-(nucleus+time • direction)) (centre-(nucleus+time • direction)) : ℂ) :=
    funext (fun _ => normalized_integral_expansion centre n i j _)
  rw [same]
  exact generated

end
end CPS1QuantumNuclear
