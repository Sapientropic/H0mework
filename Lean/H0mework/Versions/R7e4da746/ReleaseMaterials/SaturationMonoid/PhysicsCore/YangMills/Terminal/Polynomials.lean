import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.PhysicsCore.YangMills.Terminal.Gauge
import Mathlib.Analysis.Normed.Module.Multilinear.Basic

/-! Actual curvature differential-polynomial labels for the terminal gauge
field correspondence. Invariance is imposed on tensors via the adjoint Lie action. -/

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.YangMills.Terminal

noncomputable section

def axis (i : Fin 4) : GaugeSpacetime := EuclideanSpace.single i 1

structure CurvatureAddress where
  derivatives : List (Fin 4)
  first : Fin 4
  second : Fin 4

def covariantWord (G : GaugeGroup) (A : Connection G)
    (directions : List (Fin 4)) (field : GaugeSpacetime → G.Algebra) :
    GaugeSpacetime → G.Algebra :=
  directions.foldr (fun direction current x => covariantDerivative G A current x (axis direction)) field

def curvatureJet (G : GaugeGroup) (A : Connection G) (address : CurvatureAddress) :
    GaugeSpacetime → G.Algebra :=
  covariantWord G A address.derivatives
    (fun x => curvature G A x (axis address.first) (axis address.second))

def InvariantTensor (G : GaugeGroup) (arity : ℕ) :=
  {tensor : ContinuousMultilinearMap ℝ (fun _ : Fin arity => G.Algebra) ℝ //
    ∀ generator : G.Algebra, ∀ values : Fin arity → G.Algebra,
      ∑ index : Fin arity, tensor (Function.update values index ⁅generator, values index⁆) = 0}

structure PolynomialTerm (G : GaugeGroup) where
  arity : ℕ
  tensor : InvariantTensor G arity
  addresses : Fin arity → CurvatureAddress

def PolynomialTerm.dimension {G : GaugeGroup} (term : PolynomialTerm G) : ℕ :=
  ∑ index : Fin term.arity, (2 + (term.addresses index).derivatives.length)

def PolynomialTerm.evaluate {G : GaugeGroup} (term : PolynomialTerm G) :
    Connection G × GaugeSpacetime → ℝ :=
  fun pair => term.tensor.val (fun index => curvatureJet G pair.1 (term.addresses index) pair.2)

/-- Finite real linear combinations of actual invariant curvature contractions. -/
def differentialPolynomials (G : GaugeGroup) : Submodule ℝ (Connection G × GaugeSpacetime → ℝ) :=
  Submodule.span ℝ (Set.range (fun term : PolynomialTerm G => term.evaluate))

def polynomialsAtMost (G : GaugeGroup) (dimension : ℕ) :
    Submodule ℝ (Connection G × GaugeSpacetime → ℝ) :=
  Submodule.span ℝ {value | ∃ term : PolynomialTerm G,
    term.dimension ≤ dimension ∧ value = term.evaluate}

theorem polynomialsAtMost_le (G : GaugeGroup) (dimension : ℕ) :
    polynomialsAtMost G dimension ≤ differentialPolynomials G := by
  apply Submodule.span_mono
  rintro value ⟨term, _, rfl⟩
  exact ⟨term, rfl⟩

theorem polynomialsAtMost_mono (G : GaugeGroup) : Monotone (polynomialsAtMost G) := by
  intro first second leq
  apply Submodule.span_mono
  rintro value ⟨term, bound, same⟩
  exact ⟨term, bound.trans leq, same⟩

end
end SaturationMonoid.PhysicsCore.YangMills.Terminal
