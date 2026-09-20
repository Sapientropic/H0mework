import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Topology.ContinuousMap.StoneWeierstrass
import Mathlib.Topology.UniformSpace.CompactConvergence
import Mathlib.Topology.UniformSpace.Completion
import Mathlib.Topology.Instances.Real.Lemmas

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherLawCompletion

open scoped Topology
open Set Filter

noncomputable section

def scalarPolynomial {ι : Type*} (p : MvPolynomial ι ℚ) : C((ι → ℝ), ℝ) where
  toFun x := MvPolynomial.eval₂ (algebraMap ℚ ℝ) x p
  continuous_toFun := by
    simpa only [MvPolynomial.eval_map] using
      (MvPolynomial.map (algebraMap ℚ ℝ) p).continuous_eval

def readPolynomials (n m : ℕ) (p : Fin m → MvPolynomial (Fin n) ℚ) :
    C((Fin n → ℝ), (Fin m → ℝ)) where
  toFun x i := scalarPolynomial (p i) x
  continuous_toFun := continuous_pi fun i => (scalarPolynomial (p i)).continuous

@[simp] theorem readPolynomials_apply (n m : ℕ) (p : Fin m → MvPolynomial (Fin n) ℚ)
    (x : Fin n → ℝ) (i : Fin m) :
    readPolynomials n m p x i = MvPolynomial.eval₂ (algebraMap ℚ ℝ) x (p i) := rfl

example (n m : ℕ) : CompleteSpace C((Fin n → ℝ), (Fin m → ℝ)) := inferInstance

theorem uniformContinuous_evaluation {X Y : Type*} [TopologicalSpace X] [UniformSpace Y]
    (x : X) : UniformContinuous (fun f : C(X, Y) => f x) := by
  exact (UniformOnFun.uniformContinuous_eval_of_mem Y {K : Set X | IsCompact K}
    (Set.mem_singleton x) isCompact_singleton).comp
      ContinuousMap.isUniformEmbedding_toUniformOnFunIsCompact.uniformContinuous

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherLawCompletion
