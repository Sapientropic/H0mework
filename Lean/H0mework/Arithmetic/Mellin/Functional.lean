import Mathlib.Analysis.MellinTransform
import H0mework.Arithmetic.Mellin.PositiveDomain

/-!
# Narrow positive Mellin functional base

Extension by zero, the convergent submodule, and its algebraic Mellin
functional are source-neutral.  Dilation scales, Gaussian relations, q-rich
successors, zeros, and endpoints live above this firewall.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace NoIslandNoMagic
namespace CanonicalRiemann

open Complex MeasureTheory Set

noncomputable section

def positiveMellinExtension :
    ClozelPositiveMellinFunction →ₗ[ℂ] (ℝ → ℂ) where
  toFun f t := if positive : 0 < t then f ⟨t, positive⟩ else 0
  map_add' := by
    intro f g
    funext t
    by_cases positive : 0 < t <;>
      simp [positive]
  map_smul' := by
    intro c f
    funext t
    by_cases positive : 0 < t <;>
      simp [positive]

def positiveMellinConvergentSubmodule (z : ℂ) :
    Submodule ℂ ClozelPositiveMellinFunction where
  carrier := {f | MellinConvergent (positiveMellinExtension f) z}
  zero_mem' := by
    change MellinConvergent (positiveMellinExtension 0) z
    rw [map_zero]
    unfold MellinConvergent
    simp
  add_mem' := by
    intro f g hf hg
    change MellinConvergent (positiveMellinExtension (f + g)) z
    rw [map_add]
    change MellinConvergent
      (fun t => positiveMellinExtension f t +
        positiveMellinExtension g t) z
    exact (hasMellin_add hf hg).1
  smul_mem' := by
    intro c f hf
    change MellinConvergent (positiveMellinExtension (c • f)) z
    rw [map_smul]
    exact hf.const_smul c

def positiveMellinFunctional (z : ℂ) :
    positiveMellinConvergentSubmodule z →ₗ[ℂ] ℂ where
  toFun f := mellin (positiveMellinExtension f.1) z
  map_add' := by
    intro f g
    change mellin (positiveMellinExtension (f.1 + g.1)) z =
      mellin (positiveMellinExtension f.1) z +
        mellin (positiveMellinExtension g.1) z
    rw [map_add]
    exact (hasMellin_add f.2 g.2).2
  map_smul' := by
    intro c f
    change mellin (positiveMellinExtension (c • f.1)) z =
      c • mellin (positiveMellinExtension f.1) z
    rw [map_smul]
    exact (hasMellin_const_smul f.2 c).2

end

end CanonicalRiemann
end NoIslandNoMagic
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
