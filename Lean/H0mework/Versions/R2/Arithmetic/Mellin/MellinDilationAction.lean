import H0mework.Versions.R2.Arithmetic.Mellin.GaussianRemainderMellin
import H0mework.Versions.R2.Arithmetic.RiemannMellinOrbit.JumpSuccessor

/-!
# Mellin-convergent carrier and q-rich dilation action

For a fixed Mellin parameter, convergent functions form an actual complex
submodule and Mellin integration is a linear functional on it.  Positive
dilation acts linearly, with exact dual character `a⁻ᶻ`.  Specializing to the
existing q-rich successor scales gives a source-native action by
`blockQRichSuccessorScale stage`.
-/

set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace NoIslandNoMagic
namespace CanonicalRiemann

open Complex MeasureTheory Set
open QRich

noncomputable section

abbrev ClozelMellinFunction := ℝ → ℂ

def mellinConvergentSubmodule (z : ℂ) :
    Submodule ℂ ClozelMellinFunction where
  carrier := {f | MellinConvergent f z}
  zero_mem' := by
    unfold MellinConvergent
    simp
  add_mem' := by
    intro f g hf hg
    change MellinConvergent (fun t => f t + g t) z
    exact (hasMellin_add hf hg).1
  smul_mem' := by
    intro c f hf
    exact hf.const_smul c

def mellinFunctional (z : ℂ) :
    mellinConvergentSubmodule z →ₗ[ℂ] ℂ where
  toFun f := mellin f.1 z
  map_add' := by
    intro f g
    exact (hasMellin_add f.2 g.2).2
  map_smul' := by
    intro c f
    exact (hasMellin_const_smul f.2 c).2

def mellinDilation (z : ℂ) (a : ℝ) (positive : 0 < a) :
    mellinConvergentSubmodule z →ₗ[ℂ]
      mellinConvergentSubmodule z where
  toFun f :=
    ⟨fun t => f.1 (a * t),
      (MellinConvergent.comp_mul_left positive).2 f.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem mellinFunctional_dilation
    (z : ℂ) (a : ℝ) (positive : 0 < a)
    (f : mellinConvergentSubmodule z) :
    mellinFunctional z (mellinDilation z a positive f) =
      (a : ℂ) ^ (-z) • mellinFunctional z f := by
  exact mellin_comp_mul_left f.1 z positive

theorem mellinDilation_comp_apply
    (z : ℂ) (first second : ℝ)
    (firstPositive : 0 < first) (secondPositive : 0 < second)
    (f : mellinConvergentSubmodule z) :
    mellinDilation z first firstPositive
        (mellinDilation z second secondPositive f) =
      mellinDilation z (second * first)
        (mul_pos secondPositive firstPositive) f := by
  apply Subtype.ext
  funext t
  change f.1 (second * (first * t)) = f.1 ((second * first) * t)
  ring_nf

def qRichMellinDilation
    (z : ℂ) (stage : Nat) :
    mellinConvergentSubmodule z →ₗ[ℂ]
      mellinConvergentSubmodule z :=
  mellinDilation z (blockQRichSuccessorScale stage : ℝ) <| by
    rw [blockQRichSuccessorScale_eq_stage_add_three]
    positivity

theorem mellinFunctional_qRichMellinDilation
    (z : ℂ) (stage : Nat)
    (f : mellinConvergentSubmodule z) :
    mellinFunctional z (qRichMellinDilation z stage f) =
      (blockQRichSuccessorScale stage : ℂ) ^ (-z) •
        mellinFunctional z f := by
  exact mellinFunctional_dilation z
    (blockQRichSuccessorScale stage : ℝ) (by
      rw [blockQRichSuccessorScale_eq_stage_add_three]
      positivity) f

def qRichScaleProductStage (first second : Nat) : Nat :=
  blockQRichSuccessorScale first * blockQRichSuccessorScale second - 3

theorem blockQRichSuccessorScale_productStage
    (first second : Nat) :
    blockQRichSuccessorScale (qRichScaleProductStage first second) =
      blockQRichSuccessorScale first *
        blockQRichSuccessorScale second := by
  have productLarge :
      3 ≤ (first + 3) * (second + 3) := by
    calc
      3 ≤ first + 3 := by omega
      _ ≤ (first + 3) * (second + 3) :=
        Nat.le_mul_of_pos_right _ (by omega)
  unfold qRichScaleProductStage
  simp_rw [blockQRichSuccessorScale_eq_stage_add_three]
  omega

theorem qRichMellinDilation_comp_apply
    (z : ℂ) (first second : Nat)
    (f : mellinConvergentSubmodule z) :
    qRichMellinDilation z first
        (qRichMellinDilation z second f) =
      qRichMellinDilation z (qRichScaleProductStage first second) f := by
  apply Subtype.ext
  funext t
  simp only [qRichMellinDilation, mellinDilation,
    LinearMap.coe_mk, AddHom.coe_mk]
  rw [blockQRichSuccessorScale_productStage]
  push_cast
  ring_nf

end

end CanonicalRiemann
end NoIslandNoMagic
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
