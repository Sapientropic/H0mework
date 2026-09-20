import Mathlib.Logic.Relation

/-!
# Kernel-pair equivalence core

This semantic module owns the generic single-function and `(key, source)`
kernel-pair laws.  `Proposition6` remains a compatibility import; modern
authority modules depend on this file directly.
-/

/-- The kernel pair relation: `x ~ y` iff `f x = f y`. -/
def KernelPair {α : Type*} {β : Type*} (f : α → β) : α → α → Prop :=
  fun x y => f x = f y

theorem kernelPair_refl {α β : Type*} (f : α → β) (x : α) :
    KernelPair f x x := rfl

theorem kernelPair_symm {α β : Type*} (f : α → β) :
    ∀ {x y : α}, KernelPair f x y → KernelPair f y x :=
  fun {_ _} h => h.symm

theorem kernelPair_trans {α β : Type*} (f : α → β) :
    ∀ {x y z : α}, KernelPair f x y → KernelPair f y z → KernelPair f x z :=
  fun {_ _ _} hx hy => hx.trans hy

theorem kernelPair_equivalence {α β : Type*} (f : α → β) :
    Equivalence (KernelPair f) :=
  ⟨kernelPair_refl f, kernelPair_symm f, kernelPair_trans f⟩

theorem kernelPair_congr {α β γ : Type*} (f : α → β) (g : β → γ) :
    ∀ {x y : α}, KernelPair f x y → KernelPair (g ∘ f) x y :=
  fun {x y} h => by show g (f x) = g (f y); rw [h]

/-- Pair kernel: equality of both key and source projections. -/
def PairKernel {α κ σ : Type*} (key : α → κ) (src : α → σ) : α → α → Prop :=
  fun x y => key x = key y ∧ src x = src y

theorem pairKernel_refl {α κ σ : Type*} (key : α → κ) (src : α → σ) (x : α) :
    PairKernel key src x x := ⟨rfl, rfl⟩

theorem pairKernel_symm {α κ σ : Type*} (key : α → κ) (src : α → σ) :
    ∀ {x y : α}, PairKernel key src x y → PairKernel key src y x :=
  fun {_ _} ⟨hk, hs⟩ => ⟨hk.symm, hs.symm⟩

theorem pairKernel_trans {α κ σ : Type*} (key : α → κ) (src : α → σ) :
    ∀ {x y z : α}, PairKernel key src x y → PairKernel key src y z →
      PairKernel key src x z :=
  fun {_ _ _} ⟨hk1, hs1⟩ ⟨hk2, hs2⟩ => ⟨hk1.trans hk2, hs1.trans hs2⟩

theorem pairKernel_equivalence {α κ σ : Type*} (key : α → κ) (src : α → σ) :
    Equivalence (PairKernel key src) :=
  ⟨pairKernel_refl key src, pairKernel_symm key src, pairKernel_trans key src⟩

theorem pairKernel_congr {α κ σ γ : Type*}
    (key : α → κ) (src : α → σ) (op : κ × σ → γ) :
    ∀ {x y : α}, PairKernel key src x y →
      op ⟨key x, src x⟩ = op ⟨key y, src y⟩ :=
  fun {x y} ⟨hk, hs⟩ => by rw [hk, hs]
