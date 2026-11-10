import H0mework.Physics.Lorentz.LorentzCoverAndSpinDescent
import H0mework.Physics.Holonomic.HolonomicField
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-! The terminal uses the existing four-dimensional Minkowski carrier and
the actual SL(2,C) Spin--Lorentz action, with standard Schwartz pullbacks. -/

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.YangMills.Terminal

open MeasureTheory
open StageNineLorentzCoverAndSpinDescent

noncomputable section

abbrev Spacetime := ProofFreeRicherAnholonomicSource.BasePoint
abbrev Spin := StageNineGlobalBundle.SpinPlus13
abbrev Test := SchwartzMap Spacetime ℂ

def lorentzMap (s : Spin) : Spacetime ≃L[ℝ] Spacetime :=
  (spinLorentzCover s).toContinuousLinearEquiv

def translateTest (a : Spacetime) : Test →L[ℂ] Test := SchwartzMap.compSubConstCLM ℂ (-a)

def lorentzTest (s : Spin) : Test →L[ℂ] Test :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (lorentzMap s).symm

def conjugateTest : Test →L[ℝ] Test := SchwartzMap.postcompCLM Complex.conjCLE.toContinuousLinearMap

theorem translateTest_apply (a x : Spacetime) (f : Test) : translateTest a f x = f (x + a) := by
  simp only [translateTest, SchwartzMap.compSubConstCLM_apply, sub_neg_eq_add]

theorem lorentzTest_apply (s : Spin) (f : Test) (x : Spacetime) :
    lorentzTest s f x = f ((spinLorentzCover s).symm x) := rfl

theorem conjugateTest_apply (f : Test) (x : Spacetime) : conjugateTest f x = star (f x) := rfl

def SpacelikeSeparated (f g : Test) : Prop :=
  ∀ x ∈ tsupport (f : Spacetime → ℂ), ∀ y ∈ tsupport (g : Spacetime → ℂ),
    0 < minkowskiQuadratic (x - y)

def futureCone : Set Spacetime := {p | 0 ≤ p 0 ∧ minkowskiQuadratic p ≤ 0}

def momentumPair (p a : Spacetime) : ℝ :=
  p 0 * a 0 - p 1 * a 1 - p 2 * a 2 - p 3 * a 3

def spectralCharacter (p a : Spacetime) : ℂ := Complex.exp (-Complex.I * (momentumPair p a : ℂ))

def timeLine : ℝ →ₗ[ℝ] Spacetime :=
  (LinearMap.id : ℝ →ₗ[ℝ] ℝ).smulRight (StageNineHolonomicField.coordinateDirection 0)

def timeEmbedding : Multiplicative ℝ →* Multiplicative Spacetime :=
  AddMonoidHom.toMultiplicative timeLine.toAddMonoidHom

theorem timeLine_time (t : ℝ) : timeLine t 0 = t := by
  simp [timeLine, StageNineHolonomicField.coordinateDirection]

end
end SaturationMonoid.PhysicsCore.YangMills.Terminal
