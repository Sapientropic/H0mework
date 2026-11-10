import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.PhysicsCore.YangMills.Terminal.Geometry
import H0mework.Quantum.Generator.SelfAdjoint

/-! The relativistic QFT core of the terminal statement. Every clause is
expressed on the actual Hilbert space and fields; Yang--Mills gauge and
short-distance identification are supplied by the separate terminal clause. -/

set_option autoImplicit false

open MeasureTheory
open scoped InnerProductSpace LinearPMap

namespace SaturationMonoid.PhysicsCore.YangMills.Terminal

noncomputable section

/-- The two symmetry representations and their exact cross relation represent
the connected Poincare cover. Fields are Hermitian bosonic components. -/
structure QuantumCore where
  Hilbert : Type
  [hilbertNormed : NormedAddCommGroup Hilbert]
  [hilbertInner : InnerProductSpace ℂ Hilbert]
  [hilbertComplete : CompleteSpace Hilbert]
  [hilbertSeparable : TopologicalSpace.SeparableSpace Hilbert]
  Components : Type
  [componentAdd : AddCommGroup Components]
  [componentSpace : Module ℝ Components]
  translations : Multiplicative Spacetime →* (Hilbert ≃ₗᵢ[ℂ] Hilbert)
  lorentz : Spin →* (Hilbert ≃ₗᵢ[ℂ] Hilbert)
  componentAction : Spin →* (Components ≃ₗ[ℝ] Components)
  component_orbit_finite : ∀ c, FiniteDimensional ℝ
    (Submodule.span ℝ (Set.range (fun s : Spin => componentAction s c)))
  -- Continuity belongs to each finite tensor multiplet, not to a chosen
  -- norm on the entire algebraic space of local field labels.
  component_continuous : ∀ c (coordinate : Components →ₗ[ℝ] ℝ),
    Continuous (fun s => coordinate (componentAction s c))
  poincare_relation : ∀ s a v,
    lorentz s (translations (Multiplicative.ofAdd a) v) =
      translations (Multiplicative.ofAdd (lorentzMap s a)) (lorentz s v)
  poincare_continuous : ∀ v, Continuous (fun p : Spacetime × Spin =>
    translations (Multiplicative.ofAdd p.1) (lorentz p.2 v))
  vacuum : Hilbert
  vacuum_norm : ‖vacuum‖ = 1
  vacuum_translation : ∀ a, translations (Multiplicative.ofAdd a) vacuum = vacuum
  vacuum_lorentz : ∀ s, lorentz s vacuum = vacuum
  vacuum_unique : ∀ v,
    (∀ a, translations (Multiplicative.ofAdd a) v = v) ↔ ∃ c : ℂ, v = c • vacuum
  domain : Submodule ℂ Hilbert
  domain_dense : Dense (domain : Set Hilbert)
  vacuum_mem : vacuum ∈ domain
  translation_domain : ∀ a (v : domain), translations (Multiplicative.ofAdd a) v.val ∈ domain
  lorentz_domain : ∀ s (v : domain), lorentz s v.val ∈ domain
  field : Components →ₗ[ℝ] Test →ₗ[ℂ] domain →ₗ[ℂ] domain
  tempered : ∀ c (v : domain), Continuous (fun f : Test => (field c f v).val)
  hermitian : ∀ c f (u v : domain),
    inner ℂ (field c f u).val v.val = inner ℂ u.val (field c (conjugateTest f) v).val
  translation_covariant : ∀ a c f (v : domain),
    translations (Multiplicative.ofAdd a) (field c f v).val =
      (field c (translateTest a f) ⟨translations (Multiplicative.ofAdd a) v.val, translation_domain a v⟩).val
  lorentz_covariant : ∀ s c f (v : domain),
    lorentz s (field c f v).val =
      (field (componentAction s c) (lorentzTest s f) ⟨lorentz s v.val, lorentz_domain s v⟩).val
  locality : ∀ c d f g, SpacelikeSeparated f g → ∀ v : domain,
    field c f (field d g v) = field d g (field c f v)
  cyclic : Dense ((Submodule.span ℂ (Set.range (fun word : List (Components × Test) =>
    (word.foldr (fun letter v => field letter.1 letter.2 v) ⟨vacuum, vacuum_mem⟩).val))) : Set Hilbert)
  momentumMeasure : Hilbert → Measure Spacetime
  momentum_mass : ∀ v, momentumMeasure v Set.univ = ENNReal.ofReal (‖v‖ ^ 2)
  momentum_support : ∀ v, momentumMeasure v futureConeᶜ = 0
  momentum_coefficient : ∀ v a,
    inner ℂ v (translations (Multiplicative.ofAdd a) v) =
      ∫ p, spectralCharacter p a ∂momentumMeasure v

attribute [instance] QuantumCore.hilbertNormed QuantumCore.hilbertInner QuantumCore.hilbertComplete QuantumCore.hilbertSeparable
  QuantumCore.componentAdd QuantumCore.componentSpace

namespace QuantumCore

variable (Q : QuantumCore)

def operator (c : Q.Components) (f : Test) : Q.Hilbert →ₗ.[ℂ] Q.Hilbert where
  domain := Q.domain
  toFun := Q.domain.subtype.comp (Q.field c f)

def distribution (c : Q.Components) (v : Q.domain) : Test →L[ℂ] Q.Hilbert where
  toLinearMap := Q.domain.subtype.comp ((Q.field c).flip v)
  cont := Q.tempered c v

def time : Multiplicative ℝ →* (Q.Hilbert ≃ₗᵢ[ℂ] Q.Hilbert) := Q.translations.comp timeEmbedding

theorem time_continuous (v : Q.Hilbert) : Continuous (Quantum.Generator.orbit Q.time v) := by
  have continuous := (Q.poincare_continuous v).comp
    (timeLine.toContinuousLinearMap.continuous.prodMk (continuous_const (y := (1 : Spin))))
  convert! continuous using 1
  funext t
  change Q.translations (Multiplicative.ofAdd (timeLine t)) v =
    Q.translations (Multiplicative.ofAdd (timeLine t)) (Q.lorentz 1 v)
  rw [map_one]
  rfl

def hamiltonian : Q.Hilbert →ₗ.[ℂ] Q.Hilbert := Quantum.Generator.hamiltonianOperator Q.time

theorem hamiltonian_selfAdjoint : IsSelfAdjoint Q.hamiltonian :=
  Quantum.Generator.hamiltonianOperator_selfAdjoint Q.time Q.time_continuous

theorem vacuum_derivative : HasDerivAt (Quantum.Generator.orbit Q.time Q.vacuum) 0 0 := by
  have fixed : Quantum.Generator.orbit Q.time Q.vacuum = fun _ => Q.vacuum := by
    funext t
    exact Q.vacuum_translation (timeLine t)
  rw [fixed]
  exact hasDerivAt_const 0 Q.vacuum

def vacuumInDomain : Q.hamiltonian.domain :=
  ⟨Q.vacuum, Q.vacuum_derivative.differentiableAt⟩

theorem hamiltonian_vacuum : Q.hamiltonian Q.vacuumInDomain = 0 := by
  change Complex.I • deriv (Quantum.Generator.orbit Q.time Q.vacuum) 0 = 0
  rw [Q.vacuum_derivative.deriv, smul_zero]

end QuantumCore
end
end SaturationMonoid.PhysicsCore.YangMills.Terminal
