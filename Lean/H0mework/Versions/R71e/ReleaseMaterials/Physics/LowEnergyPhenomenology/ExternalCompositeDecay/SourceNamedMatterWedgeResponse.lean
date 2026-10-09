import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceNamedMatterWedgeCarrier
import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceFullYBornFrequency
import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceFullYFullSourceCausalReturn

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.NamedMatterWedgeQt
open SourceQuantumConfigurationHilbert SourceQuantumFockGauge
open GaussCoreDifferential GaussCoreHilbert GaussDensityCore GaussFockPair GaussUnitaryHistory
open FullYDynamicSource FullYDynamicResponse CompositeFullYBorn SourceScalarPairedTransport
open MeasureTheory
open scoped InnerProductSpace ENNReal
attribute [local irreducible] wedgeTest literalCoreResolvent literalSharpResolvent

private theorem positive_density_return (p : ℝ → ℝ) (hi : Integrable p)
    (hn : ∀ ω, 0 ≤ p ω) (B : Set ℝ) (hB : MeasurableSet B) :
    volume.withDensity (fun ω => ENNReal.ofReal (p ω)) B =
      ENNReal.ofReal (∫ ω in B, p ω) := by
  rw [withDensity_apply _ hB]
  exact (ofReal_integral_eq_lintegral_ofReal hi.restrict (Filter.Eventually.of_forall hn)).symm

def wedgeResponse (F : Index) (dual sharp advanced : Bool) (a : WedgeFiber)
    (f : ScalarTest) (μ : ℝ) (hμ : 0 < μ) (ω : ℝ) : H :=
  embed (literalResponse F sharp (wedgeTest dual a f) advanced μ hμ ω)

theorem actual_wedge_response_frequency (F : Index) (dual sharp advanced : Bool)
    (a : WedgeFiber) (f : ScalarTest) (μ : ℝ) (hμ : 0 < μ) :
    Integrable (fun ω : ℝ => ‖wedgeResponse F dual sharp advanced a f μ hμ ω‖ ^ 2) :=
  actual_response_square_integrable F sharp (wedgeTest dual a f) advanced μ hμ

def wedgeResponseMeasure (F : Index) (dual sharp advanced : Bool) (a : WedgeFiber)
    (f : ScalarTest) (μ : ℝ) (hμ : 0 < μ) : Measure ℝ :=
  volume.withDensity (fun ω => ENNReal.ofReal (‖wedgeResponse F dual sharp advanced a f μ hμ ω‖ ^ 2))

theorem actual_wedge_response_measure (F : Index) (dual sharp advanced : Bool)
    (a : WedgeFiber) (f : ScalarTest) (μ : ℝ) (hμ : 0 < μ) :
    (∀ B : Set ℝ, MeasurableSet B → wedgeResponseMeasure F dual sharp advanced a f μ hμ B =
      ENNReal.ofReal (∫ ω in B, ‖wedgeResponse F dual sharp advanced a f μ hμ ω‖ ^ 2)) ∧
    IsFiniteMeasure (wedgeResponseMeasure F dual sharp advanced a f μ hμ) := by
  have hi := actual_wedge_response_frequency F dual sharp advanced a f μ hμ
  constructor
  · intro B hB
    exact positive_density_return _ hi (fun _ => sq_nonneg _) B hB
  · exact ⟨by
      change (volume.withDensity _ Set.univ) < ⊤
      rw [positive_density_return _ hi (fun _ => sq_nonneg _) Set.univ MeasurableSet.univ]
      exact ENNReal.ofReal_lt_top⟩

theorem actual_wedge_full_source_return (F : Index) (dual : Bool) (a : WedgeFiber)
    (f : ScalarTest) :
    ∃ K₀ : Index, F ⊆ K₀ ∧ ∀ K : Index, K₀ ⊆ K → ∀ z : ℂ, ∀ hz : z.im ≠ 0,
      literalCoreResolvent K z hz
          ((GaussFullHamiltonian.fullAction - z • (1 : QuantumTest →ₗ[ℂ] QuantumTest))
            (wedgeTest dual a f)) = wedgeTest dual a f ∧
      literalSharpResolvent K z hz
          ((GaussFullHamiltonian.sharpAction - z • (1 : QuantumTest →ₗ[ℂ] QuantumTest))
            (wedgeTest dual a f)) = wedgeTest dual a f :=
  FullYDynamicSourceRefinement.actual_full_source_forcing_return F
    (wedgeTest dual a f) (wedgeTest dual a f)

end LowEnergy.NamedMatterWedgeQt
