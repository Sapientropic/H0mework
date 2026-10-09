import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.Runtime.Consumers
import H0mework.Versions.AB.Arithmetic.PrimeShadow.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Attraction.Precise.SourceData
import H0mework.Versions.AB.Arithmetic.PrimeShadow.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Consumers
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Proxy.Final.Comparison

set_option autoImplicit false
set_option maxRecDepth 16384
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.Spatial
open Propagation.Interface
open UnifiedOrbitals.Frame
open UnifiedOrbitals.Frame.Occupation.Factor
open UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual
open scoped Matrix Matrix.Norms.L2Operator
noncomputable section


def current := ReceiverBody.Runtime.readCurrent ReceiverBody.Runtime.afterFirst

theorem current_generated : current=ReceiverBody.Runtime.sourceOutput :=
  ReceiverBody.Runtime.first_generated.trans ReceiverBody.Runtime.generated_action_answer

theorem current_position (a : Fin 13) (k : Fin 3) :
    current.frame.position a k=UnifiedOrbitals.Attraction.Precise.nucleus a k := by
  rw [current_generated]
  rfl

theorem current_realized : current.realized=Reentry.Source.targetRealized := by
  rw [current_generated]
  exact realized_path_exact duration

theorem current_held : current.held=Reentry.Producer.exactTarget := by
  rw [current_generated]
  exact held_path_exact duration

theorem current_centres (i : Basis) :
    List.Forall (fun t => ∃ a : Fin 13, t.centre=current.frame.position a)
      (BasinRefinement.SourceFiniteData.sourceTerms i) := by
  have positions : current.frame.position=UnifiedOrbitals.Attraction.Precise.nucleus :=
    funext fun a => funext fun k => current_position a k
  rw [positions]
  exact UnifiedOrbitals.Attraction.Precise.all_term_centres_precise i

theorem current_complex_frame :
    complexFrame*registeredState current.realized*star complexFrame=registeredAOState current.realized := by
  rw [current_realized]
  exact actual_Gamma_spatial_preservation

-- recordedD3 is the recorded-frame congruence of the AO matrix, not the raw AO coefficients.
theorem current_recorded_frame_residual (i j : Basis) :
    |Proxy.Correction.recordedD3 i j-(current.realized i j).re| < (1/10^12 : ℝ) := by
  rw [current_realized]
  exact Proxy.Final.recorded_original_gamma_real i j

theorem current_normalized_frame_residual (i j : Basis) :
    |normalizedDensityMatrix i j-Proxy.Correction.recordedD3 i j| ≤ Proxy.Final.actualMatrixEnvelope :=
  Proxy.Final.actual_recorded_D3_entry i j

theorem current_rounding (a : Fin 13) (k : Fin 3) :
    |current.frame.position a k-
      BasinRefinement.WholeBandBasin.Family.All.Nuclear.nuclearPositionQ a k| <
      (1 : ℚ)/(2*10^12) := by
  rw [current_position]
  exact UnifiedOrbitals.Attraction.Precise.ledger_rounding_residual a k

theorem current_normalized_gamma_residual (i j : Basis) :
    |normalizedDensityMatrix i j-(current.realized i j).re| <
      Proxy.Final.actualMatrixEnvelope+(1/10^12 : ℝ) := by
  have triangle := abs_add_le
    (normalizedDensityMatrix i j-Proxy.Correction.recordedD3 i j)
    (Proxy.Correction.recordedD3 i j-(current.realized i j).re)
  have first := current_normalized_frame_residual i j
  have second := current_recorded_frame_residual i j
  have identity : normalizedDensityMatrix i j-(current.realized i j).re =
      (normalizedDensityMatrix i j-Proxy.Correction.recordedD3 i j)+
      (Proxy.Correction.recordedD3 i j-(current.realized i j).re) := by ring
  rw [identity]
  exact lt_of_le_of_lt triangle (add_lt_add_of_le_of_lt first second)

structure StaticClosure (body : ReceiverBody.Runtime.ActuationResult) : Prop where
  position : ∀ a k, body.frame.position a k=UnifiedOrbitals.Attraction.Precise.nucleus a k
  centres : ∀ i : Basis, List.Forall (fun t => ∃ a : Fin 13,
    t.centre=body.frame.position a) (BasinRefinement.SourceFiniteData.sourceTerms i)
  held : body.held=Reentry.Producer.exactTarget
  realized : body.realized=Reentry.Source.targetRealized
  complexFrame : complexFrame*registeredState body.realized*star complexFrame=
    registeredAOState body.realized
  rounding : ∀ a k, |body.frame.position a k-
    BasinRefinement.WholeBandBasin.Family.All.Nuclear.nuclearPositionQ a k| < (1 : ℚ)/(2*10^12)
  aoFrame : type_of% Proxy.Correction.actual_D3_factor
  exactFrameResidual : type_of% Proxy.Correction.actual_recorded_D3_difference
  density : ∀ x, type_of% (actual_original_D3_preserved x)
  registeredFrameResidual : ∀ i j : Basis,
    |Proxy.Correction.recordedD3 i j-(body.realized i j).re| < (1/10^12 : ℝ)
  normalizedFrameResidual : ∀ i j : Basis,
    |normalizedDensityMatrix i j-Proxy.Correction.recordedD3 i j| ≤ Proxy.Final.actualMatrixEnvelope
  gammaResidual : ∀ i j : Basis, |normalizedDensityMatrix i j-(body.realized i j).re| <
    Proxy.Final.actualMatrixEnvelope+(1/10^12 : ℝ)

theorem sourceStaticClosure : StaticClosure current :=
  ⟨current_position,current_centres,current_held,current_realized,current_complex_frame,
    current_rounding,Proxy.Correction.actual_D3_factor,Proxy.Correction.actual_recorded_D3_difference,
    actual_original_D3_preserved,current_recorded_frame_residual,current_normalized_frame_residual,
    current_normalized_gamma_residual⟩

theorem outputStaticClosure : StaticClosure ReceiverBody.Runtime.sourceOutput := by
  rw [← current_generated]
  exact sourceStaticClosure

end
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.Spatial
