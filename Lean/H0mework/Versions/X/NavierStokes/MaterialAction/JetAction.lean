import H0mework.Versions.X.NavierStokes.MaterialAction.PauliJet
import H0mework.Versions.X.NavierStokes.MaterialAction.SpinConnection

set_option autoImplicit false
open scoped Matrix BigOperators

namespace SaturationMonoid.NavierStokes.NativeMaterialJetAction

open PhysicsCore DiracExteriorMatterAction PointwiseDiracSpinConnectionLift
open StageNineCurrentCoframeMatterTemporalPrincipal
open ThreeDimensionalPeriodicCoarseFilterCore
open NativePauliControl NativePauliMotherAction NativePauliCoframeAction

noncomputable section

def normalizedJet (derivative : Fin 4 → PhysicalSpace) : Fin 4 → Vector :=
  fun direction => normalizedVelocity (derivative direction)

theorem source_density (velocity : PhysicalSpace) :
    NativeCanonicalFluidCoframe.density velocity = NativePauliJet.density (normalizedVelocity velocity) := by
  simp [NativeCanonicalFluidCoframe.density, NativePauliJet.density, normalizedVelocity,
    EuclideanSpace.norm_sq_eq, Real.norm_eq_abs, Fin.sum_univ_three]
  ring

def geometry (velocity : PhysicalSpace) (derivative : Fin 4 → PhysicalSpace) :
    PointwiseLorentzianCoframeJet :=
  NativeCoframeSpin.jet velocity (NativePauliJet.logDerivative (normalizedVelocity velocity) (normalizedJet derivative))

theorem density_hasDerivAt {path : ℝ → PhysicalSpace} {time : ℝ}
    (derivative : PhysicalSpace) (differentiable : HasDerivAt path derivative time) :
    HasDerivAt (fun actual => NativeCanonicalFluidCoframe.density (path actual))
      (4 * ∑ component, normalizedVelocity (path time) component * normalizedVelocity derivative component) time := by
  convert! (differentiable.norm_sq.div_const 8).const_add 2 using 1
  simp [EuclideanSpace.inner_eq_star_dotProduct, normalizedVelocity, dotProduct, Fin.sum_univ_three]
  ring

theorem scale_hasDerivAt {path : ℝ → PhysicalSpace} {time : ℝ}
    (derivative : Fin 4 → PhysicalSpace) (direction : Fin 4)
    (differentiable : HasDerivAt path (derivative direction) time) :
    HasDerivAt (fun actual => NativeCanonicalFluidCoframe.scale (path actual))
      (NativeCanonicalFluidCoframe.scale (path time) *
        NativePauliJet.logDerivative (normalizedVelocity (path time)) (normalizedJet derivative) direction) time := by
  have generated := (density_hasDerivAt _ differentiable).rpow_const
    (p := (3 : ℝ)⁻¹) (Or.inl (NativeCanonicalFluidCoframe.density_pos (path time)).ne')
  convert! generated using 1
  rw [Real.rpow_sub_one (NativeCanonicalFluidCoframe.density_pos (path time)).ne']
  simp only [NativeCanonicalFluidCoframe.scale, NativePauliJet.logDerivative, normalizedJet, source_density]
  ring

/-- The coframe jet used by the producer is the actual chain-rule derivative of the generated frame. -/
theorem coframe_hasDerivAt {path : ℝ → PhysicalSpace} {time : ℝ}
    (derivative : Fin 4 → PhysicalSpace) (direction : Fin 4)
    (differentiable : HasDerivAt path (derivative direction) time) :
    HasDerivAt (fun actual => NativeCanonicalFluidCoframe.coframe (path actual))
      ((geometry (path time) derivative).derivative direction) time := by
  apply hasDerivAt_pi.mpr
  intro internal
  apply hasDerivAt_pi.mpr
  intro coordinate
  have generated := scale_hasDerivAt derivative direction differentiable
  by_cases same : internal = coordinate
  · subst coordinate
    fin_cases internal <;>
      simp [NativeCanonicalFluidCoframe.coframe, NativeCanonicalFluidCoframe.diagonal,
        geometry, NativeCoframeSpin.jet, NativeDiagonalCoframe.jet, Matrix.diagonal_apply_eq,
        NativeCoframeSpin.weight]
    · convert! generated.pow 2 using 1
      ring
    all_goals
      convert! generated.inv (NativeCanonicalFluidCoframe.scale_pos (path time)).ne' using 1
      field_simp
  · simpa only [NativeCanonicalFluidCoframe.coframe, geometry, NativeCoframeSpin.jet,
      NativeDiagonalCoframe.jet, Matrix.diagonal_apply_ne _ same] using hasDerivAt_const time (0 : ℝ)

def freeDerivative (velocity : PhysicalSpace) (derivative : Fin 4 → PhysicalSpace)
    (direction : Fin 4) : DiracExteriorMatterCarrier :=
  lowerMatter (NativePauliJet.tangent (normalizedJet derivative direction)) +
    diracMatrixMatterAction (diracSpinConnectionLift (geometry velocity derivative).lorentzSpinConnection direction)
      (NativeCanonicalFluidCoframe.matter velocity)

def target (velocity : PhysicalSpace) (derivative : Fin 4 → PhysicalSpace) : Block :=
  -NativePauliJet.freeResponse (normalizedVelocity velocity) (normalizedJet derivative)

def covariantDerivative (velocity : PhysicalSpace) (derivative : Fin 4 → PhysicalSpace)
    (direction : Fin 4) : DiracExteriorMatterCarrier :=
  freeDerivative velocity derivative direction + gaugeIncrement velocity (target velocity derivative) direction

theorem normalized_add (velocity : PhysicalSpace)
    (first second : Fin 4 → DiracExteriorMatterCarrier) :
    normalizedDerivative velocity (fun direction => first direction + second direction) =
      normalizedDerivative velocity first + normalizedDerivative velocity second := by
  simp only [normalizedDerivative, map_add, smul_add, Finset.sum_add_distrib]

theorem spinAction_zero (block : Block) : spinAction block 0 = block := by
  ext row column
  simp [spinAction, spinPrincipal, Matrix.one_apply]

theorem tangent_response (velocity : PhysicalSpace) (derivative : Fin 4 → PhysicalSpace) :
    normalizedDerivative velocity (fun direction => lowerMatter (NativePauliJet.tangent (normalizedJet derivative direction))) =
      lowerMatter (NativePauliJet.tangent (normalizedJet derivative 0) +
        (NativeCanonicalFluidCoframe.density velocity : ℂ) • ∑ direction : Fin 3,
          spinAction (NativePauliJet.tangent (normalizedJet derivative direction.succ)) direction.succ) := by
  simp only [normalizedDerivative, spin_action, ← map_smul, ← map_sum]
  congr 1
  rw [Fin.sum_univ_succ]
  simp [compensation, spinAction_zero, Fin.sum_univ_three]

/-- The generated coframe and the source material jet produce the full free response. -/
theorem free_response (velocity : PhysicalSpace) (derivative : Fin 4 → PhysicalSpace) :
    normalizedDerivative velocity (freeDerivative velocity derivative) =
      lowerMatter (NativePauliJet.freeResponse (normalizedVelocity velocity) (normalizedJet derivative)) := by
  rw [show freeDerivative velocity derivative = fun direction =>
    lowerMatter (NativePauliJet.tangent (normalizedJet derivative direction)) +
      diracMatrixMatterAction (diracSpinConnectionLift (geometry velocity derivative).lorentzSpinConnection direction)
        (NativeCanonicalFluidCoframe.matter velocity) from rfl,
    normalized_add, tangent_response]
  rw [show geometry velocity derivative = NativeCoframeSpin.jet velocity
      (NativePauliJet.logDerivative (normalizedVelocity velocity) (normalizedJet derivative)) from rfl,
    NativeCoframeSpin.spin_response, source_matter, source_density]
  simp only [NativePauliJet.freeResponse, map_add, map_sub, map_smul]
  push_cast
  module

/-- The actual temporal principal consumes the original source jet and the generated color connection. -/
theorem actual_inverse_response (velocity : PhysicalSpace) (derivative : Fin 4 → PhysicalSpace) :
    currentCoframeMatterTemporalPrincipalInverse (NativeCanonicalFluidCoframe.coframe velocity)
        (gaugeVectorAt (NativeCanonicalFluidCoframe.coframe velocity) (covariantDerivative velocity derivative)) =
      (NativeCanonicalFluidCoframe.density velocity *
        ∑ direction : Fin 3, normalizedJet derivative direction.succ direction : ℂ) • lowerMatter 1 := by
  rw [actual_derivative_inverse]
  change normalizedDerivative velocity
    (fun direction => freeDerivative velocity derivative direction + gaugeIncrement velocity (target velocity derivative) direction) = _
  rw [normalized_add, free_response]
  have response := NativePauliCoframeAction.actual_inverse_response velocity (target velocity derivative)
  rw [gaugeVector, actual_derivative_inverse] at response
  rw [response, target, source_density]
  rw [← controlled_wholeAction]
  exact NativePauliJet.controlled_response (normalizedVelocity velocity) (normalizedJet derivative)

end
end SaturationMonoid.NavierStokes.NativeMaterialJetAction
