import H0mework.NavierStokes.MaterialJets.DensitizedReceipt

set_option autoImplicit false
open scoped Matrix BigOperators ContDiff

namespace SaturationMonoid.NavierStokes.NativeMaterialReadback

open PhysicsCore DiracCliffordRepresentation DiracExteriorMatterAction StageNineHolonomicField
open Stage9C.Material.SpinPair Stage9CU.Fluid
open ThreeDimensionalPeriodicCoarseFilterCore
open NativePauliControl NativePauliMotherAction NativePauliCoframeAction

noncomputable section

def coefficient (spin : Fin 4) (color : Fin 2) : MatterCoordinateCarrier →L[ℂ] ℂ :=
  ({ toFun := fun value => sourceColorDoubletDual color (matterCoordinateEquiv.symm value spin)
     map_add' := by intro first second; simp only [map_add, Pi.add_apply]
     map_smul' := by intro scalar value; simp [map_smul, Pi.smul_apply, smul_eq_mul] } :
    MatterCoordinateCarrier →ₗ[ℂ] ℂ).toContinuousLinearMap

theorem coefficient_matter (velocity : PhysicalSpace) (spin : Fin 4) (color : Fin 2) :
    coefficient spin color (matterCoordinateEquiv (NativeCanonicalFluidCoframe.matter velocity)) =
      InitialLift.coefficients (fun index => velocity index) spin color := by
  change sourceColorDoubletDual color
    (matterCoordinateEquiv.symm (matterCoordinateEquiv (NativeCanonicalFluidCoframe.matter velocity)) spin) = _
  rw [matterCoordinateEquiv.symm_apply_apply]
  simp only [NativeCanonicalFluidCoframe.matter, InitialLift.matter, sourceColorDoubletDual_diracMatter]

def velocityRead : MatterCoordinateCarrier →L[ℝ] PhysicalSpace :=
  ({ toFun := fun value => WithLp.toLp 2
      ![4 * (coefficient 3 0 value).re, 4 * (coefficient 3 0 value).im,
        2 * ((coefficient 2 0 value).re - (coefficient 3 1 value).re)]
     map_add' := by
       intro first second
       ext index
       fin_cases index <;> simp [map_add, mul_add]
       ring
     map_smul' := by
       intro scalar value
       ext index
       fin_cases index <;> simp [smul_eq_mul, Complex.mul_re, Complex.mul_im] <;> ring } :
    MatterCoordinateCarrier →ₗ[ℝ] PhysicalSpace).toContinuousLinearMap

theorem velocityRead_matter (velocity : PhysicalSpace) :
    velocityRead (matterCoordinateEquiv (NativeCanonicalFluidCoframe.matter velocity)) = velocity := by
  ext index
  change (![4 * (coefficient 3 0 (matterCoordinateEquiv (NativeCanonicalFluidCoframe.matter velocity))).re,
    4 * (coefficient 3 0 (matterCoordinateEquiv (NativeCanonicalFluidCoframe.matter velocity))).im,
    2 * ((coefficient 2 0 (matterCoordinateEquiv (NativeCanonicalFluidCoframe.matter velocity))).re -
      (coefficient 3 1 (matterCoordinateEquiv (NativeCanonicalFluidCoframe.matter velocity))).re)] : Fin 3 → ℝ) index = _
  simp only [coefficient_matter]
  fin_cases index <;> simp [InitialLift.coefficients, Complex.mul_re, Complex.mul_im] <;> ring

private def incrementCoefficients : PhysicalSpace →ₗ[ℝ] (Fin 4 → Fin 2 → ℂ) where
  toFun velocity := InitialLift.coefficients (fun index => velocity index) - InitialLift.coefficients 0
  map_add' := by
    intro first second
    ext spin color
    change InitialLift.coefficients (fun index => (first + second) index) spin color - InitialLift.coefficients 0 spin color =
      (InitialLift.coefficients (fun index => first index) spin color - InitialLift.coefficients 0 spin color) +
      (InitialLift.coefficients (fun index => second index) spin color - InitialLift.coefficients 0 spin color)
    fin_cases spin <;> fin_cases color <;> simp [InitialLift.coefficients] <;> ring
  map_smul' := by
    intro scalar velocity
    ext spin color
    change InitialLift.coefficients (fun index => (scalar • velocity) index) spin color - InitialLift.coefficients 0 spin color =
      scalar • (InitialLift.coefficients (fun index => velocity index) spin color - InitialLift.coefficients 0 spin color)
    fin_cases spin <;> fin_cases color <;>
      simp [InitialLift.coefficients, smul_eq_mul] <;> ring

def materialIncrement : PhysicalSpace →L[ℝ] MatterCoordinateCarrier :=
  ((sourceColorMatterCoordinateLinear.restrictScalars ℝ).comp incrementCoefficients).toContinuousLinearMap

theorem materialIncrement_eq (velocity : PhysicalSpace) :
    materialIncrement velocity = matterCoordinateEquiv (NativeCanonicalFluidCoframe.matter velocity) -
      matterCoordinateEquiv (NativeCanonicalFluidCoframe.matter 0) := by
  change sourceColorMatterCoordinateLinear
    (InitialLift.coefficients (fun index => velocity index) - InitialLift.coefficients 0) = _
  rw [map_sub]
  rfl

theorem velocityRead_increment (velocity : PhysicalSpace) :
    velocityRead (materialIncrement velocity) = velocity := by
  rw [materialIncrement_eq, map_sub, velocityRead_matter, velocityRead_matter, sub_zero]

theorem velocityRead_comp_increment : velocityRead.comp materialIncrement = ContinuousLinearMap.id ℝ PhysicalSpace := by
  apply ContinuousLinearMap.ext
  intro velocity
  exact velocityRead_increment velocity

theorem materialIncrement_injective : Function.Injective materialIncrement :=
  Function.LeftInverse.injective velocityRead_increment

theorem materialIncrement_rawDerivative (derivative : Fin 4 → PhysicalSpace) (direction : Fin 4) :
    materialIncrement (derivative direction) = matterCoordinateEquiv
      (NativeSourceMaterialAdjoint.rawDerivative derivative direction) := by
  rw [materialIncrement_eq, source_matter, source_matter, ← map_sub, ← map_sub]
  congr 2
  ext row column
  fin_cases row <;> fin_cases column <;>
    simp [hermitianBlock, normalizedVelocity,
      NativePauliJet.tangent, NativeMaterialJetAction.normalizedJet, pauli, Fin.sum_univ_three]

/-- The original connection term is retained when the full covariant jet is read as a physical derivative. -/
theorem covariant_readback (velocity : PhysicalSpace) (derivative : Fin 4 → PhysicalSpace) (direction : Fin 4) :
    velocityRead (matterCoordinateEquiv (NativeBalancedMaterialJet.derivative velocity derivative direction)) =
      derivative direction + velocityRead (matterCoordinateEquiv
        (NativeBalancedMaterialJet.connectionOperator velocity derivative direction
          (NativeCanonicalFluidCoframe.matter velocity))) := by
  rw [NativeBalancedMaterialJet.derivative, map_add, map_add, ← materialIncrement_rawDerivative,
    velocityRead_increment]

end
end SaturationMonoid.NavierStokes.NativeMaterialReadback
