import H0mework.Physics.DiracEvolution.WeakSpatialGalerkinMass

/-!
# Fiberwise Riesz form of the Dirac matter mass pairing

The action-owned real Hermitian fiber pairing is packaged as one continuous
bilinear map and represented canonically in the matter coordinate Hilbert
space.  This is the finite-dimensional seam used by the spatial `L²`
actualization; it does not choose a continuum field or solve an equation.
-/

namespace SaturationMonoid.PhysicsCore.StageNineDiracMatterFiberMassRiesz

open DiracExteriorMatterAction
open DiracCliffordRepresentation
open StageNineDiracMatterCoordinateCalculus
open StageNineDiracMatterHermitianEnergy
open StageNineDiracMatterWeakSpatialGalerkinMass
open StageNineHolonomicField
open scoped Matrix.Norms.Elementwise

noncomputable section

set_option autoImplicit false

private def matterFiberMassSecondLinear
    (matrix : DiracMatrix)
    (first : MatterCoordinateCarrier) :
    MatterCoordinateCarrier →ₗ[ℝ] ℝ where
  toFun second :=
    diracExteriorMatterEnergyPairing matrix
      (matterCoordinateEquiv.symm first)
      (matterCoordinateEquiv.symm second)
  map_add' second third := by
    rw [map_add, diracExteriorMatterEnergyPairing_add_right]
  map_smul' parameter second := by
    change
      diracExteriorMatterEnergyPairing matrix
          (matterCoordinateEquiv.symm first)
          (matterCoordinateEquiv.symm ((parameter : ℂ) • second)) = _
    rw [map_smul]
    have coeSmul :=
      Complex.coe_smul parameter (matterCoordinateEquiv.symm second)
    rw [coeSmul]
    exact diracExteriorMatterEnergyPairing_real_smul_right matrix
      parameter (matterCoordinateEquiv.symm first)
        (matterCoordinateEquiv.symm second)

private def matterFiberMassSecondCLM
    (matrix : DiracMatrix)
    (first : MatterCoordinateCarrier) :
    MatterCoordinateCarrier →L[ℝ] ℝ :=
  ⟨matterFiberMassSecondLinear matrix first,
    (matterFiberMassSecondLinear matrix first).continuous_of_finiteDimensional⟩

private def matterFiberMassFirstLinear
    (matrix : DiracMatrix) :
    MatterCoordinateCarrier →ₗ[ℝ]
      (MatterCoordinateCarrier →L[ℝ] ℝ) where
  toFun := matterFiberMassSecondCLM matrix
  map_add' first second := by
    ext third
    change
      diracExteriorMatterEnergyPairing matrix
          (matterCoordinateEquiv.symm (first + second))
          (matterCoordinateEquiv.symm third) = _
    rw [map_add]
    exact diracExteriorMatterEnergyPairing_add_left matrix
      (matterCoordinateEquiv.symm first)
      (matterCoordinateEquiv.symm second)
      (matterCoordinateEquiv.symm third)
  map_smul' parameter first := by
    ext second
    change
      diracExteriorMatterEnergyPairing matrix
          (matterCoordinateEquiv.symm ((parameter : ℂ) • first))
          (matterCoordinateEquiv.symm second) =
        parameter • diracExteriorMatterEnergyPairing matrix
          (matterCoordinateEquiv.symm first)
          (matterCoordinateEquiv.symm second)
    rw [map_smul]
    have coeSmul :=
      Complex.coe_smul parameter (matterCoordinateEquiv.symm first)
    rw [coeSmul]
    exact diracExteriorMatterEnergyPairing_real_smul_left matrix
      parameter (matterCoordinateEquiv.symm first)
        (matterCoordinateEquiv.symm second)

private def matterFiberMassFirstCLM
    (matrix : DiracMatrix) :
    MatterCoordinateCarrier →L[ℝ]
      (MatterCoordinateCarrier →L[ℝ] ℝ) :=
  ⟨matterFiberMassFirstLinear matrix,
    (matterFiberMassFirstLinear matrix).continuous_of_finiteDimensional⟩

private def matterFiberMassMatrixLinear :
    DiracMatrix →ₗ[ℝ]
      (MatterCoordinateCarrier →L[ℝ]
        (MatterCoordinateCarrier →L[ℝ] ℝ)) where
  toFun := matterFiberMassFirstCLM
  map_add' first second := by
    ext firstField secondField
    change
      diracExteriorMatterEnergyPairing (first + second)
          (matterCoordinateEquiv.symm firstField)
          (matterCoordinateEquiv.symm secondField) =
        diracExteriorMatterEnergyPairing first
            (matterCoordinateEquiv.symm firstField)
            (matterCoordinateEquiv.symm secondField) +
          diracExteriorMatterEnergyPairing second
            (matterCoordinateEquiv.symm firstField)
            (matterCoordinateEquiv.symm secondField)
    unfold diracExteriorMatterEnergyPairing
    rw [diracMatrixMatterAction_add_matrix]
    change
      ((diracExteriorMatterCoordinatePairingRight
          (matterCoordinateEquiv.symm firstField))
        ((diracMatrixMatterAction first)
            (matterCoordinateEquiv.symm secondField) +
          (diracMatrixMatterAction second)
            (matterCoordinateEquiv.symm secondField))).re = _
    rw [map_add, Complex.add_re]
    simp only [diracExteriorMatterCoordinatePairingRight_apply]
  map_smul' parameter matrix := by
    ext firstField secondField
    change
      diracExteriorMatterEnergyPairing ((parameter : ℂ) • matrix)
          (matterCoordinateEquiv.symm firstField)
          (matterCoordinateEquiv.symm secondField) =
        parameter * diracExteriorMatterEnergyPairing matrix
          (matterCoordinateEquiv.symm firstField)
          (matterCoordinateEquiv.symm secondField)
    unfold diracExteriorMatterEnergyPairing
    rw [diracMatrixMatterAction_smul_matrix]
    change
      ((diracExteriorMatterCoordinatePairingRight
          (matterCoordinateEquiv.symm firstField))
        ((parameter : ℂ) •
          (diracMatrixMatterAction matrix)
            (matterCoordinateEquiv.symm secondField))).re = _
    rw [map_smul]
    simp

/-- The physical fiber mass pairing as one continuous real trilinear map. -/
def matterFiberMassPairing :
    DiracMatrix →L[ℝ]
      (MatterCoordinateCarrier →L[ℝ]
        (MatterCoordinateCarrier →L[ℝ] ℝ)) :=
  (LinearMap.toContinuousLinearMap
    (𝕜 := ℝ)
    (E := DiracMatrix)
    (F' := MatterCoordinateCarrier →L[ℝ]
      (MatterCoordinateCarrier →L[ℝ] ℝ)))
    matterFiberMassMatrixLinear

@[simp] theorem matterFiberMassPairing_apply
    (matrix : DiracMatrix)
    (first second : MatterCoordinateCarrier) :
    matterFiberMassPairing matrix first second =
      diracExteriorMatterEnergyPairing matrix
        (matterCoordinateEquiv.symm first)
        (matterCoordinateEquiv.symm second) :=
  rfl

/-- Canonical Riesz representative of the physical fiber mass pairing. -/
def matterFiberMassRiesz
    (matrix : DiracMatrix)
    (first : MatterCoordinateCarrier) : MatterCoordinateCarrier :=
  (InnerProductSpace.toDual ℝ MatterCoordinateCarrier).symm
    (matterFiberMassPairing matrix first)

theorem matterFiberMassRiesz_pairing
    (matrix : DiracMatrix)
    (first second : MatterCoordinateCarrier) :
    inner ℝ (matterFiberMassRiesz matrix first) second =
      matterFiberMassPairing matrix first second := by
  rw [matterFiberMassRiesz, InnerProductSpace.toDual_symm_apply]

theorem norm_matterFiberMassRiesz_le
    (matrix : DiracMatrix)
    (first : MatterCoordinateCarrier) :
    ‖matterFiberMassRiesz matrix first‖ ≤
      ‖matterFiberMassPairing matrix‖ * ‖first‖ := by
  rw [matterFiberMassRiesz,
    (InnerProductSpace.toDual ℝ MatterCoordinateCarrier).symm.norm_map]
  exact (matterFiberMassPairing matrix).le_opNorm first

end

end SaturationMonoid.PhysicsCore.StageNineDiracMatterFiberMassRiesz
