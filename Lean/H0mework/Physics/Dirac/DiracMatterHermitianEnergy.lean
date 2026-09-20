import H0mework.Physics.Coframe.CurrentCoframeMatterTimeResponse
import Mathlib.Analysis.Matrix.Hermitian
import Mathlib.Analysis.Matrix.PosDef

/-!
# Hermitian energy for the Stage-9 Dirac matter carrier

The current-coframe evolution coefficients act on the four Dirac coordinates
and leave the finite internal exterior-matter carrier untouched.  This module
chooses a faithful finite internal coordinate system and sums the standard
Dirac Hermitian forms over it.  Hermitian coefficients therefore give real
fluxes, while a positive-definite time coefficient gives a strictly positive
energy on the full Dirac-exterior carrier.

The chosen basis is only a proof coordinate for the energy readout.  It does
not enter an action write, a residual, or a solution constructor.
-/

namespace SaturationMonoid.PhysicsCore.StageNineDiracMatterHermitianEnergy

open DiracCliffordRepresentation
open DiracExteriorMatterAction
open SU7ExteriorMatterRepresentation
open scoped ComplexOrder Matrix

noncomputable section

abbrev InternalMatterCoordinateIndex :=
  Module.Free.ChooseBasisIndex ℂ SU7ExteriorSpinorMatterCarrier

local instance internalMatterCoordinateIndexFintype :
    Fintype InternalMatterCoordinateIndex :=
  Fintype.ofFinite InternalMatterCoordinateIndex

/-- One faithful complex coordinate of the finite internal matter carrier. -/
def internalMatterCoordinate
    (index : InternalMatterCoordinateIndex) :
    Module.Dual ℂ SU7ExteriorSpinorMatterCarrier where
  toFun field :=
    (Module.Free.chooseBasis ℂ SU7ExteriorSpinorMatterCarrier).repr field index
  map_add' first second := by simp
  map_smul' scalar field := by simp

/-- Sum of the standard Dirac pairings over faithful internal coordinates. -/
def diracExteriorMatterCoordinatePairing
    (first second : DiracExteriorMatterCarrier) : ℂ :=
  ∑ internal : InternalMatterCoordinateIndex,
    star (fun spin => internalMatterCoordinate internal (first spin)) ⬝ᵥ
      (fun spin => internalMatterCoordinate internal (second spin))

/-- The energy pairing is complex-linear in its second matter field. -/
def diracExteriorMatterCoordinatePairingRight
    (first : DiracExteriorMatterCarrier) :
    DiracExteriorMatterCarrier →ₗ[ℂ] ℂ where
  toFun second := diracExteriorMatterCoordinatePairing first second
  map_add' second third := by
    unfold diracExteriorMatterCoordinatePairing
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro internal _
    simp only [Pi.add_apply, map_add]
    unfold dotProduct
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro spin _
    ring
  map_smul' scalar second := by
    unfold diracExteriorMatterCoordinatePairing
    simp only [RingHom.id_apply, smul_eq_mul, Pi.smul_apply, map_smul]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro internal _
    unfold dotProduct
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro spin _
    ring

@[simp] theorem diracExteriorMatterCoordinatePairingRight_apply
    (first second : DiracExteriorMatterCarrier) :
    diracExteriorMatterCoordinatePairingRight first second =
      diracExteriorMatterCoordinatePairing first second :=
  rfl

theorem diracExteriorMatterCoordinatePairing_sum_right
    {index : Type*} [Fintype index]
    (first : DiracExteriorMatterCarrier)
    (family : index → DiracExteriorMatterCarrier) :
    diracExteriorMatterCoordinatePairing first (∑ i, family i) =
      ∑ i, diracExteriorMatterCoordinatePairing first (family i) := by
  change
    diracExteriorMatterCoordinatePairingRight first (∑ i, family i) =
      ∑ i, diracExteriorMatterCoordinatePairingRight first (family i)
  rw [map_sum]

theorem internalMatterCoordinate_diracMatrixMatterAction
    (matrix : DiracMatrix)
    (field : DiracExteriorMatterCarrier)
    (row : DiracSpinorIndex)
    (internal : InternalMatterCoordinateIndex) :
    internalMatterCoordinate internal
        (diracMatrixMatterAction matrix field row) =
      ∑ column : DiracSpinorIndex,
        matrix row column * internalMatterCoordinate internal (field column) := by
  simp [diracMatrixMatterAction, internalMatterCoordinate]

/-- A Dirac matrix acts independently on every faithful internal coordinate. -/
theorem diracExteriorMatterCoordinatePairing_action
    (matrix : DiracMatrix)
    (field : DiracExteriorMatterCarrier) :
    diracExteriorMatterCoordinatePairing field
        (diracMatrixMatterAction matrix field) =
      ∑ internal : InternalMatterCoordinateIndex,
        star (fun spin => internalMatterCoordinate internal (field spin)) ⬝ᵥ
          (matrix *ᵥ
            (fun spin => internalMatterCoordinate internal (field spin))) := by
  unfold diracExteriorMatterCoordinatePairing
  apply Finset.sum_congr rfl
  intro internal _
  congr 1
  funext row
  exact internalMatterCoordinate_diracMatrixMatterAction
    matrix field row internal

/-- Hermitian Dirac coefficients give real fluxes on the full matter carrier. -/
theorem diracExteriorMatterCoordinatePairing_action_im_zero
    (matrix : DiracMatrix)
    (hermitian : Matrix.IsHermitian matrix)
    (field : DiracExteriorMatterCarrier) :
    (diracExteriorMatterCoordinatePairing field
      (diracMatrixMatterAction matrix field)).im = 0 := by
  rw [diracExteriorMatterCoordinatePairing_action]
  rw [Complex.im_sum]
  exact Finset.sum_eq_zero fun internal _ =>
    hermitian.im_star_dotProduct_mulVec_self
      (fun spin => internalMatterCoordinate internal (field spin))

/-- In particular, every current-coframe evolution coefficient has real flux. -/
theorem coframeCoordinateDiracEvolutionPrincipal_pairing_im_zero
    (coframe : LorentzianCoframe)
    (coordinate : LorentzianIndex)
    (field : DiracExteriorMatterCarrier) :
    (diracExteriorMatterCoordinatePairing field
      (diracMatrixMatterAction
        (coframeCoordinateDiracEvolutionPrincipal coframe coordinate)
        field)).im = 0 :=
  diracExteriorMatterCoordinatePairing_action_im_zero _
    (coframeCoordinateDiracEvolutionPrincipal_isHermitian coframe coordinate)
    field

theorem diracExteriorMatterCoordinateFamily_eq_zero_iff
    (field : DiracExteriorMatterCarrier) :
    (∀ internal : InternalMatterCoordinateIndex,
      (fun spin => internalMatterCoordinate internal (field spin)) = 0) ↔
      field = 0 := by
  constructor
  · intro coordinatesZero
    funext spin
    apply (Module.Free.chooseBasis ℂ SU7ExteriorSpinorMatterCarrier).repr.injective
    ext internal
    simpa [internalMatterCoordinate] using
      congrFun (coordinatesZero internal) spin
  · rintro rfl internal
    funext spin
    simp [internalMatterCoordinate]

/-- Real energy induced by one Dirac matrix on the full matter carrier. -/
def diracExteriorMatterCoordinateEnergy
    (matrix : DiracMatrix)
    (field : DiracExteriorMatterCarrier) : ℝ :=
  (diracExteriorMatterCoordinatePairing field
    (diracMatrixMatterAction matrix field)).re

theorem diracExteriorMatterCoordinateEnergy_nonneg
    (matrix : DiracMatrix)
    (positive : Matrix.PosSemidef matrix)
    (field : DiracExteriorMatterCarrier) :
    0 ≤ diracExteriorMatterCoordinateEnergy matrix field := by
  rw [diracExteriorMatterCoordinateEnergy,
    diracExteriorMatterCoordinatePairing_action, Complex.re_sum]
  exact Finset.sum_nonneg fun internal _ =>
    positive.re_dotProduct_nonneg
      (fun spin => internalMatterCoordinate internal (field spin))

/-- A positive-definite time coefficient gives strict full-carrier energy. -/
theorem diracExteriorMatterCoordinateEnergy_pos
    (matrix : DiracMatrix)
    (positive : Matrix.PosDef matrix)
    (field : DiracExteriorMatterCarrier)
    (fieldNonzero : field ≠ 0) :
    0 < diracExteriorMatterCoordinateEnergy matrix field := by
  rw [diracExteriorMatterCoordinateEnergy,
    diracExteriorMatterCoordinatePairing_action, Complex.re_sum]
  apply (Finset.sum_pos_iff_of_nonneg fun internal _ =>
    positive.posSemidef.re_dotProduct_nonneg
      (fun spin => internalMatterCoordinate internal (field spin))).2
  have coordinateNonzero :
      ∃ internal : InternalMatterCoordinateIndex,
        (fun spin => internalMatterCoordinate internal (field spin)) ≠ 0 := by
    by_contra allZero
    push Not at allZero
    exact fieldNonzero
      ((diracExteriorMatterCoordinateFamily_eq_zero_iff field).mp allZero)
  obtain ⟨internal, internalNonzero⟩ := coordinateNonzero
  exact ⟨internal, Finset.mem_univ internal,
    positive.re_dotProduct_pos internalNonzero⟩

theorem diracExteriorMatterCoordinateEnergy_eq_zero_iff
    (matrix : DiracMatrix)
    (positive : Matrix.PosDef matrix)
    (field : DiracExteriorMatterCarrier) :
    diracExteriorMatterCoordinateEnergy matrix field = 0 ↔ field = 0 := by
  constructor
  · intro energyZero
    by_contra fieldNonzero
    exact (diracExteriorMatterCoordinateEnergy_pos
      matrix positive field fieldNonzero).ne' energyZero
  · rintro rfl
    simp [diracExteriorMatterCoordinateEnergy,
      diracExteriorMatterCoordinatePairing]

end

end SaturationMonoid.PhysicsCore.StageNineDiracMatterHermitianEnergy
