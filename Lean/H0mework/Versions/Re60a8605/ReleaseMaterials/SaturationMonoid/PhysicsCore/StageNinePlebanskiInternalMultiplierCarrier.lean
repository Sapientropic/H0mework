import H0mework.Physics.Dirac.PhysicalBivectorSpinRepresentation
import H0mework.Physics.Geometry.TopologicalFourFormPairing

/-!
# J1: standard nonchiral Plebanski internal multiplier carrier

This module fixes the gravity multiplier representation independently of any
candidate world.  In the oriented internal-pair order
`(01, 02, 03, 23, 31, 12)`, a raw multiplier is a real `6 × 6` tensor.  The
standard carrier is the intersection of the pair-exchange-symmetric subspace
with the kernel of the contravariant epsilon trace.  This is the coordinate
form of the nonchiral Plebanski multiplier convention

`φ_[IJ][KL] = φ_[KL][IJ]`, `ε^{IJKL} φ_IJKL = 0`

used by Alexandrov--Krasnov, arXiv:0809.4763, equations (3)--(4).  The
convention here is `η = diag(-,+,+,+)` and `ε₀₁₂₃ = +1`, hence
`ε⁰¹²³ = -1`; the full ordered-index contraction is four times
`epsilonTrace`.

The Spin action is generated from the existing `spinLorentzCover` and acts by
inverse pullback on both internal pair legs.  It is not the existing
`PhysicalBivector` action, whose second `Fin 6` index is spacetime.  The
epsilon trace transforms by the actual exterior-square volume character, so
its zero fiber is invariant without accepting covariance, normalization, a
multiplier value, or a branch receipt as a premise.

The final regressions certify a legal nonzero diagonal mode, rejection of the
epsilon direction, rejection of a trace-free nonsymmetric mode, nontrivial
Spin action, faithful zero fiber, and the expected central-sign kernel.  This
is representation infrastructure only.  It does not define the root action,
its variations, or identify the existing 36-component gravity auxiliary with
the standard multiplier; that identification is the next reaction-image
compatibility gate.
-/

namespace SaturationMonoid.PhysicsCore.StageNinePlebanskiInternalMultiplierCarrier

open ProofFreeRicherAnholonomicSource
open StageNineBlockwiseConstitutive
open StageNineGlobalIntegratedAction
open StageNineCoframeTwoFormPairing
open StageNineGlobalBundle
open StageNineLorentzCoverAndSpinDescent
open StageNinePhysicalBivectorSpinRepresentation
open StageNineSpinMatterBundle
open StageNineTopologicalFourFormPairing

noncomputable section

set_option autoImplicit false

def epsilonPairing (first second : GaugeTwoForm) : ℝ :=
  ∑ pair : Fin 6,
    lorentzianTwoFormSign pair * first pair *
      lorentzianCoframeHodge second pair

/-- J1 uses the contravariant epsilon convention `epsilon^0123 = -1`.
The formulation-neutral lower-orientation wedge carrier instead fixes
`epsilon_0123 = +1`, so the two finite-coordinate pairings differ by exactly
one global minus sign.  This theorem keeps J1 diagnostic infrastructure tied
to the common orientation authority without making J1 the root-action
producer. -/
theorem epsilonPairing_eq_neg_orientedTwoFormWedgeCoefficient
    (first second : GaugeTwoForm) :
    epsilonPairing first second =
      -orientedTwoFormWedgeCoefficient first second := by
  simp [epsilonPairing, orientedTwoFormWedgeCoefficient_explicit,
    lorentzianTwoFormSign, minkowskiInternalSign,
    pairFirst, pairSecond, lorentzianCoframeHodge, Fin.sum_univ_six]
  ring

def timeSpaceBasis : GaugeTwoForm :=
  fun pair => if pair = 0 then 1 else 0

def spatialBasis : GaugeTwoForm :=
  fun pair => if pair = 3 then 1 else 0

def exteriorSquareVolumeScale (coframe : LorentzianCoframe) : ℝ :=
  -epsilonPairing (coframeTwoFormLinear coframe timeSpaceBasis)
    (coframeTwoFormLinear coframe spatialBasis)

abbrev InternalPairTensor := Matrix (Fin 6) (Fin 6) ℝ

def coframeTwoFormMatrix (coframe : LorentzianCoframe) :
    InternalPairTensor :=
  fun firstPair secondPair => coframeWedge coframe firstPair secondPair

def epsilonTrace (tensor : InternalPairTensor) : ℝ :=
  -(tensor 0 3 + tensor 3 0 + tensor 1 4 + tensor 4 1 +
    tensor 2 5 + tensor 5 2)

def pullbackTensor
    (coframe : LorentzianCoframe) (tensor : InternalPairTensor) :
    InternalPairTensor :=
  Matrix.transpose (coframeTwoFormMatrix coframe) * tensor *
    coframeTwoFormMatrix coframe

theorem epsilonPairing_coframeTwoFormLinear
    (coframe : LorentzianCoframe) (first second : GaugeTwoForm) :
    epsilonPairing (coframeTwoFormLinear coframe first)
        (coframeTwoFormLinear coframe second) =
      exteriorSquareVolumeScale coframe * epsilonPairing first second := by
  simp [epsilonPairing, coframeTwoFormLinear, coframeWedge,
    exteriorSquareVolumeScale, timeSpaceBasis, spatialBasis,
    lorentzianTwoFormSign, minkowskiInternalSign, pairFirst, pairSecond,
    lorentzianCoframeHodge, Fin.sum_univ_six]
  ring

theorem epsilonTrace_pullbackTensor
    (coframe : LorentzianCoframe) (tensor : InternalPairTensor) :
    epsilonTrace (pullbackTensor coframe tensor) =
      exteriorSquareVolumeScale coframe * epsilonTrace tensor := by
  simp [epsilonTrace, pullbackTensor, exteriorSquareVolumeScale,
    epsilonPairing, coframeTwoFormMatrix, Matrix.mul_apply,
    coframeTwoFormLinear, coframeWedge,
    timeSpaceBasis, spatialBasis, lorentzianTwoFormSign,
    minkowskiInternalSign, pairFirst, pairSecond,
    lorentzianCoframeHodge, Fin.sum_univ_six]
  ring

@[simp] theorem coframeTwoFormLinear_toMatrix'
    (coframe : LorentzianCoframe) :
    LinearMap.toMatrix' (coframeTwoFormLinear coframe) =
      coframeTwoFormMatrix coframe := by
  ext target source
  simp [coframeTwoFormMatrix, LinearMap.toMatrix'_apply,
    coframeTwoFormLinear,
    Pi.single_apply]

@[simp] theorem coframeTwoFormMatrix_one :
    coframeTwoFormMatrix (1 : LorentzianCoframe) = 1 := by
  rw [← coframeTwoFormLinear_toMatrix', coframeTwoFormLinear_one]
  exact LinearMap.toMatrix'_id

theorem coframeTwoFormMatrix_mul
    (first second : LorentzianCoframe) :
    coframeTwoFormMatrix (first * second) =
      coframeTwoFormMatrix first * coframeTwoFormMatrix second := by
  rw [← coframeTwoFormLinear_toMatrix', coframeTwoFormLinear_mul,
    LinearMap.toMatrix'_comp, coframeTwoFormLinear_toMatrix',
    coframeTwoFormLinear_toMatrix']

theorem pullbackTensor_comp
    (first second : LorentzianCoframe) (tensor : InternalPairTensor) :
    pullbackTensor first (pullbackTensor second tensor) =
      pullbackTensor (second * first) tensor := by
  simp [pullbackTensor, coframeTwoFormMatrix_mul, Matrix.transpose_mul,
    Matrix.mul_assoc]

def rawMultiplierSpinLinearEquiv (groupElement : SpinPlus13) :
    InternalPairTensor ≃ₗ[ℝ] InternalPairTensor :=
  { toFun := pullbackTensor (spinLorentzMatrix groupElement⁻¹)
    invFun := pullbackTensor (spinLorentzMatrix groupElement)
    left_inv := by
      intro tensor
      rw [pullbackTensor_comp, ← map_mul spinLorentzMatrix]
      simp [pullbackTensor]
    right_inv := by
      intro tensor
      rw [pullbackTensor_comp, ← map_mul spinLorentzMatrix]
      simp [pullbackTensor]
    map_add' := by
      intro first second
      simp [pullbackTensor, Matrix.mul_add, Matrix.add_mul]
    map_smul' := by
      intro scalar tensor
      simp [pullbackTensor] }

@[simp] theorem rawMultiplierSpinLinearEquiv_apply
    (groupElement : SpinPlus13) (tensor : InternalPairTensor) :
    rawMultiplierSpinLinearEquiv groupElement tensor =
      pullbackTensor (spinLorentzMatrix groupElement⁻¹) tensor :=
  rfl

theorem rawMultiplierSpinLinearEquiv_preserves_symmetry
    (groupElement : SpinPlus13) (tensor : InternalPairTensor)
    (symmetric : tensor.IsSymm) :
    (rawMultiplierSpinLinearEquiv groupElement tensor).IsSymm := by
  rw [rawMultiplierSpinLinearEquiv_apply]
  simp [pullbackTensor, Matrix.IsSymm, Matrix.transpose_mul,
    symmetric.eq, Matrix.mul_assoc]

theorem rawMultiplierSpinLinearEquiv_epsilonTrace
    (groupElement : SpinPlus13) (tensor : InternalPairTensor) :
    epsilonTrace (rawMultiplierSpinLinearEquiv groupElement tensor) =
      exteriorSquareVolumeScale (spinLorentzMatrix groupElement⁻¹) *
        epsilonTrace tensor := by
  rw [rawMultiplierSpinLinearEquiv_apply]
  exact epsilonTrace_pullbackTensor _ _

def rawMultiplierSpinRepresentation :
    SpinPlus13 →* (InternalPairTensor ≃ₗ[ℝ] InternalPairTensor) where
  toFun := rawMultiplierSpinLinearEquiv
  map_one' := by
    apply LinearEquiv.ext
    intro tensor
    simp [rawMultiplierSpinLinearEquiv, pullbackTensor]
  map_mul' first second := by
    apply LinearEquiv.ext
    intro tensor
    change pullbackTensor (spinLorentzMatrix (first * second)⁻¹) tensor =
      pullbackTensor (spinLorentzMatrix first⁻¹)
        (pullbackTensor (spinLorentzMatrix second⁻¹) tensor)
    rw [pullbackTensor_comp, mul_inv_rev, map_mul spinLorentzMatrix]

def pairExchangeDefect :
    InternalPairTensor →ₗ[ℝ] InternalPairTensor :=
  (Matrix.transposeLinearEquiv (Fin 6) (Fin 6) ℝ ℝ).toLinearMap -
    LinearMap.id

def epsilonTraceLinearMap : InternalPairTensor →ₗ[ℝ] ℝ where
  toFun := epsilonTrace
  map_add' := by
    intro first second
    simp [epsilonTrace]
    ring
  map_smul' := by
    intro scalar tensor
    simp [epsilonTrace]
    ring

def standardPlebanskiMultiplierSpace :
    Submodule ℝ InternalPairTensor :=
  pairExchangeDefect.ker ⊓ epsilonTraceLinearMap.ker

abbrev StandardPlebanskiMultiplier := standardPlebanskiMultiplierSpace

theorem mem_standardPlebanskiMultiplierSpace_iff
    (tensor : InternalPairTensor) :
    tensor ∈ standardPlebanskiMultiplierSpace ↔
      tensor.IsSymm ∧ epsilonTrace tensor = 0 := by
  simp [standardPlebanskiMultiplierSpace, pairExchangeDefect,
    epsilonTraceLinearMap, Matrix.IsSymm, sub_eq_zero]

theorem rawMultiplierSpinLinearEquiv_preserves_standardSpace
    (groupElement : SpinPlus13) (tensor : InternalPairTensor)
    (membership : tensor ∈ standardPlebanskiMultiplierSpace) :
    rawMultiplierSpinLinearEquiv groupElement tensor ∈
      standardPlebanskiMultiplierSpace := by
  rw [mem_standardPlebanskiMultiplierSpace_iff] at membership ⊢
  refine ⟨rawMultiplierSpinLinearEquiv_preserves_symmetry
    groupElement tensor membership.1, ?_⟩
  rw [rawMultiplierSpinLinearEquiv_epsilonTrace, membership.2, mul_zero]

theorem rawMultiplierSpinLinearEquiv_map_standardSpace
    (groupElement : SpinPlus13) :
    standardPlebanskiMultiplierSpace.map
        (rawMultiplierSpinLinearEquiv groupElement).toLinearMap =
      standardPlebanskiMultiplierSpace := by
  apply le_antisymm
  · rintro tensor ⟨source, sourceMembership, rfl⟩
    exact rawMultiplierSpinLinearEquiv_preserves_standardSpace
      groupElement source sourceMembership
  · intro tensor tensorMembership
    refine ⟨rawMultiplierSpinLinearEquiv groupElement⁻¹ tensor,
      rawMultiplierSpinLinearEquiv_preserves_standardSpace
        groupElement⁻¹ tensor tensorMembership, ?_⟩
    rw [rawMultiplierSpinLinearEquiv_apply]
    change pullbackTensor (spinLorentzMatrix groupElement⁻¹)
      (pullbackTensor (spinLorentzMatrix groupElement⁻¹⁻¹) tensor) = tensor
    rw [inv_inv, pullbackTensor_comp, ← map_mul spinLorentzMatrix]
    simp [pullbackTensor]

def standardPlebanskiMultiplierSpinLinearEquiv
    (groupElement : SpinPlus13) :
    StandardPlebanskiMultiplier ≃ₗ[ℝ] StandardPlebanskiMultiplier :=
  (rawMultiplierSpinLinearEquiv groupElement).ofSubmodules
    standardPlebanskiMultiplierSpace standardPlebanskiMultiplierSpace
      (rawMultiplierSpinLinearEquiv_map_standardSpace groupElement)

@[simp] theorem standardPlebanskiMultiplierSpinLinearEquiv_apply
    (groupElement : SpinPlus13) (tensor : StandardPlebanskiMultiplier) :
    (standardPlebanskiMultiplierSpinLinearEquiv groupElement tensor :
        InternalPairTensor) =
      rawMultiplierSpinLinearEquiv groupElement tensor :=
  rfl

def standardPlebanskiMultiplierSpinRepresentation :
    SpinPlus13 →* (StandardPlebanskiMultiplier ≃ₗ[ℝ]
      StandardPlebanskiMultiplier) where
  toFun := standardPlebanskiMultiplierSpinLinearEquiv
  map_one' := by
    apply LinearEquiv.ext
    intro tensor
    apply Subtype.ext
    change rawMultiplierSpinRepresentation 1 tensor = tensor
    rw [map_one]
    rfl
  map_mul' first second := by
    apply LinearEquiv.ext
    intro tensor
    apply Subtype.ext
    change rawMultiplierSpinRepresentation (first * second) tensor =
      rawMultiplierSpinRepresentation first
        (rawMultiplierSpinRepresentation second tensor)
    rw [map_mul]
    rfl

def contravariantEpsilonPairTensor : InternalPairTensor :=
  fun firstPair secondPair =>
    epsilonPairing (Pi.single firstPair 1) (Pi.single secondPair 1)

theorem contravariantEpsilonPairTensor_coordinates :
    contravariantEpsilonPairTensor 0 3 = -1 ∧
    contravariantEpsilonPairTensor 3 0 = -1 ∧
    contravariantEpsilonPairTensor 1 4 = -1 ∧
    contravariantEpsilonPairTensor 4 1 = -1 ∧
    contravariantEpsilonPairTensor 2 5 = -1 ∧
    contravariantEpsilonPairTensor 5 2 = -1 := by
  simp (disch := decide) [contravariantEpsilonPairTensor, epsilonPairing,
    lorentzianTwoFormSign,
    minkowskiInternalSign, pairFirst, pairSecond,
    lorentzianCoframeHodge, Pi.single_apply]

theorem contravariantEpsilonPairTensor_isSymm :
    contravariantEpsilonPairTensor.IsSymm := by
  apply Matrix.IsSymm.ext
  intro firstPair secondPair
  simpa [contravariantEpsilonPairTensor, epsilonPairing, mul_comm,
    mul_left_comm, mul_assoc] using
    fixedLorentzTwoFormPairing_hodge_symmetric
      (Pi.single secondPair 1) (Pi.single firstPair 1)

theorem epsilonTrace_contravariantEpsilonPairTensor :
    epsilonTrace contravariantEpsilonPairTensor = 6 := by
  rcases contravariantEpsilonPairTensor_coordinates with
    ⟨coordinate03, coordinate30, coordinate14, coordinate41,
      coordinate25, coordinate52⟩
  simp only [epsilonTrace]
  rw [coordinate03, coordinate30, coordinate14, coordinate41,
    coordinate25, coordinate52]
  norm_num

theorem contravariantEpsilonPairTensor_not_mem_standardSpace :
    contravariantEpsilonPairTensor ∉ standardPlebanskiMultiplierSpace := by
  rw [mem_standardPlebanskiMultiplierSpace_iff]
  intro membership
  rw [epsilonTrace_contravariantEpsilonPairTensor] at membership
  norm_num at membership

def legalDiagonalTensor : InternalPairTensor :=
  fun firstPair secondPair =>
    if firstPair = 0 ∧ secondPair = 0 then 1 else 0

theorem legalDiagonalTensor_isSymm : legalDiagonalTensor.IsSymm := by
  apply Matrix.IsSymm.ext
  intro firstPair secondPair
  simp only [legalDiagonalTensor]
  by_cases firstPair = 0 <;> by_cases secondPair = 0 <;> simp_all

theorem epsilonTrace_legalDiagonalTensor :
    epsilonTrace legalDiagonalTensor = 0 := by
  simp (disch := decide) [epsilonTrace, legalDiagonalTensor]

def legalDiagonalMultiplier : StandardPlebanskiMultiplier :=
  ⟨legalDiagonalTensor, by
    rw [mem_standardPlebanskiMultiplierSpace_iff]
    exact ⟨legalDiagonalTensor_isSymm,
      epsilonTrace_legalDiagonalTensor⟩⟩

@[simp] theorem legalDiagonalMultiplier_origin :
    (legalDiagonalMultiplier : InternalPairTensor) 0 0 = 1 := by
  simp [legalDiagonalMultiplier, legalDiagonalTensor]

theorem pullbackTensor_legalDiagonalTensor
    (coframe : LorentzianCoframe) (firstPair secondPair : Fin 6) :
    pullbackTensor coframe legalDiagonalTensor firstPair secondPair =
      coframeTwoFormMatrix coframe 0 firstPair *
        coframeTwoFormMatrix coframe 0 secondPair := by
  simp [pullbackTensor, Matrix.mul_apply, legalDiagonalTensor,
    Fin.sum_univ_six]

theorem coframeTwoFormMatrix_spinDilation_zero_zero :
    coframeTwoFormMatrix (spinLorentzMatrix spinDilation) 0 0 = 17 / 8 := by
  have three_ne_zero : (3 : LorentzianIndex) ≠ 0 := by decide
  simp only [coframeTwoFormMatrix, coframeWedge, pairFirst, pairSecond,
    spinLorentzMatrix_apply]
  norm_num [spinLorentzCover, spinLorentzLinearEquiv,
    spinLorentzLinearMap, spinHermitianAction, pauliDecode, pauliEncode,
    spinDilation, Matrix.mul_apply, Fin.sum_univ_two,
    Matrix.conjTranspose_apply, three_ne_zero]

theorem spinDilationInverse_legalDiagonalMultiplier_component :
    (standardPlebanskiMultiplierSpinRepresentation spinDilation⁻¹
        legalDiagonalMultiplier : InternalPairTensor) 0 0 = 289 / 64 := by
  change pullbackTensor (spinLorentzMatrix (spinDilation⁻¹)⁻¹)
    legalDiagonalTensor 0 0 = 289 / 64
  rw [inv_inv, pullbackTensor_legalDiagonalTensor,
    coframeTwoFormMatrix_spinDilation_zero_zero]
  norm_num

theorem standardPlebanskiMultiplierSpinRepresentation_nontrivial :
    standardPlebanskiMultiplierSpinRepresentation spinDilation⁻¹ ≠ 1 := by
  intro representationIsTrivial
  have componentEquality := congrArg
    (fun action : StandardPlebanskiMultiplier ≃ₗ[ℝ]
        StandardPlebanskiMultiplier =>
      (action legalDiagonalMultiplier : InternalPairTensor) 0 0)
    representationIsTrivial
  rw [spinDilationInverse_legalDiagonalMultiplier_component] at componentEquality
  norm_num at componentEquality

def oneSidedOffDiagonalTensor : InternalPairTensor :=
  fun firstPair secondPair =>
    if firstPair = 0 ∧ secondPair = 1 then 1 else 0

theorem epsilonTrace_oneSidedOffDiagonalTensor :
    epsilonTrace oneSidedOffDiagonalTensor = 0 := by
  simp (disch := decide) [epsilonTrace, oneSidedOffDiagonalTensor]

theorem oneSidedOffDiagonalTensor_not_isSymm :
    ¬oneSidedOffDiagonalTensor.IsSymm := by
  intro symmetric
  have coordinateEquality := symmetric.apply 0 1
  norm_num [oneSidedOffDiagonalTensor] at coordinateEquality

theorem oneSidedOffDiagonalTensor_not_mem_standardSpace :
    oneSidedOffDiagonalTensor ∉ standardPlebanskiMultiplierSpace := by
  rw [mem_standardPlebanskiMultiplierSpace_iff]
  intro membership
  exact oneSidedOffDiagonalTensor_not_isSymm membership.1

theorem standardPlebanskiMultiplierSpinLinearEquiv_zero_iff
    (groupElement : SpinPlus13) (tensor : StandardPlebanskiMultiplier) :
    standardPlebanskiMultiplierSpinLinearEquiv groupElement tensor = 0 ↔
      tensor = 0 := by
  exact (standardPlebanskiMultiplierSpinLinearEquiv groupElement).map_eq_zero_iff

theorem spinCentralSign_standardPlebanskiMultiplierRepresentation_eq_one :
    standardPlebanskiMultiplierSpinRepresentation spinCentralSign = 1 := by
  have coverEquality : spinLorentzCover spinCentralSign = spinLorentzCover 1 :=
    spinLorentzCover_identifies_central_sign
  have matrixEquality :
      spinLorentzMatrix spinCentralSign = spinLorentzMatrix 1 := by
    change (LinearMap.toMatrixAlgEquiv basePointCoordinateBasis)
        (spinLorentzCover spinCentralSign).toLinearMap =
      (LinearMap.toMatrixAlgEquiv basePointCoordinateBasis)
        (spinLorentzCover 1).toLinearMap
    rw [coverEquality]
  have centralSquare : spinCentralSign * spinCentralSign = 1 := by
    apply Subtype.ext
    change (-1 : Matrix (Fin 2) (Fin 2) ℂ) * (-1) = 1
    simp
  have centralInverse : spinCentralSign⁻¹ = spinCentralSign :=
    inv_eq_of_mul_eq_one_right centralSquare
  have inverseMatrixEquality :
      spinLorentzMatrix spinCentralSign⁻¹ = 1 := by
    rw [centralInverse, matrixEquality, map_one]
  apply LinearEquiv.ext
  intro tensor
  apply Subtype.ext
  change pullbackTensor (spinLorentzMatrix spinCentralSign⁻¹) tensor = tensor
  rw [inverseMatrixEquality]
  simp [pullbackTensor]

end

end SaturationMonoid.PhysicsCore.StageNinePlebanskiInternalMultiplierCarrier
