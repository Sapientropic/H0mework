import H0mework.Physics.Matter.SU7ExteriorMatterRestriction
import H0mework.Physics.Gauge.SU7MotherGaugeConnection
import Mathlib.LinearAlgebra.Prod

/-!
# Gauge-covariant finite transport jet for the Stage-7 exterior matter carrier

This module attaches the actual `Λ⁶V ⊕ Λ²V ⊕ Λ⁴V` Stage-7 matter
representation to the same `SU7MotherGaugeConnection` used by Stage 6.  The
fundamental finite transport jet `1 + A` is lifted functorially to each
exterior power.  Constant/global SU(7) conjugation covariance, invariant dual
pairing, finite direction-reindex covariance, and a nonzero coupling to the
actual P286 hypercharge Lie generator are proved rather than stored.

This is the dependency-light first layer of Stage 8 checkpoint A.  It is not
yet a Dirac/Weyl matter action: the project has no generated `Spin(1,3)` lift,
spinor carrier, gamma contraction, or local-gauge derivative term.  Hence the
finite transport jet and its scalar-valued kinetic one-form must not be read
as completion of the spin/geometry gate.
-/

namespace SaturationMonoid.PhysicsCore.SU7ExteriorMatterGaugeCovariantJet

open Matrix
open SU7MotherLieAlgebra
open SU7MotherGaugeTheory
open SU7MotherMatterNormalizerNoGo
open SU7ExteriorMatterRepresentation
open SU7ExteriorMatterRestriction
open GaugeProjection.ConcreteBlockDiagonal

open scoped TensorProduct

noncomputable section

local instance : LinearOrder SU7MotherIndex :=
  LinearOrder.lift' smBlockIndexEquivFin7 smBlockIndexEquivFin7.injective

def motherGaugeConjugate
    (groupElement : SU7MotherGroup) (matrix : SU7MotherLieMatrix) :
    SU7MotherLieMatrix := by
  let g : Matrix SU7MotherIndex SU7MotherIndex ℂ := groupElement
  refine ⟨g * matrix * star g, ?_, ?_⟩
  · rw [star_mul, star_mul, star_star,
      specialUnitaryLieMatrix_star matrix]
    noncomm_ring
  · have hunitary : star g * g = 1 :=
      Matrix.mem_unitaryGroup_iff'.mp
        (Matrix.specialUnitaryGroup_le_unitaryGroup groupElement.property)
    calc
      Matrix.trace (g * (matrix : Matrix SU7MotherIndex SU7MotherIndex ℂ) * star g) =
          Matrix.trace
            (((matrix : Matrix SU7MotherIndex SU7MotherIndex ℂ) * star g) * g) := by
        rw [Matrix.mul_assoc, Matrix.trace_mul_comm]
      _ = Matrix.trace
          ((matrix : Matrix SU7MotherIndex SU7MotherIndex ℂ) * (star g * g)) := by
        rw [Matrix.mul_assoc]
      _ = Matrix.trace (matrix : Matrix SU7MotherIndex SU7MotherIndex ℂ) := by
        rw [hunitary, Matrix.mul_one]
      _ = 0 := matrix.property.2

theorem motherGaugeConjugate_add
    (groupElement : SU7MotherGroup) (first second : SU7MotherLieMatrix) :
    motherGaugeConjugate groupElement (first + second) =
      motherGaugeConjugate groupElement first +
        motherGaugeConjugate groupElement second := by
  apply Subtype.ext
  simp [motherGaugeConjugate, mul_add, add_mul]

theorem motherGaugeConjugate_bracket
    (groupElement : SU7MotherGroup) (first second : SU7MotherLieMatrix) :
    motherGaugeConjugate groupElement (suLieBracket first second) =
      suLieBracket (motherGaugeConjugate groupElement first)
        (motherGaugeConjugate groupElement second) := by
  apply Subtype.ext
  let g : Matrix SU7MotherIndex SU7MotherIndex ℂ := groupElement
  have hunitary : star g * g = 1 :=
    Matrix.mem_unitaryGroup_iff'.mp
      (Matrix.specialUnitaryGroup_le_unitaryGroup groupElement.property)
  change
    g * (((first : Matrix SU7MotherIndex SU7MotherIndex ℂ) * second) -
        ((second : Matrix SU7MotherIndex SU7MotherIndex ℂ) * first)) * star g =
      ((g * first * star g) * (g * second * star g)) -
        ((g * second * star g) * (g * first * star g))
  calc
    g * (((first : Matrix SU7MotherIndex SU7MotherIndex ℂ) * second) -
          ((second : Matrix SU7MotherIndex SU7MotherIndex ℂ) * first)) * star g =
        g * first * second * star g -
          g * second * first * star g := by noncomm_ring
    _ = g * first * (star g * g) * second * star g -
          g * second * (star g * g) * first * star g := by
      rw [hunitary]
      simp
    _ = ((g * first * star g) * (g * second * star g)) -
          ((g * second * star g) * (g * first * star g)) := by
      noncomm_ring

/-- Constant/global SU(7) conjugation of the mother connection.  A local
gauge transform also needs the inhomogeneous derivative-of-gauge term and is
deliberately not claimed here. -/
def constantGaugeTransformMotherConnection
    (groupElement : SU7MotherGroup)
    (connection : SU7MotherGaugeConnection) : SU7MotherGaugeConnection where
  potential := fun direction =>
    motherGaugeConjugate groupElement (connection.potential direction)
  exteriorDerivative := fun pair =>
    motherGaugeConjugate groupElement (connection.exteriorDerivative pair)

theorem motherCurvature_constantGaugeTransform
    (groupElement : SU7MotherGroup)
    (connection : SU7MotherGaugeConnection) (pair : Fin 6) :
    motherCurvature
        (constantGaugeTransformMotherConnection groupElement connection) pair =
      motherGaugeConjugate groupElement (motherCurvature connection pair) := by
  rw [motherCurvature, motherCurvature,
    motherGaugeConjugate_add, motherGaugeConjugate_bracket]
  rfl

/-- First finite transport jet `1 + A`.  On higher exterior powers its
functorial lift retains finite higher-order terms, so it is not identified
with the infinitesimal derived Lie-algebra representation. -/
def fundamentalMotherTransportMatrix (matrix : SU7MotherLieMatrix) :
    Matrix SU7MotherIndex SU7MotherIndex ℂ :=
  1 + (matrix : Matrix SU7MotherIndex SU7MotherIndex ℂ)

def fundamentalMotherTransport (matrix : SU7MotherLieMatrix) :
    Module.End ℂ SU7FundamentalCarrier :=
  Matrix.mulVecLin (fundamentalMotherTransportMatrix matrix)

@[simp]
theorem fundamentalMotherTransport_zero :
    fundamentalMotherTransport (0 : SU7MotherLieMatrix) = LinearMap.id := by
  apply LinearMap.ext
  intro vector
  simp [fundamentalMotherTransport, fundamentalMotherTransportMatrix]

theorem fundamentalMotherTransportMatrix_conjugation
    (groupElement : SU7MotherGroup) (matrix : SU7MotherLieMatrix) :
    fundamentalMotherTransportMatrix
          (motherGaugeConjugate groupElement matrix) *
        (groupElement : Matrix SU7MotherIndex SU7MotherIndex ℂ) =
      (groupElement : Matrix SU7MotherIndex SU7MotherIndex ℂ) *
        fundamentalMotherTransportMatrix matrix := by
  let g : Matrix SU7MotherIndex SU7MotherIndex ℂ := groupElement
  have hunitary : star g * g = 1 :=
    Matrix.mem_unitaryGroup_iff'.mp
      (Matrix.specialUnitaryGroup_le_unitaryGroup groupElement.property)
  change (1 + g * matrix * star g) * g = g * (1 + matrix)
  calc
    (1 + g * (matrix : Matrix SU7MotherIndex SU7MotherIndex ℂ) * star g) * g =
        g + g * matrix * (star g * g) := by noncomm_ring
    _ = g + g * matrix := by rw [hunitary, Matrix.mul_one]
    _ = g * (1 + matrix) := by rw [Matrix.mul_add, Matrix.mul_one]

theorem fundamentalMotherTransport_covariant
    (groupElement : SU7MotherGroup) (matrix : SU7MotherLieMatrix) :
    (fundamentalMotherTransport (motherGaugeConjugate groupElement matrix)).comp
        (su7FundamentalRepresentation groupElement) =
      (su7FundamentalRepresentation groupElement).comp
        (fundamentalMotherTransport matrix) := by
  apply LinearMap.ext
  intro vector
  change
    fundamentalMotherTransportMatrix (motherGaugeConjugate groupElement matrix) *ᵥ
        ((groupElement : Matrix SU7MotherIndex SU7MotherIndex ℂ) *ᵥ vector) =
      (groupElement : Matrix SU7MotherIndex SU7MotherIndex ℂ) *ᵥ
        (fundamentalMotherTransportMatrix matrix *ᵥ vector)
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
    fundamentalMotherTransportMatrix_conjugation]

/-! The finite transport is not merely a formal action: the actual P286
hypercharge Lie direction acts nontrivially on the same exterior basis used
by the Stage-7 restriction proof. -/

def fundamentalMotherTransportEigenvalue (index : SU7MotherIndex) : ℂ :=
  1 + Complex.I * (fundamentalHyperchargeWeight index : ℂ)

theorem fundamentalMotherTransport_p286Hypercharge_basis
    (index : SU7MotherIndex) :
    fundamentalMotherTransport p286HyperchargeLieGenerator
        (su7FundamentalBasis index) =
      fundamentalMotherTransportEigenvalue index •
        su7FundamentalBasis index := by
  funext row
  fin_cases index <;> fin_cases row <;>
    simp [fundamentalMotherTransport, fundamentalMotherTransportMatrix,
      fundamentalMotherTransportEigenvalue, p286HyperchargeLieGenerator,
      p286LieBlockEmbed, rawP286LieBlock, weakHyperchargeLieBlock,
      hyperchargeLieBlock, scalarLieBlock, hyperchargeGenerator,
      su7FundamentalBasis, fundamentalHyperchargeWeight]

def exteriorMotherTransport (degree : ℕ) (matrix : SU7MotherLieMatrix) :
    Module.End ℂ (⋀[ℂ]^degree SU7FundamentalCarrier) :=
  exteriorPower.map degree (fundamentalMotherTransport matrix)

@[simp]
theorem exteriorMotherTransport_zero (degree : ℕ) :
    exteriorMotherTransport degree (0 : SU7MotherLieMatrix) = LinearMap.id := by
  rw [exteriorMotherTransport, fundamentalMotherTransport_zero,
    exteriorPower.map_id]

theorem exteriorMotherTransport_covariant
    (degree : ℕ) (groupElement : SU7MotherGroup)
    (matrix : SU7MotherLieMatrix) :
    (exteriorMotherTransport degree
        (motherGaugeConjugate groupElement matrix)).comp
          (su7ExteriorPowerRepresentation degree groupElement) =
      (su7ExteriorPowerRepresentation degree groupElement).comp
        (exteriorMotherTransport degree matrix) := by
  change
    (exteriorPower.map degree
        (fundamentalMotherTransport (motherGaugeConjugate groupElement matrix))).comp
          (exteriorPower.map degree
            (su7FundamentalRepresentation groupElement)) =
      (exteriorPower.map degree
          (su7FundamentalRepresentation groupElement)).comp
        (exteriorPower.map degree (fundamentalMotherTransport matrix))
  rw [← exteriorPower.map_comp, ← exteriorPower.map_comp,
    fundamentalMotherTransport_covariant]

def exteriorMotherTransportEigenvalue {degree : ℕ}
    (index : ExteriorBasisIndex degree) : ℂ :=
  ∏ position : Fin degree,
    fundamentalMotherTransportEigenvalue
      (Set.powersetCard.ofFinEmbEquiv.symm index position)

theorem exteriorMotherTransport_p286Hypercharge_basis
    (degree : ℕ) (index : ExteriorBasisIndex degree) :
    exteriorMotherTransport degree p286HyperchargeLieGenerator
        (su7ExteriorBasis degree index) =
      exteriorMotherTransportEigenvalue index •
        su7ExteriorBasis degree index := by
  change
    exteriorPower.map degree
        (fundamentalMotherTransport p286HyperchargeLieGenerator)
        (su7ExteriorBasis degree index) = _
  rw [su7ExteriorBasis, exteriorPower.basis_apply,
    exteriorPower.map_apply_ιMulti_family]
  change
    exteriorPower.ιMulti ℂ degree
        (fun position =>
          fundamentalMotherTransport p286HyperchargeLieGenerator
            (su7FundamentalBasis
              (Set.powersetCard.ofFinEmbEquiv.symm index position))) = _
  have hpointwise :
      (fun position =>
          fundamentalMotherTransport p286HyperchargeLieGenerator
            (su7FundamentalBasis
              (Set.powersetCard.ofFinEmbEquiv.symm index position))) =
        (fun position =>
          fundamentalMotherTransportEigenvalue
              (Set.powersetCard.ofFinEmbEquiv.symm index position) •
            su7FundamentalBasis
              (Set.powersetCard.ofFinEmbEquiv.symm index position)) := by
    funext position
    exact fundamentalMotherTransport_p286Hypercharge_basis _
  rw [hpointwise, (exteriorPower.ιMulti ℂ degree).map_smul_univ]
  rfl

theorem exteriorPosition_prod_eq_subset_prod_complex {degree : ℕ}
    (index : ExteriorBasisIndex degree) (value : SU7MotherIndex → ℂ) :
    (∏ position : Fin degree,
        value (Set.powersetCard.ofFinEmbEquiv.symm index position)) =
      ∏ basisIndex ∈ index.1, value basisIndex := by
  calc
    _ = ∏ basisIndex : {basisIndex // basisIndex ∈ index.1},
          value basisIndex :=
      (exteriorPositionEquiv index).prod_comp
        (fun basisIndex => value basisIndex)
    _ = _ := (Finset.prod_subtype index.1 (by simp) value).symm

def hyperchargeDegreeTwoSubset : Finset SU7MotherIndex :=
  {(Sum.inl 0 : SU7MotherIndex), hyperPlusIndex}

def hyperchargeDegreeTwoIndex : ExteriorBasisIndex 2 :=
  ⟨hyperchargeDegreeTwoSubset, by
    change hyperchargeDegreeTwoSubset.card = 2
    simp [hyperchargeDegreeTwoSubset, hyperPlusIndex]⟩

theorem exteriorMotherTransportEigenvalue_hyperchargeDegreeTwoIndex :
    exteriorMotherTransportEigenvalue hyperchargeDegreeTwoIndex =
      1 + Complex.I := by
  rw [exteriorMotherTransportEigenvalue,
    exteriorPosition_prod_eq_subset_prod_complex]
  norm_num [hyperchargeDegreeTwoIndex, hyperchargeDegreeTwoSubset,
    fundamentalMotherTransportEigenvalue, fundamentalHyperchargeWeight,
    hyperPlusIndex]

theorem exteriorMotherTransport_p286Hypercharge_degreeTwo :
    exteriorMotherTransport 2 p286HyperchargeLieGenerator
        (su7ExteriorBasis 2 hyperchargeDegreeTwoIndex) =
      (1 + Complex.I) •
        su7ExteriorBasis 2 hyperchargeDegreeTwoIndex := by
  rw [exteriorMotherTransport_p286Hypercharge_basis,
    exteriorMotherTransportEigenvalue_hyperchargeDegreeTwoIndex]

theorem exteriorMotherIncrement_p286Hypercharge_degreeTwo_ne_zero :
    ((exteriorMotherTransport 2 p286HyperchargeLieGenerator -
        (LinearMap.id :
          Module.End ℂ (⋀[ℂ]^2 SU7FundamentalCarrier)))
        (su7ExteriorBasis 2 hyperchargeDegreeTwoIndex)) ≠ 0 := by
  rw [LinearMap.sub_apply,
    exteriorMotherTransport_p286Hypercharge_degreeTwo,
    LinearMap.id_apply]
  have hbasis :
      su7ExteriorBasis 2 hyperchargeDegreeTwoIndex ≠ 0 :=
    (su7ExteriorBasis 2).ne_zero hyperchargeDegreeTwoIndex
  have hi : (Complex.I : ℂ) ≠ 0 := by norm_num
  simpa [add_smul] using smul_ne_zero hi hbasis

def exteriorSpinorMotherTransport (matrix : SU7MotherLieMatrix) :
    Module.End ℂ SU7ExteriorSpinorMatterCarrier :=
  (exteriorMotherTransport 6 matrix).prodMap
    ((exteriorMotherTransport 2 matrix).prodMap
      (exteriorMotherTransport 4 matrix))

@[simp]
theorem exteriorSpinorMotherTransport_zero :
    exteriorSpinorMotherTransport (0 : SU7MotherLieMatrix) = LinearMap.id := by
  apply LinearMap.ext
  rintro ⟨degreeSix, degreeTwo, degreeFour⟩
  simp [exteriorSpinorMotherTransport]

theorem exteriorSpinorMotherTransport_covariant
    (groupElement : SU7MotherGroup) (matrix : SU7MotherLieMatrix) :
    (exteriorSpinorMotherTransport
        (motherGaugeConjugate groupElement matrix)).comp
          (su7ExteriorSpinorMatterRepresentation groupElement) =
      (su7ExteriorSpinorMatterRepresentation groupElement).comp
        (exteriorSpinorMotherTransport matrix) := by
  apply LinearMap.ext
  rintro ⟨degreeSix, degreeTwo, degreeFour⟩
  apply Prod.ext
  · simpa [exteriorSpinorMotherTransport,
      su7ExteriorSpinorMatterRepresentation] using
      LinearMap.congr_fun
        (exteriorMotherTransport_covariant 6 groupElement matrix) degreeSix
  · apply Prod.ext
    · simpa [exteriorSpinorMotherTransport,
        su7ExteriorSpinorMatterRepresentation] using
        LinearMap.congr_fun
          (exteriorMotherTransport_covariant 2 groupElement matrix) degreeTwo
    · simpa [exteriorSpinorMotherTransport,
        su7ExteriorSpinorMatterRepresentation] using
        LinearMap.congr_fun
          (exteriorMotherTransport_covariant 4 groupElement matrix) degreeFour

def exteriorSpinorMotherIncrement (matrix : SU7MotherLieMatrix) :
    Module.End ℂ SU7ExteriorSpinorMatterCarrier :=
  exteriorSpinorMotherTransport matrix - LinearMap.id

@[simp]
theorem exteriorSpinorMotherIncrement_zero :
    exteriorSpinorMotherIncrement (0 : SU7MotherLieMatrix) = 0 := by
  rw [exteriorSpinorMotherIncrement, exteriorSpinorMotherTransport_zero]
  exact sub_self
    (LinearMap.id : Module.End ℂ SU7ExteriorSpinorMatterCarrier)

theorem exteriorSpinorMotherIncrement_covariant
    (groupElement : SU7MotherGroup) (matrix : SU7MotherLieMatrix) :
    (exteriorSpinorMotherIncrement
        (motherGaugeConjugate groupElement matrix)).comp
          (su7ExteriorSpinorMatterRepresentation groupElement) =
      (su7ExteriorSpinorMatterRepresentation groupElement).comp
        (exteriorSpinorMotherIncrement matrix) := by
  apply LinearMap.ext
  intro matter
  have htransport := LinearMap.congr_fun
    (exteriorSpinorMotherTransport_covariant groupElement matrix) matter
  simpa [exteriorSpinorMotherIncrement] using htransport

def p286HyperchargeMatterProbe : SU7ExteriorSpinorMatterCarrier :=
  (0, (su7ExteriorBasis 2 hyperchargeDegreeTwoIndex, 0))

/-- Positive regression: the same actual mother Lie direction and the same
Stage-7 matter carrier have a nonzero coupling. -/
theorem exteriorSpinorMotherIncrement_p286Hypercharge_probe_ne_zero :
    exteriorSpinorMotherIncrement p286HyperchargeLieGenerator
        p286HyperchargeMatterProbe ≠ 0 := by
  intro hzero
  have hdegreeTwo := congrArg
    (fun matter : SU7ExteriorSpinorMatterCarrier => matter.2.1) hzero
  apply exteriorMotherIncrement_p286Hypercharge_degreeTwo_ne_zero
  simpa [exteriorSpinorMotherIncrement, exteriorSpinorMotherTransport,
    p286HyperchargeMatterProbe] using hdegreeTwo

structure ExteriorMatterFirstJet where
  field : SU7ExteriorSpinorMatterCarrier
  derivative : LorentzianIndex → SU7ExteriorSpinorMatterCarrier
  conjugateField : Module.Dual ℂ SU7ExteriorSpinorMatterCarrier

def constantGaugeTransformMatterJet
    (groupElement : SU7MotherGroup) (jet : ExteriorMatterFirstJet) :
    ExteriorMatterFirstJet where
  field := su7ExteriorSpinorMatterRepresentation groupElement jet.field
  derivative := fun direction =>
    su7ExteriorSpinorMatterRepresentation groupElement (jet.derivative direction)
  conjugateField := jet.conjugateField.comp
    (su7ExteriorSpinorMatterRepresentation groupElement⁻¹)

def exteriorMatterCovariantDerivative
    (connection : SU7MotherGaugeConnection) (jet : ExteriorMatterFirstJet)
    (direction : LorentzianIndex) : SU7ExteriorSpinorMatterCarrier :=
  jet.derivative direction +
    exteriorSpinorMotherIncrement (connection.potential direction) jet.field

theorem exteriorMatterCovariantDerivative_of_zero_potential
    (connection : SU7MotherGaugeConnection) (jet : ExteriorMatterFirstJet)
    (potential_zero : ∀ direction, connection.potential direction = 0)
    (direction : LorentzianIndex) :
    exteriorMatterCovariantDerivative connection jet direction =
      jet.derivative direction := by
  simp [exteriorMatterCovariantDerivative, potential_zero]

theorem exteriorMatterCovariantDerivative_constantGauge_covariant
    (groupElement : SU7MotherGroup)
    (connection : SU7MotherGaugeConnection) (jet : ExteriorMatterFirstJet)
    (direction : LorentzianIndex) :
    exteriorMatterCovariantDerivative
        (constantGaugeTransformMotherConnection groupElement connection)
        (constantGaugeTransformMatterJet groupElement jet) direction =
      su7ExteriorSpinorMatterRepresentation groupElement
        (exteriorMatterCovariantDerivative connection jet direction) := by
  have hincrement := LinearMap.congr_fun
    (exteriorSpinorMotherIncrement_covariant groupElement
      (connection.potential direction)) jet.field
  simpa [exteriorMatterCovariantDerivative,
    constantGaugeTransformMotherConnection,
    constantGaugeTransformMatterJet, map_add] using hincrement

def exteriorMatterKineticOneForm
    (connection : SU7MotherGaugeConnection) (jet : ExteriorMatterFirstJet) :
    LorentzianIndex → ℂ :=
  fun direction =>
    jet.conjugateField
      (exteriorMatterCovariantDerivative connection jet direction)

theorem exteriorMatterKineticOneForm_constantGauge_invariant
    (groupElement : SU7MotherGroup)
    (connection : SU7MotherGaugeConnection) (jet : ExteriorMatterFirstJet) :
    exteriorMatterKineticOneForm
        (constantGaugeTransformMotherConnection groupElement connection)
        (constantGaugeTransformMatterJet groupElement jet) =
      exteriorMatterKineticOneForm connection jet := by
  funext direction
  rw [exteriorMatterKineticOneForm,
    exteriorMatterCovariantDerivative_constantGauge_covariant]
  simp [constantGaugeTransformMatterJet]
  rfl

/-! ## Finite direction-reindex covariance

This is honest covariance of the first-jet direction carrier.  It is not yet
the missing local `Spin(1,3)` action on Weyl/Dirac indices. -/

def reindexMotherPotentialJet
    (frame : Equiv.Perm LorentzianIndex)
    (connection : SU7MotherGaugeConnection) : SU7MotherGaugeConnection where
  potential := fun direction => connection.potential (frame.symm direction)
  exteriorDerivative := connection.exteriorDerivative

def reindexMatterJetDirections
    (frame : Equiv.Perm LorentzianIndex) (jet : ExteriorMatterFirstJet) :
    ExteriorMatterFirstJet where
  field := jet.field
  derivative := fun direction => jet.derivative (frame.symm direction)
  conjugateField := jet.conjugateField

theorem exteriorMatterCovariantDerivative_reindex
    (frame : Equiv.Perm LorentzianIndex)
    (connection : SU7MotherGaugeConnection) (jet : ExteriorMatterFirstJet)
    (direction : LorentzianIndex) :
    exteriorMatterCovariantDerivative
        (reindexMotherPotentialJet frame connection)
        (reindexMatterJetDirections frame jet) direction =
      exteriorMatterCovariantDerivative connection jet
        (frame.symm direction) := by
  rfl

theorem exteriorMatterKineticOneForm_reindex
    (frame : Equiv.Perm LorentzianIndex)
    (connection : SU7MotherGaugeConnection) (jet : ExteriorMatterFirstJet) :
    exteriorMatterKineticOneForm
        (reindexMotherPotentialJet frame connection)
        (reindexMatterJetDirections frame jet) =
      exteriorMatterKineticOneForm connection jet ∘ frame.symm := by
  rfl

end
end SaturationMonoid.PhysicsCore.SU7ExteriorMatterGaugeCovariantJet
