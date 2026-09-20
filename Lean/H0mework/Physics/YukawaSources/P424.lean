import H0mework.Realization.Relations.FintypeDerivation
import H0mework.Realization.Descent.P423

/-!
# Proposition 424: matrix normal form for the nine Yukawa rows

P415 opens the remaining alpha/RG producer into nine named Yukawa rows.
P416/P417 connect those rows to the three Standard-Model generations and the
three 4D Poincare slots.

This file tightens the finite surface once more: the nine rows are not merely
nine names.  They are the product of

* three Standard-Model generations;
* three interaction sectors: up-like, down-like, charged lepton.

The product matrix is equivalent to `YukawaParameter`, each generation/slot has
exactly three rows, and P415's named nine-row producer is equivalent to a
matrix-indexed producer.  P423's strict physical front door can therefore be
read as:

`matrix nine-row sigma table + independent physical geometry producer`.

Boundary: this is still finite Standard-Model bookkeeping.  It does not derive
beta functions, threshold matching, or the physical values of the table rows.
-/

namespace SaturationMonoid
namespace StandardModelConstraint

open AffineRelaxation.GeometryConnection

/-! ## Three-by-three Yukawa matrix carrier -/

/-- The three Yukawa interaction sectors in each Standard-Model generation. -/
inductive YukawaInteractionSector where
  | upLike
  | downLike
  | chargedLepton
  deriving DecidableEq, Repr, FintypeViaProxy

namespace YukawaInteractionSector

/-- THEOREM 1: there are three interaction sectors. -/
theorem card : Fintype.card YukawaInteractionSector = 3 := by
  decide

end YukawaInteractionSector

/-- The canonical `generation × sector` matrix of the nine Yukawa parameters. -/
def yukawaMatrixParameter :
    StandardModelFermionGeneration -> YukawaInteractionSector -> YukawaParameter
  | .first, .upLike => .up
  | .first, .downLike => .down
  | .first, .chargedLepton => .electron
  | .second, .upLike => .charm
  | .second, .downLike => .strange
  | .second, .chargedLepton => .muon
  | .third, .upLike => .top
  | .third, .downLike => .bottom
  | .third, .chargedLepton => .tau

/-- The inverse matrix coordinates of a named Yukawa parameter. -/
def yukawaMatrixCoordinates :
    YukawaParameter -> StandardModelFermionGeneration × YukawaInteractionSector
  | .up => (.first, .upLike)
  | .down => (.first, .downLike)
  | .electron => (.first, .chargedLepton)
  | .charm => (.second, .upLike)
  | .strange => (.second, .downLike)
  | .muon => (.second, .chargedLepton)
  | .top => (.third, .upLike)
  | .bottom => (.third, .downLike)
  | .tau => (.third, .chargedLepton)

/-- THEOREM 2: the nine Yukawa parameters are exactly a `3 × 3` matrix. -/
def yukawaMatrixEquiv :
    StandardModelFermionGeneration × YukawaInteractionSector ≃ YukawaParameter where
  toFun p := yukawaMatrixParameter p.1 p.2
  invFun := yukawaMatrixCoordinates
  left_inv := by
    intro p
    rcases p with ⟨g, s⟩
    cases g <;> cases s <;> rfl
  right_inv := by
    intro y
    cases y <;> rfl

instance : Fintype YukawaParameter :=
  Fintype.ofEquiv (StandardModelFermionGeneration × YukawaInteractionSector)
    yukawaMatrixEquiv

/-- THEOREM 3: the Yukawa parameter carrier has exactly nine rows. -/
theorem yukawaParameter_card : Fintype.card YukawaParameter = 9 := by
  decide

/-- THEOREM 4: matrix coordinates recover the existing generation projection. -/
theorem yukawaMatrix_generation_eq
    (g : StandardModelFermionGeneration) (s : YukawaInteractionSector) :
    yukawaFermionGeneration (yukawaMatrixParameter g s) = g := by
  cases g <;> cases s <;> rfl

/-- THEOREM 5: matrix rows land in the Poincare slot of their generation. -/
theorem yukawaMatrix_poincareSlot_eq
    (g : StandardModelFermionGeneration) (s : YukawaInteractionSector) :
    yukawaPoincareSlot (yukawaMatrixParameter g s) =
      standardModelGenerationPoincareSlot g := by
  cases g <;> cases s <;> rfl

/-- THEOREM 6: the matrix presentation covers every named Yukawa row. -/
theorem yukawaMatrix_surjective :
    Function.Surjective
      (fun p : StandardModelFermionGeneration × YukawaInteractionSector =>
        yukawaMatrixParameter p.1 p.2) := by
  intro y
  cases y
  · exact ⟨(.first, .upLike), rfl⟩
  · exact ⟨(.second, .upLike), rfl⟩
  · exact ⟨(.third, .upLike), rfl⟩
  · exact ⟨(.first, .downLike), rfl⟩
  · exact ⟨(.second, .downLike), rfl⟩
  · exact ⟨(.third, .downLike), rfl⟩
  · exact ⟨(.first, .chargedLepton), rfl⟩
  · exact ⟨(.second, .chargedLepton), rfl⟩
  · exact ⟨(.third, .chargedLepton), rfl⟩

/-- THEOREM 7: the matrix presentation has no duplicate rows. -/
theorem yukawaMatrix_injective :
    Function.Injective
      (fun p : StandardModelFermionGeneration × YukawaInteractionSector =>
        yukawaMatrixParameter p.1 p.2) := by
  intro p q h
  rcases p with ⟨g, s⟩
  rcases q with ⟨g', s'⟩
  cases g <;> cases s <;> cases g' <;> cases s' <;>
    simp [yukawaMatrixParameter] at h ⊢

/-- THEOREM 8: each Standard-Model generation contains exactly three Yukawa
rows. -/
theorem yukawa_generation_fiber_card
    (g : StandardModelFermionGeneration) :
    Fintype.card { y : YukawaParameter // yukawaFermionGeneration y = g } =
      3 := by
  cases g <;> decide

/-- THEOREM 9: each Poincare generation slot contains exactly three Yukawa
rows. -/
theorem yukawa_poincareSlot_fiber_card
    (s : FourDimensionalPoincareSlot) :
    Fintype.card { y : YukawaParameter // yukawaPoincareSlot y = s } = 3 := by
  cases s <;> decide

/-- The interaction sector coordinate of a named Yukawa parameter. -/
def yukawaInteractionSectorOf (y : YukawaParameter) : YukawaInteractionSector :=
  (yukawaMatrixCoordinates y).2

/-- THEOREM 10: each interaction sector occurs once in each generation, hence
three times in the nine-row table. -/
theorem yukawa_interactionSector_fiber_card
    (s : YukawaInteractionSector) :
    Fintype.card { y : YukawaParameter // yukawaInteractionSectorOf y = s } =
      3 := by
  cases s <;> decide

/-! ## Matrix-indexed primitive sigma RG path table -/

/-- P415's primitive atom-native sigma table indexed by the `3 × 3` Yukawa
matrix instead of nine ad-hoc field names. -/
structure MatrixPrimitiveAtomNativeSigmaYukawaRGPathTableProducer
    {Index A CKMCarrier : Type*} [AddCommGroup A]
    (atoms : GrandUnificationPrimitiveProducerAtoms Index A CKMCarrier) where
  step : StandardModelScaleCode -> StandardModelScaleCode -> Prop
  reach_not_sigma_order :
    RGStepReach step ≠
      fun a b : StandardModelScaleCode => atoms.sigma a ≤ atoms.sigma b
  fourPi_eq_realFourPi : atoms.fourPi = realFourPi
  matrix_reaches_weak :
    ∀ g s,
      RGStepReach step
        (StandardModelScaleCode.yukawa (yukawaMatrixParameter g s))
        StandardModelScaleCode.weak
  step_sigma_monotone :
    ∀ {a b : StandardModelScaleCode}, step a b ->
      atoms.sigma a ≤ atoms.sigma b

namespace MatrixPrimitiveAtomNativeSigmaYukawaRGPathTableProducer

variable {Index A CKMCarrier : Type*} [AddCommGroup A]
variable {atoms : GrandUnificationPrimitiveProducerAtoms Index A CKMCarrier}

/-- THEOREM 11: the matrix table fills P414/P415's all-Yukawa reachability
field. -/
theorem selected_yukawa_reaches_weak
    (C : MatrixPrimitiveAtomNativeSigmaYukawaRGPathTableProducer atoms) :
    ∀ y : YukawaParameter,
      RGStepReach C.step (StandardModelScaleCode.yukawa y)
        StandardModelScaleCode.weak := by
  intro y
  cases y
  · exact C.matrix_reaches_weak .first .upLike
  · exact C.matrix_reaches_weak .second .upLike
  · exact C.matrix_reaches_weak .third .upLike
  · exact C.matrix_reaches_weak .first .downLike
  · exact C.matrix_reaches_weak .second .downLike
  · exact C.matrix_reaches_weak .third .downLike
  · exact C.matrix_reaches_weak .first .chargedLepton
  · exact C.matrix_reaches_weak .second .chargedLepton
  · exact C.matrix_reaches_weak .third .chargedLepton

/-- THEOREM 12: a matrix table forgets to P415's named nine-row table. -/
def toPrimitiveAtomNativeSigmaYukawaRGPathTableProducer
    (C : MatrixPrimitiveAtomNativeSigmaYukawaRGPathTableProducer atoms) :
    PrimitiveAtomNativeSigmaYukawaRGPathTableProducer atoms where
  step := C.step
  reach_not_sigma_order := C.reach_not_sigma_order
  fourPi_eq_realFourPi := C.fourPi_eq_realFourPi
  up_reaches_weak := C.matrix_reaches_weak .first .upLike
  charm_reaches_weak := C.matrix_reaches_weak .second .upLike
  top_reaches_weak := C.matrix_reaches_weak .third .upLike
  down_reaches_weak := C.matrix_reaches_weak .first .downLike
  strange_reaches_weak := C.matrix_reaches_weak .second .downLike
  bottom_reaches_weak := C.matrix_reaches_weak .third .downLike
  electron_reaches_weak := C.matrix_reaches_weak .first .chargedLepton
  muon_reaches_weak := C.matrix_reaches_weak .second .chargedLepton
  tau_reaches_weak := C.matrix_reaches_weak .third .chargedLepton
  step_sigma_monotone := C.step_sigma_monotone

end MatrixPrimitiveAtomNativeSigmaYukawaRGPathTableProducer

namespace PrimitiveAtomNativeSigmaYukawaRGPathTableProducer

variable {Index A CKMCarrier : Type*} [AddCommGroup A]
variable {atoms : GrandUnificationPrimitiveProducerAtoms Index A CKMCarrier}

/-- THEOREM 13: P415's named nine-row table opens to the matrix-indexed table. -/
def toMatrixPrimitiveAtomNativeSigmaYukawaRGPathTableProducer
    (C : PrimitiveAtomNativeSigmaYukawaRGPathTableProducer atoms) :
    MatrixPrimitiveAtomNativeSigmaYukawaRGPathTableProducer atoms where
  step := C.step
  reach_not_sigma_order := C.reach_not_sigma_order
  fourPi_eq_realFourPi := C.fourPi_eq_realFourPi
  matrix_reaches_weak := by
    intro g s
    exact C.selected_yukawa_reaches_weak (yukawaMatrixParameter g s)
  step_sigma_monotone := C.step_sigma_monotone

end PrimitiveAtomNativeSigmaYukawaRGPathTableProducer

/-! ## Existence-level matrix normal form -/

/-- A primitive atom object equipped with a matrix-indexed nine-row native sigma
RG table. -/
def ExistsMatrixPrimitiveAtomNativeSigmaYukawaRGPathTableProducer
    (Index A CKMCarrier : Type*) [AddCommGroup A] : Prop :=
  ∃ atoms : GrandUnificationPrimitiveProducerAtoms Index A CKMCarrier,
    Nonempty (MatrixPrimitiveAtomNativeSigmaYukawaRGPathTableProducer atoms)

/-- THEOREM 14: matrix tables supply P415's named nine-row table surface. -/
theorem existsPrimitiveTable_of_matrixPrimitiveTable
    {Index A CKMCarrier : Type*} [AddCommGroup A] :
    ExistsMatrixPrimitiveAtomNativeSigmaYukawaRGPathTableProducer
        Index A CKMCarrier ->
      ExistsPrimitiveAtomNativeSigmaYukawaRGPathTableProducer
        Index A CKMCarrier := by
  rintro ⟨atoms, ⟨C⟩⟩
  exact
    ⟨atoms, ⟨C.toPrimitiveAtomNativeSigmaYukawaRGPathTableProducer⟩⟩

/-- THEOREM 15: P415's named nine-row table surface supplies the matrix table. -/
theorem existsMatrixPrimitiveTable_of_primitiveTable
    {Index A CKMCarrier : Type*} [AddCommGroup A] :
    ExistsPrimitiveAtomNativeSigmaYukawaRGPathTableProducer
        Index A CKMCarrier ->
      ExistsMatrixPrimitiveAtomNativeSigmaYukawaRGPathTableProducer
        Index A CKMCarrier := by
  rintro ⟨atoms, ⟨C⟩⟩
  exact
    ⟨atoms, ⟨C.toMatrixPrimitiveAtomNativeSigmaYukawaRGPathTableProducer⟩⟩

/-- THEOREM 16: exact matrix normal form for the atom-native nine-row table. -/
theorem primitiveTable_nonempty_iff_matrixPrimitiveTable
    {Index A CKMCarrier : Type*} [AddCommGroup A] :
    ExistsPrimitiveAtomNativeSigmaYukawaRGPathTableProducer
        Index A CKMCarrier ↔
      ExistsMatrixPrimitiveAtomNativeSigmaYukawaRGPathTableProducer
        Index A CKMCarrier := by
  constructor
  · exact existsMatrixPrimitiveTable_of_primitiveTable
  · exact existsPrimitiveTable_of_matrixPrimitiveTable

/-- THEOREM 17: P423's strict physical front door can be read in matrix
coordinates. -/
theorem strictPhysicalNineRowPoincare_nonempty_iff_matrixTable_and_physical
    {Index A CKMCarrier PhysicalGeometry : Type*} [AddCommGroup A]
    (adapter : PhysicalPoincareGeometryAdapter PhysicalGeometry) :
    ExistsStrictPhysicalNineRowPoincareProducer
        Index A CKMCarrier PhysicalGeometry adapter ↔
      ExistsMatrixPrimitiveAtomNativeSigmaYukawaRGPathTableProducer
        Index A CKMCarrier ∧
        Nonempty PhysicalGeometry := by
  rw [strictPhysicalNineRowPoincare_nonempty_iff_nineRow_and_physical adapter,
    primitiveTable_nonempty_iff_matrixPrimitiveTable]

/-- THEOREM 18: a strict physical matrix front door supplies the full current
concrete holy-grail output package. -/
theorem strictPhysicalMatrixNineRow_concrete_holy_grail_output
    {Index A CKMCarrier PhysicalGeometry : Type*} [AddCommGroup A]
    (adapter : PhysicalPoincareGeometryAdapter PhysicalGeometry) :
    ExistsMatrixPrimitiveAtomNativeSigmaYukawaRGPathTableProducer
        Index A CKMCarrier ∧
        Nonempty PhysicalGeometry ->
      ∃ O : StandardModelPoincareHolyGrailOutput Index A CKMCarrier,
        SingleSourceHolyGrailReceiptStatement O.receipt ∧
          Nonempty
            (StandardModelFermionGeneration ≃ FourDimensionalPoincareSlot) ∧
          Function.Surjective yukawaPoincareSlot ∧
          IsEmpty (Fin 4 ↪ StandardModelFermionGeneration) := by
  intro h
  exact
    strictPhysicalNineRowPoincare_concrete_holy_grail_output adapter
      ((strictPhysicalNineRowPoincare_nonempty_iff_matrixTable_and_physical
        adapter).mpr h)

end StandardModelConstraint
end SaturationMonoid
