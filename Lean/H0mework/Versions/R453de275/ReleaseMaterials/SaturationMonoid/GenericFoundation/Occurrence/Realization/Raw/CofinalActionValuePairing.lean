import H0mework.Versions.R453de275.ReleaseMaterials.SaturationMonoid.GenericFoundation.Occurrence.Realization.Raw.CofinalActionCochain

/-!
# Full value pairing from the actual receipt evaluator

For a commutative-ring-valued source evaluator, multiplication of the two
complete evaluated words gives a source-owned integer-bilinear pairing with
the original value unit. This is not a quotient pairing or Hilbert Gram. It
is installed beside the existing raw, residual and relation-differential
faces at the exact original event, retaining its whole row and next.
-/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace RawGeneratedRoot.CofinalAction

open CofinalFaithfulRealization
open CofinalFaithfulRealization.RootGeneratedCofinalFaithfulRealizationAt

noncomputable section

variable {D : Dynamics.{0}} {Carrier : Type} [CommRing Carrier]

def valuePairing (law : Law D Carrier)
    {state : D.State}
    (occurrence : (source D).toRootSource.actual.OccurrenceAt state) :
    (law.Generator →₀ ℤ) →ₗ[ℤ] (law.Generator →₀ ℤ) →ₗ[ℤ] Carrier :=
  let read : (law.Generator →₀ ℤ) →ₗ[ℤ] Carrier :=
    ((faithfulLaw law).faithfulAt occurrence).freeEvaluation
  LinearMap.mk₂ ℤ
    (fun left right => read left * read right)
    (by intro left₁ left₂ right; simp [map_add, add_mul])
    (by intro coefficient left right; simp [map_smul]; ring)
    (by intro left right₁ right₂; rw [map_add, mul_add])
    (by intro coefficient left right; simp [map_smul]; ring)

def valuePairingComponent (law : Law D Carrier) :
    SourceNativeProjectionLaw (restructuringSource D).toLedgerSource where
  Projection := PUnit
  ActiveAt := fun _ {_} _ => PUnit
  InactiveAt := fun _ {_} _ => PEmpty
  classify := fun _ {_} _ => .inl PUnit.unit
  PayloadAt := fun _ {_} _ _ =>
    (law.Generator →₀ ℤ) →ₗ[ℤ] (law.Generator →₀ ℤ) →ₗ[ℤ] Carrier
  project := fun _ {_} occurrence _ => valuePairing law occurrence

def valuePairingSource (law : Law D Carrier) :
    SourceNativeAuthoritySource (network D) (vocabulary D) :=
  ((cochainRoot law).source).withProjectionCoface (valuePairingComponent law)

def valuePairingRoot (law : Law D Carrier) :
    SourceNativeAuthoritativeRootClosure (network D) (vocabulary D) where
  source := valuePairingSource law
  emitted := emitted D
  compiler_commutes := (cochainRoot law).compiler_commutes

def oldCochainValueInstallation (law : Law D Carrier) :
    SourceNativeProjectionLaw.InstallationAt
      (cochainRoot law).source.projectionLaw
      (valuePairingRoot law).source.projectionLaw :=
  SourceNativeProjectionLaw.InstallationAt.inheritedCoface
    (cochainRoot law).source (valuePairingComponent law)

theorem valuePairingRoot_same_lower (law : Law D Carrier) :
    (valuePairingRoot law).toLedgerRoot = (root D).toAuthoritativeRoot.toLedgerRoot :=
  rfl

theorem generated_value_pairing_ledger_next (law : Law D Carrier) (state : D.State) :
    (valuePairingRoot law).source.projectionLaw.outcomeAt
        (.component PUnit.unit) ((valuePairingRoot law).emitted state) =
      .inl ⟨PUnit.unit, valuePairing law (emitted D state)⟩ ∧
    (∀ old : (cochainRoot law).source.projectionLaw.Projection,
      HEq ((valuePairingRoot law).source.projectionLaw.outcomeAt
          ((oldCochainValueInstallation law).embed old)
          ((valuePairingRoot law).emitted state))
        ((cochainRoot law).source.projectionLaw.outcomeAt old
          ((cochainRoot law).emitted state))) ∧
    HEq (((valuePairingRoot law).toLedgerRoot.generatedLedgerAt state).entryDisposition
      (entry D state))
      (LedgerEntryDispositionAt.evolved
        (LedgerEntryEvolutionAt.transferred (D.emit state)
          rfl rfl (Nat.le_refl _) :
            LedgerEntryEvolutionAt (network D)
              (entry D state) (entry D (D.update (D.emit state))))) ∧
    ((valuePairingRoot law).toRoot.evolutionAt state).nextCurrent? =
      some (D.update (D.emit state)) := by
  exact ⟨rfl, fun old => (oldCochainValueInstallation law).outcome_heq
    (emitted D state) old, (generated_event_ledger_next law state).2.1,
    (generated_event_ledger_next law state).2.2⟩

theorem generated_value_pairing_basis (law : Law D Carrier) (state : D.State)
    (left right : law.Generator) (leftCoefficient rightCoefficient : ℤ) :
    valuePairing law (emitted D state)
        (Finsupp.single left leftCoefficient)
        (Finsupp.single right rightCoefficient) =
      (leftCoefficient • (law.evaluatorAt (D.emit state)).root left) *
        (rightCoefficient • (law.evaluatorAt (D.emit state)).root right) := by
  have leftEq := (generated_single_equation law state left leftCoefficient).1
  have rightEq := (generated_single_equation law state right rightCoefficient).1
  change ((faithfulLaw law).faithfulAt (emitted D state)).freeEvaluation
      (Finsupp.single left leftCoefficient) *
    ((faithfulLaw law).faithfulAt (emitted D state)).freeEvaluation
      (Finsupp.single right rightCoefficient) = _
  exact congrArg₂ (· * ·) leftEq rightEq

/-- Values invisible to multiplication against this source's complete
evaluator image. The original Carrier unit and occurrence remain unchanged. -/
def valuePairingAnnihilator (law : Law D Carrier) {state : D.State}
    (occurrence : (source D).toRootSource.actual.OccurrenceAt state) :
    Submodule ℤ Carrier where
  carrier := {value | ∀ word : law.Generator →₀ ℤ,
    value * ((faithfulLaw law).faithfulAt occurrence).freeEvaluation word = 0}
  zero_mem' := by intro word; exact zero_mul _
  add_mem' := by
    intro left right leftInvisible rightInvisible word
    rw [add_mul, leftInvisible word, rightInvisible word, zero_add]
  smul_mem' := by
    intro coefficient value invisible word
    rw [zsmul_eq_mul, mul_assoc, invisible word, mul_zero]

/-- The complete inverse fibre of the pairing for every commutative value
ring: exactly the source-value difference annihilating its actual image. -/
theorem valuePairing_fibre_iff_annihilator
    (law : Law D Carrier) {state : D.State}
    (occurrence : (source D).toRootSource.actual.OccurrenceAt state)
    (left right : law.Generator →₀ ℤ) :
    valuePairing law occurrence left = valuePairing law occurrence right ↔
      ((faithfulLaw law).faithfulAt occurrence).freeEvaluation left -
        ((faithfulLaw law).faithfulAt occurrence).freeEvaluation right ∈
          valuePairingAnnihilator law occurrence := by
  let read := ((faithfulLaw law).faithfulAt occurrence).freeEvaluation
  constructor
  · intro same
    change ∀ word : law.Generator →₀ ℤ,
      (read left - read right) * read word = 0
    intro word
    have atWord := LinearMap.congr_fun same word
    change read left * read word = read right * read word at atWord
    rw [sub_mul]
    exact sub_eq_zero.mpr atWord
  · intro invisible
    apply LinearMap.ext
    intro word
    have atWord := invisible word
    change (read left - read right) * read word = 0 at atWord
    rw [sub_mul] at atWord
    change read left * read word = read right * read word
    exact sub_eq_zero.mp atWord

/-- In a reduced value ring, the same word on both legs detects exactly the
source evaluator's zero fibre. This does not choose a square root or recover
the evaluator's full value from its pairing. -/
theorem valuePairing_self_zero_iff [IsReduced Carrier]
    (law : Law D Carrier) {state : D.State}
    (occurrence : (source D).toRootSource.actual.OccurrenceAt state)
    (word : law.Generator →₀ ℤ) :
    valuePairing law occurrence word word = 0 ↔
      ((faithfulLaw law).faithfulAt occurrence).freeEvaluation word = 0 := by
  change ((faithfulLaw law).faithfulAt occurrence).freeEvaluation word *
      ((faithfulLaw law).faithfulAt occurrence).freeEvaluation word = 0 ↔ _
  constructor
  · intro zero
    apply IsReduced.eq_zero
    exact IsNilpotent.mk _ 2 (by simpa only [pow_two] using zero)
  · intro zero
    rw [zero, zero_mul]

theorem valuePairingAnnihilator_source_value_iff_zero [IsReduced Carrier]
    (law : Law D Carrier) {state : D.State}
    (occurrence : (source D).toRootSource.actual.OccurrenceAt state)
    (word : law.Generator →₀ ℤ) :
    ((faithfulLaw law).faithfulAt occurrence).freeEvaluation word ∈
        valuePairingAnnihilator law occurrence ↔
      ((faithfulLaw law).faithfulAt occurrence).freeEvaluation word = 0 := by
  constructor
  · intro invisible
    have square := invisible word
    apply IsReduced.eq_zero
    exact IsNilpotent.mk _ 2 (by simpa only [pow_two] using square)
  · intro zero
    rw [zero]
    exact (valuePairingAnnihilator law occurrence).zero_mem

theorem valuePairing_left_kernel_iff [IsReduced Carrier]
    (law : Law D Carrier) {state : D.State}
    (occurrence : (source D).toRootSource.actual.OccurrenceAt state)
    (word : law.Generator →₀ ℤ) :
    (∀ right : law.Generator →₀ ℤ,
      valuePairing law occurrence word right = 0) ↔
      ((faithfulLaw law).faithfulAt occurrence).freeEvaluation word = 0 := by
  constructor
  · intro zero
    exact (valuePairing_self_zero_iff law occurrence word).mp (zero word)
  · intro zero right
    change ((faithfulLaw law).faithfulAt occurrence).freeEvaluation word *
      ((faithfulLaw law).faithfulAt occurrence).freeEvaluation right = 0
    rw [zero, zero_mul]

theorem valuePairing_kernel_eq_freeEvaluation_kernel [IsReduced Carrier]
    (law : Law D Carrier) {state : D.State}
    (occurrence : (source D).toRootSource.actual.OccurrenceAt state) :
    LinearMap.ker (valuePairing law occurrence) =
      LinearMap.ker (((faithfulLaw law).faithfulAt occurrence).freeEvaluation) := by
  ext word
  change valuePairing law occurrence word = 0 ↔
    ((faithfulLaw law).faithfulAt occurrence).freeEvaluation word = 0
  constructor
  · intro zero
    apply (valuePairing_left_kernel_iff law occurrence word).mp
    intro right
    rw [zero]
    rfl
  · intro zero
    apply LinearMap.ext
    intro right
    exact (valuePairing_left_kernel_iff law occurrence word).mpr zero right

/-- The entire curried pairing has exactly the original evaluator's inverse
fibres among words of this fixed source. A single diagonal value alone has
no such recovery law. -/
theorem valuePairing_fibre_iff_freeEvaluation_fibre [IsReduced Carrier]
    (law : Law D Carrier) {state : D.State}
    (occurrence : (source D).toRootSource.actual.OccurrenceAt state)
    (left right : law.Generator →₀ ℤ) :
    valuePairing law occurrence left = valuePairing law occurrence right ↔
      ((faithfulLaw law).faithfulAt occurrence).freeEvaluation left =
        ((faithfulLaw law).faithfulAt occurrence).freeEvaluation right := by
  have kernel := valuePairing_kernel_eq_freeEvaluation_kernel law occurrence
  constructor
  · intro same
    have zero : left - right ∈ LinearMap.ker (valuePairing law occurrence) := by
      change valuePairing law occurrence (left - right) = 0
      rw [map_sub, same, sub_self]
    rw [kernel] at zero
    change ((faithfulLaw law).faithfulAt occurrence).freeEvaluation (left - right) = 0
      at zero
    have readSub := (((faithfulLaw law).faithfulAt occurrence).freeEvaluation).map_sub
      left right
    exact sub_eq_zero.mp (readSub.symm.trans zero)
  · intro same
    have zero : left - right ∈
        LinearMap.ker (((faithfulLaw law).faithfulAt occurrence).freeEvaluation) := by
      change ((faithfulLaw law).faithfulAt occurrence).freeEvaluation (left - right) = 0
      have readSub := (((faithfulLaw law).faithfulAt occurrence).freeEvaluation).map_sub
        left right
      exact readSub.trans (sub_eq_zero.mpr same)
    rw [← kernel] at zero
    change valuePairing law occurrence (left - right) = 0 at zero
    rw [map_sub] at zero
    exact sub_eq_zero.mp zero

/-- Canonical recovery on the actual image of the complete pairing. It is
the existing quotient-by-kernel factorization followed by the first
isomorphism theorem; no representative or inverse value is supplied. -/
def valuePairingRangeRecovery [IsReduced Carrier]
    (law : Law D Carrier) {state : D.State}
    (occurrence : (source D).toRootSource.actual.OccurrenceAt state) :
    LinearMap.range (valuePairing law occurrence) →ₗ[ℤ] Carrier :=
  ((LinearMap.ker (valuePairing law occurrence)).liftQ
    (((faithfulLaw law).faithfulAt occurrence).freeEvaluation)
    (valuePairing_kernel_eq_freeEvaluation_kernel law occurrence).le).comp
      ((valuePairing law occurrence).quotKerEquivRange.symm.toLinearMap)

theorem valuePairingRangeRecovery_actual [IsReduced Carrier]
    (law : Law D Carrier) {state : D.State}
    (occurrence : (source D).toRootSource.actual.OccurrenceAt state)
    (word : law.Generator →₀ ℤ) :
    valuePairingRangeRecovery law occurrence
        ⟨valuePairing law occurrence word, ⟨word, rfl⟩⟩ =
      ((faithfulLaw law).faithfulAt occurrence).freeEvaluation word := by
  let pairing := valuePairing law occurrence
  let read := ((faithfulLaw law).faithfulAt occurrence).freeEvaluation
  have image : pairing word ∈ LinearMap.range pairing := ⟨word, rfl⟩
  have inverse := LinearMap.quotKerEquivRange_symm_apply_image pairing word image
  change ((LinearMap.ker pairing).liftQ read
      (valuePairing_kernel_eq_freeEvaluation_kernel law occurrence).le)
        (pairing.quotKerEquivRange.symm ⟨pairing word, image⟩) = read word
  rw [inverse]
  rfl

end
end RawGeneratedRoot.CofinalAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
