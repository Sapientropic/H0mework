/-
  Proposition 270: concrete Standard-Model gauge embedding into SU(7).

  P269 turned the first physics-facing roadmap item into a P203 adapter.
  This file performs the analogous first, conservative step for the second
  item: name the concrete group objects and the shape of the block-diagonal
  embedding certificate.

  The direction matters: the Standard Model gauge group is represented as a
  subgroup/embedded copy inside the unified `SU(7)` carrier.  The certificate
  is therefore an injective embedding into `SU(7)`, not a projection out of it.

  Boundary: this file proves the subgroup/embedding consequences of a supplied
  injective block-diagonal homomorphism.  It does not yet build the concrete
  `diag(SU(3), SU(2), z, z⁻¹)` matrix and prove its determinant/unitarity facts.
-/

import Mathlib.Analysis.Complex.Circle
import Mathlib.LinearAlgebra.UnitaryGroup

/-! ## Concrete gauge group objects -/

namespace SaturationMonoid
namespace GaugeProjection

/-- Candidate unified fiber group for the roadmap's SU(7) slice. -/
abbrev SU7Gauge := Matrix.specialUnitaryGroup (Fin 7) ℂ

/-- Standard Model color factor. -/
abbrev SU3Gauge := Matrix.specialUnitaryGroup (Fin 3) ℂ

/-- Standard Model weak-isospin factor. -/
abbrev SU2Gauge := Matrix.specialUnitaryGroup (Fin 2) ℂ

/-- Standard Model hypercharge factor, represented as the unit circle `U(1)`. -/
abbrev U1Gauge := Circle

/-- The concrete candidate Standard Model gauge group object. -/
abbrev StandardModelGaugeGroup := SU3Gauge × SU2Gauge × U1Gauge

/-- Projection to the color `SU(3)` factor. -/
def standardModelColorProjection : StandardModelGaugeGroup →* SU3Gauge where
  toFun g := g.1
  map_one' := rfl
  map_mul' _ _ := rfl

/-- Projection to the weak `SU(2)` factor. -/
def standardModelWeakProjection : StandardModelGaugeGroup →* SU2Gauge where
  toFun g := g.2.1
  map_one' := rfl
  map_mul' _ _ := rfl

/-- Projection to the hypercharge `U(1)` factor. -/
def standardModelHyperchargeProjection : StandardModelGaugeGroup →* U1Gauge where
  toFun g := g.2.2
  map_one' := rfl
  map_mul' _ _ := rfl

/-- Inclusion of the color factor into the Standard Model product group. -/
noncomputable def standardModelColorInclusion : SU3Gauge →* StandardModelGaugeGroup where
  toFun c := (c, 1, 1)
  map_one' := rfl
  map_mul' _ _ := by simp

/-- Inclusion of the weak factor into the Standard Model product group. -/
noncomputable def standardModelWeakInclusion : SU2Gauge →* StandardModelGaugeGroup where
  toFun w := (1, w, 1)
  map_one' := rfl
  map_mul' _ _ := by simp

/-- Inclusion of the hypercharge factor into the Standard Model product group. -/
noncomputable def standardModelHyperchargeInclusion : U1Gauge →* StandardModelGaugeGroup where
  toFun y := (1, 1, y)
  map_one' := rfl
  map_mul' _ _ := by simp

/-- THEOREM 1: the color inclusion is a section of the color projection. -/
theorem colorProjection_colorInclusion (c : SU3Gauge) :
    standardModelColorProjection (standardModelColorInclusion c) = c := by
  simp [standardModelColorProjection, standardModelColorInclusion]

/-- THEOREM 2: the weak inclusion is a section of the weak projection. -/
theorem weakProjection_weakInclusion (w : SU2Gauge) :
    standardModelWeakProjection (standardModelWeakInclusion w) = w := by
  simp [standardModelWeakProjection, standardModelWeakInclusion]

/-- THEOREM 3: the hypercharge inclusion is a section of the hypercharge
projection. -/
theorem hyperchargeProjection_hyperchargeInclusion (y : U1Gauge) :
    standardModelHyperchargeProjection (standardModelHyperchargeInclusion y) = y := by
  simp [standardModelHyperchargeProjection, standardModelHyperchargeInclusion]

/-- A conservative certificate target for the roadmap claim
`SU(3) × SU(2) × U(1) ⊂ SU(7)`.

The `blockDiagonal` map is required to be injective, so the Standard Model
gauge product is not collapsed.  Future work should replace the supplied
homomorphism with a concrete matrix-level construction, but the algebraic
direction and subgroup consequences are fixed here. -/
structure SU7StandardModelBreakingChainCertificate where
  blockDiagonal : StandardModelGaugeGroup →* SU7Gauge
  blockDiagonal_injective : Function.Injective blockDiagonal

namespace SU7StandardModelBreakingChainCertificate

/-- The embedded Standard Model gauge subgroup of `SU(7)`. -/
noncomputable def standardModelGaugeSubgroup
    (C : SU7StandardModelBreakingChainCertificate) : Subgroup SU7Gauge :=
  C.blockDiagonal.range

/-- THEOREM 4: membership in the embedded subgroup is exactly being the image
of a Standard Model gauge element. -/
theorem mem_standardModelGaugeSubgroup_iff
    (C : SU7StandardModelBreakingChainCertificate)
    (u : SU7Gauge) :
    u ∈ standardModelGaugeSubgroup C ↔
      ∃ g : StandardModelGaugeGroup, C.blockDiagonal g = u := Iff.rfl

/-- THEOREM 5: equality after block-diagonal embedding is equality in the
Standard Model gauge product. -/
theorem blockDiagonal_eq_iff
    (C : SU7StandardModelBreakingChainCertificate)
    (g h : StandardModelGaugeGroup) :
    C.blockDiagonal g = C.blockDiagonal h ↔ g = h := by
  constructor
  · intro hgh
    exact C.blockDiagonal_injective hgh
  · intro hgh
    simp [hgh]

/-- THEOREM 6: the block-diagonal map embeds the Standard Model product as a
subgroup-valued homomorphism. -/
noncomputable def blockDiagonalSubgroupEmbedding
    (C : SU7StandardModelBreakingChainCertificate) :
    StandardModelGaugeGroup →* standardModelGaugeSubgroup C where
  toFun g := ⟨C.blockDiagonal g, ⟨g, rfl⟩⟩
  map_one' := by
    exact Subtype.ext C.blockDiagonal.map_one
  map_mul' g h := by
    exact Subtype.ext (C.blockDiagonal.map_mul g h)

/-- THEOREM 7: the subgroup-valued block-diagonal embedding is injective. -/
theorem blockDiagonalSubgroupEmbedding_injective
    (C : SU7StandardModelBreakingChainCertificate) :
    Function.Injective (blockDiagonalSubgroupEmbedding C) := by
  intro g h hgh
  apply C.blockDiagonal_injective
  exact congrArg Subtype.val hgh

/-- THEOREM 8: the embedded color channel is the color-factor inclusion
followed by the block-diagonal embedding. -/
noncomputable def colorChannel
    (C : SU7StandardModelBreakingChainCertificate) : SU3Gauge →* SU7Gauge :=
  C.blockDiagonal.comp standardModelColorInclusion

/-- THEOREM 9: the embedded weak channel is the weak-factor inclusion followed
by the block-diagonal embedding. -/
noncomputable def weakChannel
    (C : SU7StandardModelBreakingChainCertificate) : SU2Gauge →* SU7Gauge :=
  C.blockDiagonal.comp standardModelWeakInclusion

/-- THEOREM 10: the embedded hypercharge channel is the hypercharge-factor
inclusion followed by the block-diagonal embedding. -/
noncomputable def hyperchargeChannel
    (C : SU7StandardModelBreakingChainCertificate) : U1Gauge →* SU7Gauge :=
  C.blockDiagonal.comp standardModelHyperchargeInclusion

/-- THEOREM 11: simultaneous equality of embedded factor triples is exactly
simultaneous equality of the three Standard Model factors. -/
theorem blockDiagonal_factors_eq_iff
    (C : SU7StandardModelBreakingChainCertificate)
    (c c' : SU3Gauge) (w w' : SU2Gauge) (y y' : U1Gauge) :
    C.blockDiagonal (c, w, y) = C.blockDiagonal (c', w', y') ↔
      c = c' ∧ w = w' ∧ y = y' := by
  constructor
  · intro h
    have hg : (c, w, y) = (c', w', y') := C.blockDiagonal_injective h
    have hc : c = c' := congrArg Prod.fst hg
    have hp : (w, y) = (w', y') := congrArg Prod.snd hg
    have hw : w = w' := congrArg Prod.fst hp
    have hy : y = y' := congrArg Prod.snd hp
    exact ⟨hc, hw, hy⟩
  · rintro ⟨hc, hw, hy⟩
    simp [hc, hw, hy]

end SU7StandardModelBreakingChainCertificate

end GaugeProjection
end SaturationMonoid

/-!
  Summary:
  - P270 names the concrete Lean group objects:
    `SU(7)` and `SU(3) × SU(2) × U(1)`.
  - It corrects the old quotient-style direction: the Standard Model gauge
    product is supplied as an injective `blockDiagonal` homomorphism into
    `SU(7)`.
  - From such a certificate, Lean derives the embedded subgroup, the
    subgroup-valued embedding, injectivity of that embedding, the embedded
    color/weak/hypercharge channels, and the factor-equality criterion.
  - Boundary: the concrete matrix-level formula
    `diag(SU(3), SU(2), z, z⁻¹)`, determinant/unitarity proof, representation
    content, Higgs breaking, anomaly cancellation, or Standard Model parameter
    derivation is not proved here.
-/
