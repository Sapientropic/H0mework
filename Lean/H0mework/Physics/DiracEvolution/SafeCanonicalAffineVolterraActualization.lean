import H0mework.Physics.DiracEvolution.SafeCanonicalAffineVolterraRecognition

/-!
# Canonical affine Volterra actualization

Countability puts all canonical dense-test Volterra reads on one common
full-measure time occurrence.  The existing mother-mass Riesz law then makes
the already generated physical `L²` value unique at every such occurrence.
No solution field, subsequence, target, or new evolution is supplied.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CauchySafeMatterCanonicalAffineVolterraActualization

open Filter MeasureTheory Set
open StageNineCauchySafeMatterSpatialL2TestCarrier
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterCanonicalAffineTailEnergyActionLaw
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterCanonicalAffineVolterraRecognition
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterSameSourceGalerkinFamily
open StageNineDiracMatterSpatialEnergyBalance

noncomputable section

set_option autoImplicit false

/-- All countably many canonical dense reads obey the generated Volterra law
on one common full-measure time set. -/
theorem canonicalAffinePhysicalTimeL2MassRead_ae_all_volterraRepresentative
    (timeEnd : ℝ)
    (timePositive : 0 < timeEnd)
    (a b : DiracMatterSpatialCoordinates)
    (boxOrder : a ≤ b) :
    ∀ᵐ time ∂volume.restrict (Icc 0 timeEnd), ∀ test : ℕ,
      canonicalAffinePhysicalTimeL2MassRead
          timeEnd timePositive.le a b boxOrder test
            (projIcc 0 timeEnd timePositive.le time) =
        canonicalAffinePhysicalMassVolterraRepresentative
          timeEnd timePositive a b boxOrder test time := by
  apply ae_all_iff.2
  intro test
  exact canonicalAffinePhysicalTimeL2MassRead_ae_eq_volterraRepresentative
    timeEnd timePositive a b boxOrder test

/-- One exact time occurrence on which every canonical dense read of the
source-generated output has its Volterra value. -/
structure CanonicalAffineVolterraDenseReadOccurrence
    (timeEnd : ℝ)
    (timePositive : 0 < timeEnd)
    (a b : DiracMatterSpatialCoordinates)
    (boxOrder : a ≤ b) where
  time : Icc 0 timeEnd
  reads : ∀ test : ℕ,
    canonicalAffinePhysicalTimeL2MassRead
        timeEnd timePositive.le a b boxOrder test time =
      canonicalAffinePhysicalMassVolterraRepresentative
        timeEnd timePositive a b boxOrder test time.1

/-- A positive source-time interval contains an exact common dense-read
occurrence. -/
theorem nonempty_canonicalAffineVolterraDenseReadOccurrence
    (timeEnd : ℝ)
    (timePositive : 0 < timeEnd)
    (a b : DiracMatterSpatialCoordinates)
    (boxOrder : a ≤ b) :
    Nonempty (CanonicalAffineVolterraDenseReadOccurrence
      timeEnd timePositive a b boxOrder) := by
  let μ : Measure ℝ := volume.restrict (Icc 0 timeEnd)
  have μne : μ ≠ 0 := by
    intro μzero
    have univZero : μ Set.univ = 0 := by rw [μzero]; simp
    rw [Measure.restrict_apply_univ, Real.volume_Icc] at univZero
    have timeNonpositive : timeEnd ≤ 0 := by simpa [μ] using univZero
    exact (not_le_of_gt timePositive) timeNonpositive
  letI : NeZero μ := ⟨μne⟩
  have reads :=
    canonicalAffinePhysicalTimeL2MassRead_ae_all_volterraRepresentative
      timeEnd timePositive a b boxOrder
  have readsAndMem : ∀ᵐ time ∂μ,
      (∀ test : ℕ,
        canonicalAffinePhysicalTimeL2MassRead
            timeEnd timePositive.le a b boxOrder test
              (projIcc 0 timeEnd timePositive.le time) =
          canonicalAffinePhysicalMassVolterraRepresentative
            timeEnd timePositive a b boxOrder test time) ∧
        time ∈ Icc 0 timeEnd := by
    exact reads.and (ae_restrict_mem measurableSet_Icc)
  obtain ⟨time, timeReads, timeMem⟩ := readsAndMem.exists
  let physicalTime : Icc 0 timeEnd := ⟨time, timeMem⟩
  refine ⟨{ time := physicalTime, reads := ?_ }⟩
  intro test
  have projEq : projIcc 0 timeEnd timePositive.le time = physicalTime := by
    exact projIcc_val timePositive.le physicalTime
  rw [projEq] at timeReads
  exact timeReads test

/-- The physical value carried by a common dense-read occurrence is the
already generated whole-time `L²` output's value there. -/
def CanonicalAffineVolterraDenseReadOccurrence.physicalField
    {timeEnd : ℝ}
    {timePositive : 0 < timeEnd}
    {a b : DiracMatterSpatialCoordinates}
    {boxOrder : a ≤ b}
    (occurrence : CanonicalAffineVolterraDenseReadOccurrence
      timeEnd timePositive a b boxOrder) : CauchySafeMatterSpatialL2 a b :=
  canonicalAffinePhysicalTimeL2Output
    timeEnd timePositive.le a b boxOrder occurrence.time

theorem CanonicalAffineVolterraDenseReadOccurrence.physicalField_massRead
    {timeEnd : ℝ}
    {timePositive : 0 < timeEnd}
    {a b : DiracMatterSpatialCoordinates}
    {boxOrder : a ≤ b}
    (occurrence : CanonicalAffineVolterraDenseReadOccurrence
      timeEnd timePositive a b boxOrder)
    (test : ℕ) :
    fixedP506L0CauchySafeMatterSpatialMassRead occurrence.time.1 a b
        occurrence.physicalField test =
      canonicalAffinePhysicalMassVolterraRepresentative
        timeEnd timePositive a b boxOrder test occurrence.time.1 := by
  have readEq := canonicalAffinePhysicalTimeL2MassRead_eq_spatialMassRead
    timeEnd timePositive.le a b boxOrder test occurrence.time
  exact readEq.symm.trans (occurrence.reads test)

/-- Dense Volterra mass reads uniquely determine the physical spatial `L²`
value at the same exact occurrence. -/
theorem CanonicalAffineVolterraDenseReadOccurrence.physicalField_unique
    {timeEnd : ℝ}
    {timePositive : 0 < timeEnd}
    {a b : DiracMatterSpatialCoordinates}
    {boxOrder : a ≤ b}
    (occurrence : CanonicalAffineVolterraDenseReadOccurrence
      timeEnd timePositive a b boxOrder)
    (candidate : CauchySafeMatterSpatialL2 a b)
    (candidateReads : ∀ test,
      fixedP506L0CauchySafeMatterSpatialMassRead occurrence.time.1 a b
          candidate test =
        canonicalAffinePhysicalMassVolterraRepresentative
          timeEnd timePositive a b boxOrder test occurrence.time.1) :
    candidate = occurrence.physicalField := by
  apply fixedP506L0CauchySafeMatterSpatialMassRead_injective
    occurrence.time.1 a b boxOrder
  intro test
  exact (candidateReads test).trans (occurrence.physicalField_massRead test).symm

/-! ## Exact generated-limit occurrence -/

/-- The exact lower occurrence emitted by the complete canonical affine
history on one fixed source slab and spatial box.  It has one constructor and
no selector, representative, output, or completion payload. -/
inductive CanonicalAffineVolterraLimitOccurrence
    (timeEnd : ℝ)
    (_timePositive : 0 < timeEnd)
    (a b : DiracMatterSpatialCoordinates)
    (_boxOrder : a ≤ b) : Type
  | generated

instance canonicalAffineVolterraLimitOccurrenceUnique
    (timeEnd : ℝ)
    (timePositive : 0 < timeEnd)
    (a b : DiracMatterSpatialCoordinates)
    (boxOrder : a ≤ b) :
    Unique (CanonicalAffineVolterraLimitOccurrence
      timeEnd timePositive a b boxOrder) where
  default := .generated
  uniq occurrence := by cases occurrence; rfl

/-- The exact occurrence reads the already generated whole-time physical
output; it does not carry or select that output. -/
def CanonicalAffineVolterraLimitOccurrence.physicalOutput
    {timeEnd : ℝ}
    {timePositive : 0 < timeEnd}
    {a b : DiracMatterSpatialCoordinates}
    {boxOrder : a ≤ b}
    (_occurrence : CanonicalAffineVolterraLimitOccurrence
      timeEnd timePositive a b boxOrder) :=
  canonicalAffinePhysicalTimeL2Output
    timeEnd timePositive.le a b boxOrder

theorem CanonicalAffineVolterraLimitOccurrence.physicalOutput_eq
    {timeEnd : ℝ}
    {timePositive : 0 < timeEnd}
    {a b : DiracMatterSpatialCoordinates}
    {boxOrder : a ≤ b}
    (occurrence : CanonicalAffineVolterraLimitOccurrence
      timeEnd timePositive a b boxOrder) :
    occurrence.physicalOutput =
      canonicalAffinePhysicalTimeL2Output
        timeEnd timePositive.le a b boxOrder :=
  rfl

/-- No alternate presentation of the same exact occurrence can change its
authoritative physical output. -/
theorem CanonicalAffineVolterraLimitOccurrence.physicalOutput_eq_of_occurrences
    {timeEnd : ℝ}
    {timePositive : 0 < timeEnd}
    {a b : DiracMatterSpatialCoordinates}
    {boxOrder : a ≤ b}
    (first second : CanonicalAffineVolterraLimitOccurrence
      timeEnd timePositive a b boxOrder) :
    first.physicalOutput = second.physicalOutput :=
  rfl

/-- The source-generated Volterra recognition belongs to the same exact
lower occurrence as the physical output. -/
theorem CanonicalAffineVolterraLimitOccurrence.massRead_ae_eq_volterra
    {timeEnd : ℝ}
    {timePositive : 0 < timeEnd}
    {a b : DiracMatterSpatialCoordinates}
    {boxOrder : a ≤ b}
    (_occurrence : CanonicalAffineVolterraLimitOccurrence
      timeEnd timePositive a b boxOrder)
    (test : ℕ) :
    ∀ᵐ time ∂volume.restrict (Icc 0 timeEnd),
      canonicalAffinePhysicalTimeL2MassRead
          timeEnd timePositive.le a b boxOrder test
            (projIcc 0 timeEnd timePositive.le time) =
        canonicalAffinePhysicalMassVolterraRepresentative
          timeEnd timePositive a b boxOrder test time :=
  canonicalAffinePhysicalTimeL2MassRead_ae_eq_volterraRepresentative
    timeEnd timePositive a b boxOrder test

/-- The exact limit event has a common dense-read occurrence downstream; the
event itself remains the unique source-history token. -/
theorem CanonicalAffineVolterraLimitOccurrence.hasCommonDenseReadOccurrence
    {timeEnd : ℝ}
    {timePositive : 0 < timeEnd}
    {a b : DiracMatterSpatialCoordinates}
    {boxOrder : a ≤ b}
    (_occurrence : CanonicalAffineVolterraLimitOccurrence
      timeEnd timePositive a b boxOrder) :
    Nonempty (CanonicalAffineVolterraDenseReadOccurrence
      timeEnd timePositive a b boxOrder) :=
  nonempty_canonicalAffineVolterraDenseReadOccurrence
    timeEnd timePositive a b boxOrder

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CauchySafeMatterCanonicalAffineVolterraActualization
