import H0mework.Physics.SourceContracts.P448

/-!
# Proposition 449: physical-faithfulness layer for the grand-unification kernel

P447 gives the current grand-unification target a single irreducible producer
kernel.  P448 proves that this kernel is still too weak: a degenerate toy
carrier with zero Yukawa output, zero CKM/H¹, and identity RG inhabits it.

This file adds the missing shape of the next front door.  A physically
faithful kernel must be nondegenerate along the producer axes that the roadmap
keeps naming as real work:

* a nonzero selected Yukawa output;
* a nonzero sampled Yukawa sigma;
* a nonzero selected CKM output;
* a nonzero CKM H¹ class;
* a nontrivial RG action on the accepted constraint surface.

No physical instance is constructed here.  The point is sharper: the old
P447/P448 toy solution is now mechanically rejected, and any future "holy
grail" proof must inhabit this stricter front door rather than the normal-form
kernel alone.
-/

namespace SaturationMonoid
namespace StandardModelConstraint

namespace GrandUnificationProducerNormalForm

variable {Index A CKMCarrier : Type*} [AddCommGroup A]

/-! ## Faithfulness predicates -/

/-- At least one selected Yukawa slot is nonzero. -/
def HasNonzeroSelectedYukawa
    (K : IrreducibleGrandUnificationProducerKernel Index A CKMCarrier) :
    Prop :=
  ∃ y : YukawaParameter,
    K.generated K.selectedSeed (yukawaSlot y) ≠ 0

/-- At least one selected Yukawa sampled sigma is nonzero. -/
def HasNonzeroSampledYukawaSigma
    (K : IrreducibleGrandUnificationProducerKernel Index A CKMCarrier) :
    Prop :=
  ∃ y : YukawaParameter,
    K.sigma (StandardModelScaleCode.yukawa y) ≠ 0

/-- At least one selected CKM slot is nonzero. -/
def HasNonzeroSelectedCKM
    (K : IrreducibleGrandUnificationProducerKernel Index A CKMCarrier) :
    Prop :=
  ∃ a : CKMParameter,
    K.generated K.selectedSeed (ckmSlot a) ≠ 0

/-- The CKM carrier maps some selected input to a nonzero H¹ class. -/
def HasNonzeroCKMH1Class
    (K : IrreducibleGrandUnificationProducerKernel Index A CKMCarrier) :
    Prop :=
  ∃ seed : DiscreteStandardModelSeed,
    K.ckm.toH1 (K.ckmInput seed) ≠
      CechAdditiveCover.h1Zero K.ckm.cover

/-- The RG flow does something nontrivial on an accepted parameter vector. -/
def HasNontrivialRGOnConstraint
    (K : IrreducibleGrandUnificationProducerKernel Index A CKMCarrier) :
    Prop :=
  ∃ s : StandardModelScaleCode, ∃ p : ParameterVector ℝ,
    K.constraints p ∧ K.rg.evolve s p ≠ p

/-- The nondegenerate physical-faithfulness layer for the P447 kernel.

This is intentionally stricter than mere `Nonempty` of the kernel.  It is the
first Lean-level firewall against the P448 degenerate inhabitant. -/
structure KernelPhysicalFaithfulness
    (K : IrreducibleGrandUnificationProducerKernel Index A CKMCarrier) :
    Prop where
  nonzeroSelectedYukawa : HasNonzeroSelectedYukawa K
  nonzeroSampledYukawaSigma : HasNonzeroSampledYukawaSigma K
  nonzeroSelectedCKM : HasNonzeroSelectedCKM K
  nonzeroCKMH1 : HasNonzeroCKMH1Class K
  nontrivialRG : HasNontrivialRGOnConstraint K

/-- The stricter current front door: not merely an irreducible kernel, but a
physically faithful one. -/
def PhysicallyFaithfulGrandUnificationFrontDoor
    (Index A CKMCarrier : Type*) [AddCommGroup A] : Prop :=
  ∃ K : IrreducibleGrandUnificationProducerKernel Index A CKMCarrier,
    KernelPhysicalFaithfulness K

/-! ## Transport back to the existing normal forms -/

/-- THEOREM 1: a physically faithful front door still supplies the P447
irreducible kernel. -/
theorem faithfulFrontDoor_implies_irreducibleKernel :
    PhysicallyFaithfulGrandUnificationFrontDoor Index A CKMCarrier ->
      Nonempty (IrreducibleGrandUnificationProducerKernel Index A CKMCarrier) := by
  rintro ⟨K, _hfaithful⟩
  exact ⟨K⟩

/-- THEOREM 2: a physically faithful front door supplies the current central
holy-grail constants, via P447. -/
theorem faithfulFrontDoor_implies_currentCentralHolyGrailConstants :
    PhysicallyFaithfulGrandUnificationFrontDoor Index A CKMCarrier ->
      CurrentFormalExactGeometryCentralHolyGrailConstants
        Index A CKMCarrier := by
  intro h
  exact
    (currentCentralHolyGrailConstants_iff_irreducibleProducerKernel
      (Index := Index) (A := A) (CKMCarrier := CKMCarrier)).mpr
      (faithfulFrontDoor_implies_irreducibleKernel
        (Index := Index) (A := A) (CKMCarrier := CKMCarrier) h)

/-- THEOREM 3: a physically faithful front door supplies the single-source
receipt, via P447. -/
theorem faithfulFrontDoor_implies_singleSourcePhysicalHolyGrailReceipt :
    PhysicallyFaithfulGrandUnificationFrontDoor Index A CKMCarrier ->
      Nonempty
        (SingleSourcePhysicalGrandUnificationHolyGrailReceipt
          Index A CKMCarrier) := by
  intro h
  exact
    (irreducibleProducerKernel_iff_singleSourcePhysicalHolyGrailReceipt
      (Index := Index) (A := A) (CKMCarrier := CKMCarrier)).mp
      (faithfulFrontDoor_implies_irreducibleKernel
        (Index := Index) (A := A) (CKMCarrier := CKMCarrier) h)

/-! ## P448 toy rejection -/

namespace DegenerateKernelAudit

/-- THEOREM 4: the P448 toy kernel has no nonzero selected Yukawa slot. -/
theorem unitToy_not_nonzeroSelectedYukawa :
    ¬ HasNonzeroSelectedYukawa unitToyKernel := by
  rintro ⟨y, hy⟩
  exact hy (unitToy_yukawa_zero unitToyKernel.selectedSeed y)

/-- THEOREM 5: the P448 toy kernel has no nonzero sampled Yukawa sigma. -/
theorem unitToy_not_nonzeroSampledYukawaSigma :
    ¬ HasNonzeroSampledYukawaSigma unitToyKernel := by
  rintro ⟨y, hy⟩
  cases y <;> exact hy rfl

/-- THEOREM 6: the P448 toy kernel has no nonzero selected CKM slot. -/
theorem unitToy_not_nonzeroSelectedCKM :
    ¬ HasNonzeroSelectedCKM unitToyKernel := by
  rintro ⟨a, ha⟩
  exact ha (unitToy_ckm_zero unitToyKernel.selectedSeed a)

/-- THEOREM 7: the P448 toy kernel has no nonzero CKM H¹ class. -/
theorem unitToy_not_nonzeroCKMH1Class :
    ¬ HasNonzeroCKMH1Class unitToyKernel := by
  rintro ⟨seed, hseed⟩
  exact hseed rfl

/-- THEOREM 8: the P448 toy kernel has no nontrivial RG action on accepted
vectors. -/
theorem unitToy_not_nontrivialRGOnConstraint :
    ¬ HasNontrivialRGOnConstraint unitToyKernel := by
  rintro ⟨s, p, _hp, hneq⟩
  exact hneq rfl

/-- THEOREM 9: the P448 toy kernel fails every faithfulness facet. -/
theorem unitToy_fails_all_faithfulness_facets :
    (¬ HasNonzeroSelectedYukawa unitToyKernel) ∧
    (¬ HasNonzeroSampledYukawaSigma unitToyKernel) ∧
    (¬ HasNonzeroSelectedCKM unitToyKernel) ∧
    (¬ HasNonzeroCKMH1Class unitToyKernel) ∧
    (¬ HasNontrivialRGOnConstraint unitToyKernel) := by
  exact
    ⟨unitToy_not_nonzeroSelectedYukawa,
      unitToy_not_nonzeroSampledYukawaSigma,
      unitToy_not_nonzeroSelectedCKM,
      unitToy_not_nonzeroCKMH1Class,
      unitToy_not_nontrivialRGOnConstraint⟩

/-- THEOREM 10: the P448 toy kernel is not physically faithful. -/
theorem unitToy_not_kernelPhysicalFaithfulness :
    ¬ KernelPhysicalFaithfulness unitToyKernel := by
  intro h
  exact unitToy_not_nonzeroSelectedYukawa h.nonzeroSelectedYukawa

/-- THEOREM 11: the old front door is strictly weaker than the new faithful
front door at the level of available evidence: P448 supplies a kernel inhabitant
that the new front door rejects. -/
theorem unitToy_kernel_nonempty_but_not_faithful :
    Nonempty (IrreducibleGrandUnificationProducerKernel Unit Unit Unit) ∧
      ¬ KernelPhysicalFaithfulness unitToyKernel := by
  exact ⟨unitToyKernel_nonempty, unitToy_not_kernelPhysicalFaithfulness⟩

end DegenerateKernelAudit

end GrandUnificationProducerNormalForm

end StandardModelConstraint
end SaturationMonoid
