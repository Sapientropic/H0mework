import H0mework.Physics.SourceContracts.P449

/-!
# Proposition 519: singleton-collapse kills the P449 RG producer

P449 tried to harden the grand-unification producer by requiring nontrivial RG
motion on the accepted constraint surface.  This file proves that this demand
is not merely hard; in the current P447 kernel it is impossible.

The reason is structural.  P447 also requires

`constraints_exact_selected : constraints p <-> p = generated selectedSeed`.

So the accepted surface is a singleton.  Any RG flow preserving that surface
must fix every accepted vector.  Therefore `HasNontrivialRGOnConstraint` is
false for every irreducible kernel, not only for the P448 toy inhabitant.

This is the producer-level correction: physical RG dynamics cannot live after
the zero-continuous-parameter quotient has collapsed the surface to one point.
It has to be produced on the pre-collapse running surface and only then
projected to the selected zero-free output.
-/

namespace SaturationMonoid
namespace StandardModelConstraint
namespace GrandUnificationProducerNormalForm

variable {Index A CKMCarrier : Type*} [AddCommGroup A]

/-! ## Singleton accepted surfaces force RG fixed points -/

/-- THEOREM 1: every RG flow preserving the P447 selected singleton fixes every
accepted parameter vector. -/
theorem rg_fixed_on_selected_singleton
    (K : IrreducibleGrandUnificationProducerKernel Index A CKMCarrier)
    (s : StandardModelScaleCode) (p : ParameterVector ℝ)
    (hp : K.constraints p) :
    K.rg.evolve s p = p := by
  have hp_selected : p = K.generated K.selectedSeed :=
    (K.constraints_exact_selected p).mp hp
  have hevolved_constraints : K.constraints (K.rg.evolve s p) :=
    K.rg_preserves_constraints s p hp
  have hevolved_selected :
      K.rg.evolve s p = K.generated K.selectedSeed :=
    (K.constraints_exact_selected (K.rg.evolve s p)).mp
      hevolved_constraints
  exact hevolved_selected.trans hp_selected.symm

/-- THEOREM 2: no P447 irreducible kernel can satisfy P449's nontrivial-RG
faithfulness facet. -/
theorem no_nontrivialRGOnConstraint_of_irreducibleKernel
    (K : IrreducibleGrandUnificationProducerKernel Index A CKMCarrier) :
    ¬ HasNontrivialRGOnConstraint K := by
  rintro ⟨s, p, hp, hne⟩
  exact hne (rg_fixed_on_selected_singleton K s p hp)

/-- THEOREM 3: P449's `KernelPhysicalFaithfulness` is uninhabited for every
P447 irreducible kernel. -/
theorem no_kernelPhysicalFaithfulness_of_irreducibleKernel
    (K : IrreducibleGrandUnificationProducerKernel Index A CKMCarrier) :
    ¬ KernelPhysicalFaithfulness K := by
  intro hfaithful
  exact
    no_nontrivialRGOnConstraint_of_irreducibleKernel K
      hfaithful.nontrivialRG

/-- THEOREM 4: the P449 faithful front door is empty for all carriers, because
its RG facet is placed after the selected-surface singleton collapse. -/
theorem no_physicallyFaithfulGrandUnificationFrontDoor :
    ¬ PhysicallyFaithfulGrandUnificationFrontDoor Index A CKMCarrier := by
  rintro ⟨K, hfaithful⟩
  exact no_kernelPhysicalFaithfulness_of_irreducibleKernel K hfaithful

/-! ## Corrected producer target -/

/-- A running-surface RG witness must be supplied before the selected singleton
quotient is imposed.

This is intentionally a separate producer target, not a replacement theorem:
P519 proves that the old post-collapse target is empty, so the next real
producer must carry a pre-collapse running surface plus a projection to the
zero-continuous selected output. -/
structure PreCollapseRunningRGProducer
    (Index A CKMCarrier : Type*) [AddCommGroup A] where
  generated : DiscreteStandardModelSeed -> ParameterVector ℝ
  preConstraints : ParameterVector ℝ -> Prop
  selectedSeed : DiscreteStandardModelSeed
  selectedConstraints : ParameterVector ℝ -> Prop
  rg : RenormalizationGroupFlow StandardModelScaleCode ℝ
  pre_generated_satisfies :
    ∀ seed : DiscreteStandardModelSeed, preConstraints (generated seed)
  pre_rg_preserves :
    ∀ s p, preConstraints p -> preConstraints (rg.evolve s p)
  selected_exact :
    ∀ p : ParameterVector ℝ,
      selectedConstraints p <-> p = generated selectedSeed
  selected_in_pre :
    ∀ p, selectedConstraints p -> preConstraints p
  nontrivial_pre_rg :
    ∃ s : StandardModelScaleCode, ∃ seed : DiscreteStandardModelSeed,
      rg.evolve s (generated seed) ≠ generated seed

/-- THEOREM 5: a pre-collapse RG producer cannot be confused with P449's empty
post-collapse RG facet; it witnesses nontrivial dynamics on the running surface
before projection. -/
theorem preCollapseRunningRGProducer_has_nontrivial_pre_rg
    (P : PreCollapseRunningRGProducer Index A CKMCarrier) :
    ∃ s : StandardModelScaleCode, ∃ seed : DiscreteStandardModelSeed,
      P.rg.evolve s (P.generated seed) ≠ P.generated seed :=
  P.nontrivial_pre_rg

/-! ## A minimal inhabited pre-collapse running producer -/

namespace PreCollapseRunningRGProducerAudit

/-- A one-slot nonzero vector used only to witness nontrivial pre-collapse RG
motion. -/
def qcdThetaOneVector : ParameterVector ℝ
  | StandardModelParameter.qcd_theta => 1
  | _ => 0

/-- The finite sign character used by the minimal running producer: the weak
scale acts by sign flip, all other scale labels act trivially. -/
def weakSign : StandardModelScaleCode -> ℝ
  | StandardModelScaleCode.weak => -1
  | _ => 1

/-- A `Z₂`-style composition on the two visible sign sectors, totalized over
all declared scale labels by sending non-weak labels to the identity sector. -/
def weakSignCompose
    (s t : StandardModelScaleCode) : StandardModelScaleCode :=
  match s, t with
  | StandardModelScaleCode.weak, StandardModelScaleCode.weak =>
      StandardModelScaleCode.gut
  | StandardModelScaleCode.weak, _ => StandardModelScaleCode.weak
  | _, StandardModelScaleCode.weak => StandardModelScaleCode.weak
  | _, _ => StandardModelScaleCode.gut

/-- THEOREM 6: `weakSignCompose` is exactly multiplication of the sign
character. -/
theorem weakSign_compose
    (s t : StandardModelScaleCode) :
    weakSign (weakSignCompose s t) = weakSign s * weakSign t := by
  cases s <;> cases t <;> simp [weakSign, weakSignCompose]

/-- A concrete pre-collapse RG flow: each scale label acts by multiplying the
whole 19-slot vector by its `weakSign`.  This is deliberately minimal; its role
is to witness that lawful nontrivial RG motion is possible before the selected
singleton quotient is imposed. -/
def weakSignRG : RenormalizationGroupFlow StandardModelScaleCode ℝ where
  evolve := fun s p slot => weakSign s * p slot
  idScale := StandardModelScaleCode.gut
  composeScale := weakSignCompose
  evolve_id := by
    intro p
    funext slot
    simp [weakSign]
  evolve_compose := by
    intro s t p
    funext slot
    rw [weakSign_compose]
    ring

/-- THEOREM 7: the weak-sign RG flow is nontrivial on `qcdThetaOneVector`. -/
theorem weakSignRG_nontrivial_on_qcdThetaOneVector :
    weakSignRG.evolve StandardModelScaleCode.weak qcdThetaOneVector ≠
      qcdThetaOneVector := by
  intro h
  have hslot := congrFun h StandardModelParameter.qcd_theta
  norm_num [weakSignRG, weakSign, qcdThetaOneVector] at hslot

/-- A concrete inhabited pre-collapse running producer.

The pre-collapse surface is intentionally broad (`True`) so the weak-sign RG
has room to move.  The selected output is a singleton.  This is the corrected
coordinate shape: dynamics first, zero-free selected projection afterward. -/
def toyPreCollapseRunningRGProducer :
    PreCollapseRunningRGProducer Unit Unit Unit where
  generated := fun _ => qcdThetaOneVector
  preConstraints := fun _ => True
  selectedSeed := DegenerateKernelAudit.toySeed
  selectedConstraints := fun p => p = qcdThetaOneVector
  rg := weakSignRG
  pre_generated_satisfies := by
    intro _seed
    trivial
  pre_rg_preserves := by
    intro _s _p _hp
    trivial
  selected_exact := by
    intro p
    rfl
  selected_in_pre := by
    intro _p _hp
    trivial
  nontrivial_pre_rg := by
    exact
      ⟨StandardModelScaleCode.weak,
        DegenerateKernelAudit.toySeed,
        weakSignRG_nontrivial_on_qcdThetaOneVector⟩

/-- THEOREM 7: the corrected pre-collapse running-RG producer target is
inhabited, unlike P449's post-collapse faithful front door. -/
theorem toyPreCollapseRunningRGProducer_nonempty :
    Nonempty (PreCollapseRunningRGProducer Unit Unit Unit) :=
  ⟨toyPreCollapseRunningRGProducer⟩

end PreCollapseRunningRGProducerAudit

end GrandUnificationProducerNormalForm
end StandardModelConstraint
end SaturationMonoid
