import H0mework.Physics.AlphaSources.P532
import H0mework.Physics.MixingSources.P636

/-!
# Proposition 637: alpha_s source allocation and pre-collapse fiber shape

P635 identifies the current finite `alpha_s` producer faces as one object.
P636 does the analogous cleanup for the Yukawa / CKM side.

This file sharpens the next `alpha_s` producer debt without pretending to solve
the smooth physics in one step.  On the current finite source surface:

* the `SU(7)`-breaking coordinate is the unique active source;
* the threshold, three-loop RG, and Higgs / extra-representation coordinates
  are forced to zero by the producer-facing accounting law;
* any nontrivial RG / threshold / Higgs dynamics that still projects to this
  closed `alpha_s` output must therefore live in a pre-collapse fiber above the
  singleton output surface.

Boundary: the final physical producer still has to replace the abstract
pre-collapse fiber by an actual SU(7)-breaking / threshold / three-loop /
Higgs-spectrum calculation.  P637 proves the exact shape that producer must
have, and rules out hiding it on the already-collapsed output surface.
-/

noncomputable section

namespace SaturationMonoid
namespace StandardModelConstraint

/-! ## The canonical selected source -/

/-- The selected source family for the current finite `alpha_s` line:
`SU(7)` breaking only. -/
def alphaStrongSelectSU7Breaking :
    AlphaStrongResidualSource -> Bool
  | .su7Breaking => true
  | .threshold => false
  | .threeLoopRG => false
  | .higgsExtraRepresentation => false

/-- THEOREM 1: on the finite source surface, the `SU(7)`-breaking contribution
is exactly the displayed alpha-level gap. -/
theorem alphaStrong_sourceSurface_su7Contribution_eq_gap
    (P : AlphaStrongResidualGapProducer)
    (hP : AlphaStrongResidualProducerFiniteSourceSurface P) :
    P.contribution .su7Breaking = alphaStrongTwoLoopSMDisplayedGap ℚ := by
  have hnormal :
      AlphaStrongSU7ComponentNormalForm P.contribution :=
    (alphaStrongResidualProducerFiniteSourceSurface_iff_componentNormalForm
      P).mp hP
  rw [alphaStrongTwoLoopAlphaGap_eq_89_div_10000]
  exact hnormal .su7Breaking

/-- THEOREM 2: on the finite source surface, threshold effects are zero. -/
theorem alphaStrong_sourceSurface_threshold_eq_zero
    (P : AlphaStrongResidualGapProducer)
    (hP : AlphaStrongResidualProducerFiniteSourceSurface P) :
    P.contribution .threshold = 0 := by
  have hnormal :
      AlphaStrongSU7ComponentNormalForm P.contribution :=
    (alphaStrongResidualProducerFiniteSourceSurface_iff_componentNormalForm
      P).mp hP
  simpa using hnormal .threshold

/-- THEOREM 3: on the finite source surface, the three-loop RG source is zero.
-/
theorem alphaStrong_sourceSurface_threeLoopRG_eq_zero
    (P : AlphaStrongResidualGapProducer)
    (hP : AlphaStrongResidualProducerFiniteSourceSurface P) :
    P.contribution .threeLoopRG = 0 := by
  have hnormal :
      AlphaStrongSU7ComponentNormalForm P.contribution :=
    (alphaStrongResidualProducerFiniteSourceSurface_iff_componentNormalForm
      P).mp hP
  simpa using hnormal .threeLoopRG

/-- THEOREM 4: on the finite source surface, the Higgs / extra-representation
source is zero. -/
theorem alphaStrong_sourceSurface_higgsExtra_eq_zero
    (P : AlphaStrongResidualGapProducer)
    (hP : AlphaStrongResidualProducerFiniteSourceSurface P) :
    P.contribution .higgsExtraRepresentation = 0 := by
  have hnormal :
      AlphaStrongSU7ComponentNormalForm P.contribution :=
    (alphaStrongResidualProducerFiniteSourceSurface_iff_componentNormalForm
      P).mp hP
  simpa using hnormal .higgsExtraRepresentation

/-- THEOREM 5: selecting only `SU(7)` breaking closes the alpha-level residual
on the finite source surface. -/
theorem alphaStrong_sourceSurface_selectedSU7Sum_eq_gap
    (P : AlphaStrongResidualGapProducer)
    (hP : AlphaStrongResidualProducerFiniteSourceSurface P) :
    P.selectedSum alphaStrongSelectSU7Breaking =
      alphaStrongTwoLoopSMDisplayedGap ℚ := by
  unfold AlphaStrongResidualGapProducer.selectedSum
  unfold AlphaStrongFourSourceClosureReceipt.selectedSum
  rw [alphaStrongResidualSource_univ_sum]
  simp [alphaStrongSelectSU7Breaking,
    AlphaStrongFourSourceClosureReceipt.selectedContribution,
    AlphaStrongResidualGapProducer.toFourSourceClosureReceipt,
    AlphaStrongFourSourceClosureReceipt.contribution,
    alphaStrong_sourceSurface_su7Contribution_eq_gap P hP]

/-- THEOREM 6: the omitted non-`SU(7)` sources have zero total contribution on
the finite source surface. -/
theorem alphaStrong_sourceSurface_omittedNonSU7Sum_eq_zero
    (P : AlphaStrongResidualGapProducer)
    (hP : AlphaStrongResidualProducerFiniteSourceSurface P) :
    P.omittedSum alphaStrongSelectSU7Breaking = 0 :=
  P.omittedSum_eq_zero_of_selectedSum_eq_gap
    alphaStrongSelectSU7Breaking
    (alphaStrong_sourceSurface_selectedSU7Sum_eq_gap P hP)

/-! ## Pre-collapse fiber dynamics over the closed output -/

/-- A pre-collapse `alpha_s` residual dynamics object.

The field `Pre` is the running surface.  The map `collapse` projects a running
state to the already-closed residual producer.  A nontrivial dynamics that
preserves `collapse` is therefore genuine pre-collapse motion, not output-level
producer freedom. -/
structure PreCollapseAlphaStrongResidualDynamics where
  Pre : Type
  step : Pre -> Pre
  collapse : Pre -> AlphaStrongResidualGapProducer
  collapse_source_surface :
    ∀ x : Pre, AlphaStrongResidualProducerFiniteSourceSurface (collapse x)
  step_preserves_collapse :
    ∀ x : Pre, collapse (step x) = collapse x
  nontrivial_step :
    ∃ x : Pre, step x ≠ x

namespace PreCollapseAlphaStrongResidualDynamics

/-- THEOREM 7: every collapsed output of a pre-collapse dynamics object is the
canonical finite `alpha_s` residual producer. -/
theorem collapse_eq_canonical
    (D : PreCollapseAlphaStrongResidualDynamics)
    (x : D.Pre) :
    D.collapse x = alphaStrongSU7BreakingResidualGapProducer :=
  eq_alphaStrongSU7BreakingResidualGapProducer_of_sourceSurface
    (D.collapse x)
    (D.collapse_source_surface x)

/-- THEOREM 8: every collapsed output has inverse residual
`-89000/128511`. -/
theorem collapse_inverseCorrection_eq_target
    (D : PreCollapseAlphaStrongResidualDynamics)
    (x : D.Pre) :
    inverseCorrectionFromAlphaGap
        (alphaStrongTwoLoopSMOutput ℚ)
        (D.collapse x).producedGap =
      -((89000 : ℚ) / 128511) :=
  alphaStrongResidualProducer_sourceSurface_inverseCorrection
    (D.collapse x)
    (D.collapse_source_surface x)

/-- THEOREM 9: every collapsed output closes the displayed strong coupling. -/
theorem collapse_closes_displayedAlpha
    (D : PreCollapseAlphaStrongResidualDynamics)
    (x : D.Pre) :
    (1 : ℚ) /
        (alphaStrongTwoLoopSMOutputInverse ℚ +
          inverseCorrectionFromAlphaGap
            (alphaStrongTwoLoopSMOutput ℚ)
            (D.collapse x).producedGap) =
      alphaStrongDisplayed ℚ :=
  alphaStrongResidualProducer_sourceSurface_closes_displayedAlpha
    (D.collapse x)
    (D.collapse_source_surface x)

/-- THEOREM 10: if a pre-collapse dynamics object has nontrivial step while
preserving the closed output, its collapse map cannot be injective.  Equivalently,
the dynamics must live in a genuine fiber above the finite output surface. -/
theorem collapse_not_injective_of_nontrivial_step
    (D : PreCollapseAlphaStrongResidualDynamics) :
    ¬ Function.Injective D.collapse := by
  rintro hinj
  rcases D.nontrivial_step with ⟨x, hx⟩
  exact hx (hinj (D.step_preserves_collapse x))

end PreCollapseAlphaStrongResidualDynamics

/-! ## A minimal nonempty fiber witness -/

/-- The smallest possible pre-collapse fiber step: flip a two-point fiber. -/
def alphaStrongBoolFiberStep : Bool -> Bool :=
  Bool.not

/-- THEOREM 11: the two-point fiber step is nontrivial. -/
theorem alphaStrongBoolFiberStep_nontrivial :
    ∃ x : Bool, alphaStrongBoolFiberStep x ≠ x := by
  refine ⟨true, ?_⟩
  decide

/-- A minimal pre-collapse fiber over the closed finite `alpha_s` producer.

This is not the physical RG calculation.  It is a machine-checked inhabitant of
the corrected coordinate shape: nontrivial dynamics before collapse, canonical
closed `alpha_s` output after collapse. -/
def boolFiberAlphaStrongPreCollapseDynamics :
    PreCollapseAlphaStrongResidualDynamics where
  Pre := Bool
  step := alphaStrongBoolFiberStep
  collapse := fun _ => alphaStrongSU7BreakingResidualGapProducer
  collapse_source_surface := fun _ =>
    alphaStrongSU7BreakingResidualGapProducer_sourceSurface
  step_preserves_collapse := fun _ => rfl
  nontrivial_step := alphaStrongBoolFiberStep_nontrivial

/-! ## Receipt -/

/-- Compact certificate for the current `alpha_s` source allocation and the
pre-collapse-fiber shape required by any future smooth producer. -/
structure AlphaStrongSourceAllocationPreCollapseFiberCertificate where
  selected_source :
    AlphaStrongResidualSource -> Bool
  selected_source_eq :
    selected_source = alphaStrongSelectSU7Breaking
  su7_selected_closes :
    ∀ P : AlphaStrongResidualGapProducer,
      AlphaStrongResidualProducerFiniteSourceSurface P ->
        P.selectedSum selected_source =
          alphaStrongTwoLoopSMDisplayedGap ℚ
  omitted_non_su7_zero :
    ∀ P : AlphaStrongResidualGapProducer,
      AlphaStrongResidualProducerFiniteSourceSurface P ->
        P.omittedSum selected_source = 0
  threshold_zero :
    ∀ P : AlphaStrongResidualGapProducer,
      AlphaStrongResidualProducerFiniteSourceSurface P ->
        P.contribution .threshold = 0
  three_loop_rg_zero :
    ∀ P : AlphaStrongResidualGapProducer,
      AlphaStrongResidualProducerFiniteSourceSurface P ->
        P.contribution .threeLoopRG = 0
  higgs_extra_zero :
    ∀ P : AlphaStrongResidualGapProducer,
      AlphaStrongResidualProducerFiniteSourceSurface P ->
        P.contribution .higgsExtraRepresentation = 0
  pre_collapse_fiber_nonempty :
    Nonempty PreCollapseAlphaStrongResidualDynamics
  pre_collapse_outputs_canonical :
    ∀ D : PreCollapseAlphaStrongResidualDynamics,
      ∀ x : D.Pre,
        D.collapse x = alphaStrongSU7BreakingResidualGapProducer
  pre_collapse_nontrivial_forces_noninjective_collapse :
    ∀ D : PreCollapseAlphaStrongResidualDynamics,
      ¬ Function.Injective D.collapse

/-- THEOREM 12: source-allocation and pre-collapse-fiber certificate for the
current finite `alpha_s` residual producer. -/
def alphaStrongSourceAllocationPreCollapseFiberCertificate :
    AlphaStrongSourceAllocationPreCollapseFiberCertificate where
  selected_source := alphaStrongSelectSU7Breaking
  selected_source_eq := rfl
  su7_selected_closes := by
    intro P hP
    exact alphaStrong_sourceSurface_selectedSU7Sum_eq_gap P hP
  omitted_non_su7_zero := by
    intro P hP
    exact alphaStrong_sourceSurface_omittedNonSU7Sum_eq_zero P hP
  threshold_zero := alphaStrong_sourceSurface_threshold_eq_zero
  three_loop_rg_zero := alphaStrong_sourceSurface_threeLoopRG_eq_zero
  higgs_extra_zero := alphaStrong_sourceSurface_higgsExtra_eq_zero
  pre_collapse_fiber_nonempty :=
    ⟨boolFiberAlphaStrongPreCollapseDynamics⟩
  pre_collapse_outputs_canonical := by
    intro D x
    exact D.collapse_eq_canonical x
  pre_collapse_nontrivial_forces_noninjective_collapse := by
    intro D
    exact D.collapse_not_injective_of_nontrivial_step

end StandardModelConstraint
end SaturationMonoid
