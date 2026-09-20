/-
  Proposition 503: information/matter projection equivalence.

  P459 proves that the `3+2+1+1` SU(7) block-incidence carrier has six
  canonical off-diagonal information incidences, and that the accepted
  Standard-Model schedule identifies those incidences with the five Weyl
  matter multiplets plus the Higgs doublet.

  P467/P468 prove that the dynamic content of the same carrier is a single
  zero-target residual/keep spine: apparent rate growth toward `1` is the
  complementary reading of keep/headroom relaxation toward `0`.

  This file bundles those two statements into the precise Lean-safe content of
  the slogan "information = matter": in the current formal carrier, matter
  slots are exactly information-incidence slots, and their scalar content law
  is the same zero-target residual law.

  Boundary: this is a carrier/projection theorem.  It does not prove that the
  physical world has this carrier, derive particle masses from first
  principles, or identify information with matter outside this formal
  Standard-Model projection interface.
-/

import H0mework.Physics.RepresentationSources.P459
import H0mework.Physics.SourceContracts.P468
import H0mework.Realization.RelaxationFlow.P502

namespace SaturationMonoid
namespace StandardModelConstraint
namespace InformationMatterProjection

open RunningSigmaBeta

/-! ## Slot-level information/matter equivalence -/

/-- The information side: off-diagonal incidences of the `3+2+1+1` carrier. -/
abbrev InformationSlot := SU7BlockIncidence

/-- The matter side: five Weyl matter multiplets plus the Higgs doublet. -/
abbrev MatterSlot := SU7GeneratedCarrierSlot

/-- The current carrier's information-to-matter projection. -/
def informationMatterEquiv : InformationSlot ≃ MatterSlot :=
  blockIncidenceGeneratedSlotEquiv

/-- THEOREM 1: every matter/Higgs slot has an information-incidence source. -/
theorem every_matter_slot_has_information_source
    (s : MatterSlot) :
    ∃ i : InformationSlot, informationMatterEquiv i = s :=
  ⟨informationMatterEquiv.symm s,
    Equiv.apply_symm_apply informationMatterEquiv s⟩

/-- THEOREM 2: every information incidence has a matter/Higgs projection. -/
theorem every_information_slot_has_matter_projection
    (i : InformationSlot) :
    ∃ s : MatterSlot, informationMatterEquiv i = s :=
  ⟨informationMatterEquiv i, rfl⟩

/-- THEOREM 3: projecting information to matter and back preserves the
information slot. -/
theorem information_matter_roundtrip_left
    (i : InformationSlot) :
    informationMatterEquiv.symm (informationMatterEquiv i) = i :=
  Equiv.symm_apply_apply informationMatterEquiv i

/-- THEOREM 4: projecting matter to information and back preserves the
matter slot. -/
theorem information_matter_roundtrip_right
    (s : MatterSlot) :
    informationMatterEquiv (informationMatterEquiv.symm s) = s :=
  Equiv.apply_symm_apply informationMatterEquiv s

/-- THEOREM 5: the two projections have the same finite cardinality. -/
theorem informationSlot_card_eq_matterSlot_card :
    Fintype.card InformationSlot = Fintype.card MatterSlot := by
  rw [SU7BlockIncidence.card, SU7GeneratedCarrierSlot.card]

/-! ## Representation trace and scalar-content laws -/

/-- THEOREM 6: the information-incidence trace input is exactly the matter
multiplet trace input. -/
theorem information_trace_input_eq_matter_trace_input
    (G : StandardModelGaugeFactor) :
    incidenceCarrierTraceInput G = multipletCarrierTraceInput G :=
  incidenceCarrierTraceInput_eq_multipletCarrierTraceInput G

/-- THEOREM 7: the same information/matter trace input forces the carrier
`b0` value. -/
theorem information_matter_trace_forces_carrierB0
    (G : StandardModelGaugeFactor) :
    betaCoeff (incidenceCarrierTraceInput G) = carrierB0 G :=
  betaCoeff_incidenceCarrierTraceInput_eq_carrierB0 G

/-- THEOREM 8: residual-power content is exactly zero-target relaxation
content.  This is the scalar content law shared by information and matter
coordinates in this carrier. -/
theorem residual_content_eq_zeroTarget_information_content
    {K : Type*} [Field K] (initial sigma : K) (n : Nat) :
    initial * ((1 - sigma) ^ n) =
      (fun x : K => AffineRelaxation.relaxModule (0 : K) sigma x)^[n]
        initial :=
  residual_power_eq_zeroTarget_relaxModule_iterate initial sigma n

/-- THEOREM 9: the rate-facing matter coordinate is the complement of the
zero-target information/keep coordinate, not a second target. -/
theorem rate_matter_coordinate_eq_information_keep_complement
    {K : Type*} [Field K] (h sigma : K) :
    (1 : K) - bumpSatField h sigma =
      AffineRelaxation.relaxModule (0 : K) sigma ((1 : K) - h) :=
  complement_bumpSatField_eq_zeroTarget_relaxModule_keep h sigma

/-- THEOREM 10: sampled rate trajectories are zero-target keep flows in the
complementary coordinate. -/
theorem sampled_rate_matter_eq_information_keep_flow
    (h lambda step : ℝ) (n : Nat) :
    (1 : ℝ) -
        (fun z : ℝ =>
          bumpSatField z (AffineRelaxation.realDecayRate lambda step))^[n] h =
      AffineRelaxation.realDecayRelaxFlow
        (0 : ℝ) lambda ((n : ℝ) * step) ((1 : ℝ) - h) :=
  complement_bumpSatField_iterate_realDecayRate_eq_zeroTarget_flow_keep
    h lambda step n

/-- THEOREM 11: subdividing a fixed total time preserves the same information
/ matter content.  Refinement does not create a new amount of matter/content;
it only samples the same continuous zero-target flow more finely. -/
theorem fixed_total_subdivision_preserves_information_matter_content
    (lambda T : ℝ) {n : Nat} (hn : 0 < n) :
    ((1 : ℝ) - AffineRelaxation.realDecayRate lambda (T / (n : ℝ))) ^ n =
      AffineRelaxation.realDecayResidual lambda T :=
  AffineRelaxation.residual_power_of_subdivided_realDecayRate_eq_total
    lambda T hn

/-! ## Bundled receipt -/

/-- A bundled receipt for the precise carrier theorem behind
"information = matter". -/
structure InformationMatterProjectionEquivalenceCertificate : Prop where
  slot_equiv :
    Nonempty (InformationSlot ≃ MatterSlot)
  matter_has_information_source :
    ∀ s : MatterSlot, ∃ i : InformationSlot, informationMatterEquiv i = s
  information_has_matter_projection :
    ∀ i : InformationSlot, ∃ s : MatterSlot, informationMatterEquiv i = s
  roundtrip_information :
    ∀ i : InformationSlot,
      informationMatterEquiv.symm (informationMatterEquiv i) = i
  roundtrip_matter :
    ∀ s : MatterSlot,
      informationMatterEquiv (informationMatterEquiv.symm s) = s
  same_cardinality :
    Fintype.card InformationSlot = Fintype.card MatterSlot
  trace_input :
    ∀ G : StandardModelGaugeFactor,
      incidenceCarrierTraceInput G = multipletCarrierTraceInput G
  b0_projection :
    ∀ G : StandardModelGaugeFactor,
      betaCoeff (incidenceCarrierTraceInput G) = carrierB0 G
  zero_target_content :
    ∀ {K : Type*} [Field K], ∀ initial sigma : K, ∀ n : Nat,
      initial * ((1 - sigma) ^ n) =
        (fun x : K => AffineRelaxation.relaxModule (0 : K) sigma x)^[n]
          initial
  rate_complement_content :
    ∀ {K : Type*} [Field K], ∀ h sigma : K,
      (1 : K) - bumpSatField h sigma =
        AffineRelaxation.relaxModule (0 : K) sigma ((1 : K) - h)
  sampled_content :
    ∀ h lambda step : ℝ, ∀ n : Nat,
      (1 : ℝ) -
          (fun z : ℝ =>
            bumpSatField z (AffineRelaxation.realDecayRate lambda step))^[n] h =
        AffineRelaxation.realDecayRelaxFlow
          (0 : ℝ) lambda ((n : ℝ) * step) ((1 : ℝ) - h)
  fixed_total_subdivision :
    ∀ lambda T : ℝ, ∀ n : Nat, 0 < n ->
      ((1 : ℝ) - AffineRelaxation.realDecayRate lambda (T / (n : ℝ))) ^ n =
        AffineRelaxation.realDecayResidual lambda T

/-- THEOREM 12: the current Standard-Model projection carrier supplies the
information/matter equivalence receipt. -/
theorem informationMatterProjectionEquivalenceCertificate :
    InformationMatterProjectionEquivalenceCertificate where
  slot_equiv := ⟨informationMatterEquiv⟩
  matter_has_information_source := every_matter_slot_has_information_source
  information_has_matter_projection :=
    every_information_slot_has_matter_projection
  roundtrip_information := information_matter_roundtrip_left
  roundtrip_matter := information_matter_roundtrip_right
  same_cardinality := informationSlot_card_eq_matterSlot_card
  trace_input := information_trace_input_eq_matter_trace_input
  b0_projection := information_matter_trace_forces_carrierB0
  zero_target_content :=
    residual_content_eq_zeroTarget_information_content
  rate_complement_content :=
    rate_matter_coordinate_eq_information_keep_complement
  sampled_content := sampled_rate_matter_eq_information_keep_flow
  fixed_total_subdivision := fun lambda T _n hn =>
    fixed_total_subdivision_preserves_information_matter_content lambda T hn

end InformationMatterProjection
end StandardModelConstraint
end SaturationMonoid
