import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Exit.Redemption.Admission
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Structural.Consumers.Canonical.UBI

set_option autoImplicit false
set_option maxRecDepth 4096

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Exit.Redemption.Consumers

open Source.Program PublicFunction.Repayment
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Instances.UBI (law)

noncomputable section

abbrev originalInput := Structural.Consumers.Canonical.UBI.input
abbrev originalVisit := Structural.Consumers.Canonical.UBI.visit

def position : Position Bool Unit := ⟨(), false, true⟩

def originalNeedCut := ProgrammeSource.rawCurrent originalInput originalVisit.current

def redemptionCut :=
  (law.execute originalNeedCut 0 (List.take 2 (ProgrammeSource.rawEvent originalInput originalVisit.current))).final

theorem the_measured_leg_is_the_original_ubi_root_instruction :
    (law.rawItems (ProgrammeSource.rawCurrent originalInput originalVisit.current)
      (ProgrammeSource.rawEvent originalInput originalVisit.current))[2]? =
      some ⟨2, redemptionCut, request law position 1⟩ := rfl

private theorem original_safe : Safe law originalNeedCut redemptionCut position 1 := by
  apply (safe_iff_original_authority_and_tight_material_interval law originalNeedCut redemptionCut position 1).mpr
  unfold Within Authorized
  decide +kernel

theorem the_actual_ubi_leg_attains_the_source_bounds :
    lower law originalNeedCut redemptionCut position = 1 ∧ upper law originalNeedCut redemptionCut position = 1 ∧
    Safe law originalNeedCut redemptionCut position 1 ∧
    ∀ quantity, Safe law originalNeedCut redemptionCut position quantity → quantity = 1 := by
  have lo : lower law originalNeedCut redemptionCut position = 1 := by decide +kernel
  have hi : upper law originalNeedCut redemptionCut position = 1 := by decide +kernel
  refine ⟨lo, hi, original_safe, ?_⟩
  intro quantity accepted
  obtain ⟨_, _, within, _⟩ :=
    (safe_iff_original_authority_and_tight_material_interval law originalNeedCut redemptionCut position quantity).mp accepted
  exact le_antisymm (within.2.trans_eq hi) (lo.symm.trans_le within.1)

theorem a_smaller_redeemed_payment_is_real_but_cannot_cover_living :
    law.Valid redemptionCut (request law position (1 / 2)) ∧
      ¬ Safe law originalNeedCut redemptionCut position (1 / 2) := by
  refine ⟨by decide +kernel, ?_⟩
  intro safe
  have wrong := the_actual_ubi_leg_attains_the_source_bounds.2.2.2 _ safe
  norm_num at wrong

end

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Exit.Redemption.Consumers
