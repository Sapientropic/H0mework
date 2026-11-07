import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Joint.Boundary.Finite

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Joint.Boundary

open Source.Program Innovation

noncomputable section

attribute [local irreducible] actualLaw budget

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  {mechanism : Trials.Mechanism Party Good Port Technology Instrument}
  {past : List (RawEvent Party Good Port Technology Instrument)} {nature : mechanism.Nature}
  {response : Control.HistoryResponse (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)}
  (seed : Global.Seed (mechanism := mechanism) (past := past) (nature := nature) (response := response))
  (claim : Entitlement.Source.Claim (window seed)) (current : Current seed claim)
  (proposal : RawEvent Party Good Port Technology Instrument)

theorem actual_permit_facts_force_the_source_admitted_branch (permit : Permit seed claim current proposal) :
    Admitted seed claim current proposal := by
  unfold Admitted verdict
  rw [dif_pos permit.productiveDeclared,dif_pos permit.grossDeclared]
  cases seen : inspection seed claim current proposal with
  | blocked request rest original denied =>
      have equation : proposal = executed seed claim current proposal ++ request :: rest := original
      have lengths := congrArg List.length equation
      rw [permit.noStop] at lengths
      simp only [List.length_append,List.length_cons] at lengths
      omega
  | complete whole =>
      cases needs : Responsibility.Family.inspectNeeds (actualLaw seed) current.raw
          (executed seed claim current proposal) seed.current.members with
      | necessity actor original unpaid => exact False.elim (unpaid (permit.needs actor original).1)
      | maintenance actor original unpaid => exact False.elim (unpaid (permit.needs actor original).2)
      | paid complete =>
          dsimp only
          rw [dif_pos permit.strictProgress]
          trivial

def unpaid_actual_residual_without_strict_progress_returns_refusal
    (issue : ResidualAt seed claim (next seed claim current proposal))
    (noProgress : ¬ budget seed claim (next seed claim current proposal) < budget seed claim current) :
    RefusalAt seed claim current proposal (verdict seed claim current proposal) := by
  cases decision : verdict seed claim current proposal with
  | admitted permit => exact False.elim (noProgress permit.strictProgress)
  | settled paid needs p g noStop =>
      cases issue with
      | productive key original positive => exact False.elim ((ne_of_gt positive) (paid.1 key original))
      | gross key original positive => exact False.elim ((ne_of_gt positive) (paid.2 key original))
  | gate issue => exact .gate issue
  | needs issue => exact .needs issue
  | residual issue noProgress => exact .residual issue noProgress

theorem actual_refusal_excludes_a_joint_old_row_permit
    (refusal : RefusalAt seed claim current proposal (verdict seed claim current proposal)) :
    ¬ Permit seed claim current proposal := by
  intro permit
  exact refusal_cannot_mint_the_requested_renewal_authority seed claim current proposal refusal
    (actual_permit_facts_force_the_source_admitted_branch seed claim current proposal permit)

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Joint.Boundary
