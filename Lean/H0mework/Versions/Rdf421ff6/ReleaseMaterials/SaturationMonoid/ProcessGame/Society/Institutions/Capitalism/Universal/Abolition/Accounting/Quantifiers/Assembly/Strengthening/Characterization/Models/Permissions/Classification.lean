import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Characterization.Models.Permissions.Positive

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Characterization.Models.Permissions

open Source.Program Source.ProgrammeControl Source.ProgrammeControl.Kernel
noncomputable section

theorem either_single_blocking_atom_excludes_every_private_phase
    (ownerGranted recipientGranted : Bool) (blocked : ownerGranted = false ∨ recipientGranted = true)
    (current : RawCurrent Bool Unit Unit Unit) (port recipient : Bool) :
    ¬ PrivatePhase (law ownerGranted recipientGranted) current port recipient := by
  intro phase
  rcases blocked with rfl | rfl
  · cases recipientGranted <;> cases port <;> cases recipient <;>
      simp [PrivatePhase,law,Kernel.Consumers.StoredAccess.law] at phase
  · cases ownerGranted <;> cases port <;> cases recipient <;>
      simp [PrivatePhase,law,Kernel.Consumers.StoredAccess.law] at phase

theorem either_single_blocking_atom_excludes_every_capital_kernel
    (ownerGranted recipientGranted : Bool) (blocked : ownerGranted = false ∨ recipientGranted = true)
    (current : RawCurrent Bool Unit Unit Unit) (word : RawEvent Bool Unit Bool Unit Unit) :
    ¬ Nonempty (CapitalRelationKernel (law ownerGranted recipientGranted) current word) := by
  rintro ⟨capital⟩
  exact either_single_blocking_atom_excludes_every_private_phase ownerGranted recipientGranted blocked
    capital.proposal.access.access.val.before capital.proposal.access.port capital.proposal.access.recipient
    capital.checked.1.2.2.1

/-- The source has actual controlled access, need, return and disposal.
Inside this family, both permission atoms are necessary and sufficient. -/
theorem capital_regeneration_is_exactly_the_two_actual_permission_atoms
    (ownerGranted recipientGranted : Bool) (clock : ℚ) (round : Nat) :
    Nonempty (CapitalRelationKernel (law ownerGranted recipientGranted) (state clock round) body) ↔
      ownerGranted = true ∧ recipientGranted = false := by
  constructor
  · intro capital
    cases ownerGranted with
    | false =>
        exfalso
        exact either_single_blocking_atom_excludes_every_capital_kernel false recipientGranted (Or.inl rfl) _ _ capital
    | true =>
        cases recipientGranted with
        | false => exact ⟨rfl,rfl⟩
        | true =>
            exfalso
            exact either_single_blocking_atom_excludes_every_capital_kernel true true (Or.inr rfl) _ _ capital
  · rintro ⟨rfl,rfl⟩
    exact ⟨generated clock round⟩

theorem restoring_access_does_not_change_the_original_actual_execution :
    (law true true).rawItems (state 0 0) body = (law true false).rawItems (state 0 0) body ∧
      (law true true).next (state 0 0) body = (law true false).next (state 0 0) body := by
  constructor
  · simp [law,body,Kernel.Consumers.StoredAccess.law,Kernel.Consumers.StoredAccess.body,
      Kernel.Consumers.StoredAccess.current,state,RawLaw.rawItems,RawLaw.execute,
      RawLaw.step,RawLaw.Valid,RawLaw.SignerMatches,RawLaw.operationAllowed,
      RawLaw.ClaimGuard,RawLaw.debit,RawLaw.credit,RawLaw.requiredPorts,
      RawLaw.paidStep,RawLaw.nextClaims,flowAt,locate,amount,NonnegativeBundle,RawPolicy.eval]
  · apply RawCurrent.ext
    · funext actor good; cases actor <;> cases good <;> decide +kernel
    · funext instrument actor holder; cases instrument; cases actor <;> cases holder <;> decide +kernel
    · rfl
    · decide +kernel
    · decide +kernel

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Characterization.Models.Permissions
