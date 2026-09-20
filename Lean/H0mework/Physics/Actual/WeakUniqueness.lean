import H0mework.Physics.Actual.WeakCandidate

/-! The source's eventual native law fixes every original weak occurrence.
Faithful compact reads recover the complete smooth configuration. -/

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage9CU.Weak

open StageNineHolonomicField

noncomputable section

theorem candidate_value_eq_firstWrite (candidate : Candidate) :
    candidate.val = sequence 7 := by
  obtain ⟨occurrence, same⟩ := candidate.property
  exact same.symm.trans
    (WeakCluster.limit_eq_of_eventuallyConstant sequence_eventually_firstWrite occurrence)

theorem candidate_eq_canonical (candidate : Candidate) : candidate = canonical :=
  Subtype.ext (candidate_value_eq_firstWrite candidate)

theorem pairwise_eq (left right : Candidate) : left = right :=
  (candidate_eq_canonical left).trans (candidate_eq_canonical right).symm

theorem pairwise_distanceSquared_zero (left right : Candidate) :
    dist (density left) (density right) ^ 2 = 0 := by
  rw [pairwise_eq left right]
  simp

theorem existsUnique_candidate : ∃! _candidate : Candidate, True :=
  ⟨canonical, trivial, fun candidate _ ↦ candidate_eq_canonical candidate⟩

theorem configuration_eq_firstWrite_of_candidate
    {configuration : StageNineHolonomicConfiguration} (smooth : configuration.Smooth)
    (admitted : ∃ candidate : Candidate,
      density candidate = Fields.compactCoordinates configuration smooth) :
    configuration = History.configuration 7 := by
  obtain ⟨candidate, same⟩ := admitted
  apply Fields.configuration_eq_of_compactCoordinates_eq smooth (History.configuration_smooth 7)
  exact same.symm.trans (candidate_value_eq_firstWrite candidate)

end
end SaturationMonoid.PhysicsCore.Stage9CU.Weak
