import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ForcePeace.Contract.Policy
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ForcePeace.Counterplay.Timing.Deadline
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ForcePeace.Counterplay.Timing.Write

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ForcePeace

open Capitalism.Universal.Source.Program
open PublicFunction.Mandate Counterplay

noncomputable section

universe u v

variable {Party Good Port Technology Instrument Community : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Technology]
  [DecidableEq Instrument] [DecidableEq Community]
  {CivilView : Type u} {OpponentView : Type v}

variable (game : Game Party Good Port (State Party Technology) Instrument Community CivilView OpponentView)
  {base : RawLaw Party Good Port Technology Instrument}
  {scope : Scope (Party := Party) (Good := Good) (Port := Port)} {actor : Party}
  (plan : CivilPlan Party Good Port (State Party Technology) Instrument CivilView)
  {word : Reparation.Actual.Script Party Good Port (State Party Technology) Instrument}
  (receipt : EffectiveRelease base scope game.seed (submittedCut game) actor word)

/-- A paid revision occupies the first material slot. A failed exit at
the same cut precedes it, while a competing first material item ties. -/
def inspectPaidBoundary :
    { breach : game.JointBreach (constitutionalMove game) plan //
      (breach.clock : ℝ) < (receipt.clock : ℝ) ∨ (receipt.clock : ℝ) = (breach.clock : ℝ) ∧
        (breach.visit < receipt.ordinal ∨ breach.visit = receipt.ordinal ∧ breach.position < 1) } ⊕
      PLift (game.JointSafeBoundary (constitutionalMove game) plan (receipt.clock : ℝ) receipt.ordinal 1) := by
  classical
  by_cases safe : game.JointSafeBoundary (constitutionalMove game) plan (receipt.clock : ℝ) receipt.ordinal 1
  · exact .inr ⟨safe⟩
  · have found := (game.unsafe_joint_boundary_has_an_earlier_actual_breach (constitutionalMove game) plan
      (receipt.clock : ℝ) receipt.ordinal 1).mp safe
    exact .inl ⟨Classical.choose found, Classical.choose_spec found⟩

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ForcePeace
