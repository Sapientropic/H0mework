import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Runtime.Activation.Layouts
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Ingress.Continuation

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Runtime

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument) (depth sourceStart : Nat)
  (datum : Ingress.Datum input depth sourceStart) (prefixLimit renewalLimit : Nat)
  (reader : Raw.Reader input depth (Ingress.cut input depth sourceStart))
  (review : Option (ReviewPhase.ContextAt input) := none)

private theorem before_transitive {first middle last : Nat × (Nat × Nat)}
    (earlier : Before first middle) (later : Before middle last) : Before first last := by
  unfold Before Financial.Installation.Runtime.Before at *
  omega

private theorem before_irreflexive (value : Nat × (Nat × Nat)) : ¬ Before value value := by
  unfold Before Financial.Installation.Runtime.Before
  omega

theorem activated_frames_forward (first distance : Nat) :
    Before (activatedFrames (review := review) input depth sourceStart datum prefixLimit renewalLimit reader first).rank
      (activatedFrames (review := review) input depth sourceStart datum prefixLimit renewalLimit reader (first + distance + 1)).rank := by
  induction distance with
  | zero => exact (activatedFrames (review := review) input depth sourceStart datum prefixLimit renewalLimit reader first).next_progress
  | succ distance prior =>
      exact before_transitive prior
        (activatedFrames (review := review) input depth sourceStart datum prefixLimit renewalLimit reader (first + distance + 1)).next_progress

theorem activated_frames_erase_injective : Function.Injective
    (fun tick => (activatedFrames (review := review) input depth sourceStart datum prefixLimit renewalLimit reader tick).presentation.erase) := by
  intro left right same
  have equalRanks := ActivatedFrame.rank_eq_of_erasure _ _
    (activatedLayouts (review := review) input depth sourceStart datum prefixLimit renewalLimit reader left)
    (activatedLayouts (review := review) input depth sourceStart datum prefixLimit renewalLimit reader right) same
  rcases lt_trichotomy left right with earlier | equal | later
  · obtain ⟨distance, following⟩ := Nat.exists_eq_add_of_lt earlier
    have strict := activated_frames_forward (review := review) input depth sourceStart datum prefixLimit renewalLimit reader left distance
    rw [← following, equalRanks] at strict
    exact (before_irreflexive _ strict).elim
  · exact equal
  · obtain ⟨distance, following⟩ := Nat.exists_eq_add_of_lt later
    have strict := activated_frames_forward (review := review) input depth sourceStart datum prefixLimit renewalLimit reader right distance
    rw [← following, equalRanks] at strict
    exact (before_irreflexive _ strict).elim

private theorem projection_mod
    (current : ActivatedFrame (review := review) input depth (Ingress.cut input depth sourceStart)
      prefixLimit renewalLimit depth (Ingress.cut input depth sourceStart))
    (layout : current.Layout) :
    erasedProjectionCard current.presentation.erase % 4 = 0 ∨
      erasedProjectionCard current.presentation.erase % 4 = 2 ∨ erasedProjectionCard current.presentation.erase % 4 = 3 := by
  cases current with
  | original frame =>
      have card := layout.card
      change erasedProjectionCard (ActivatedFrame.original frame).presentation.erase = _ at card
      split_ifs at card <;> omega
  | enacted origin admission frame =>
      have card := layout.card
      change erasedProjectionCard (ActivatedFrame.enacted origin admission frame).presentation.erase = _ at card
      omega

theorem activated_frames_projection_mod (tick : Nat) :
    let size := erasedProjectionCard (activatedFrames (review := review) input depth sourceStart datum prefixLimit renewalLimit reader tick).presentation.erase % 4
    size = 0 ∨ size = 2 ∨ size = 3 :=
  projection_mod (input := input) (depth := depth) (sourceStart := sourceStart)
    (prefixLimit := prefixLimit) (renewalLimit := renewalLimit) (review := review)
    (activatedFrames (review := review) input depth sourceStart datum prefixLimit renewalLimit reader tick)
    (activatedLayouts (review := review) input depth sourceStart datum prefixLimit renewalLimit reader tick)

#print axioms activated_frames_erase_injective

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Runtime
