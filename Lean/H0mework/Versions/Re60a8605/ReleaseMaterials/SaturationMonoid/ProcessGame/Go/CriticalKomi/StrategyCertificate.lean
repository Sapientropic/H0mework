import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Go.CriticalKomi.TwoEyeFamily
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Go.CriticalKomi.EyeCoalitionRecognize
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Go.CriticalKomi.VitalChambers

/-!
Finite solved native ports compile to a Boolean survival relation.  The
open-play leaves are source living-area witnesses; all other nodes retain exact
frames and original legal successors.  This is a consumer of generated solved
data, not an evaluator or an installation of a future value function.
-/

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Go.CriticalKomi

theorem acceptsMargin_trans (side : Polarity) (threshold middle margin : Int)
    (relaxed : acceptsMargin side threshold middle = true)
    (accepted : acceptsMargin side middle margin = true) :
    acceptsMargin side threshold margin = true := by
  cases side <;> simp only [acceptsMargin, decide_eq_true_eq] at *
  · exact Int.le_trans relaxed accepted
  · exact Int.le_trans accepted relaxed

theorem forcingRead_threshold_mono {n : Nat} (side : Polarity)
    (threshold middle : Int) (relaxed : acceptsMargin side threshold middle = true)
    (frame : Frame n) (post : Frame n → Bool)
    (accepted : forcingRead side middle frame post = true) :
    forcingRead side threshold frame post = true := by
  cases status : frame.visible.status with
  | playing => simpa only [forcingRead, status] using accepted
  | terminal reason =>
      simp only [forcingRead, status, terminalGood, Bool.and_eq_true] at accepted ⊢
      exact ⟨accepted.1, acceptsMargin_trans side threshold middle _ relaxed accepted.2⟩

theorem forcingRead_post_mono {n : Nat} (side : Polarity) (threshold : Int)
    (frame : Frame n) (small large : Frame n → Bool)
    (included : ∀ target, small target = true → large target = true)
    (accepted : forcingRead side threshold frame small = true) :
    forcingRead side threshold frame large = true := by
  cases status : frame.visible.status with
  | terminal reason => simpa only [forcingRead, status] using accepted
  | playing =>
      simp only [forcingRead, status] at accepted ⊢
      by_cases owned : frame.visible.toMove = side
      · obtain ⟨move, target, step, scoring, good⟩ :=
          (preimage_own side frame small owned).mp accepted
        exact (preimage_own side frame large owned).mpr
          ⟨move, target, step, scoring, included target good⟩
      · apply (preimage_opponent side frame large owned).mpr
        intro move target step scoring
        exact included target ((preimage_opponent side frame small owned).mp
          accepted move target step scoring)

/-- Solved local data; the universal constructor is indexed by the original
scoring enumerator, so no caller-supplied coverage assertion is needed. -/
inductive Certificate {n : Nat} (side : Polarity) (threshold : Int) : Frame n → Type
  | terminal {frame : Frame n}
      (finished : frame.visible.status = .terminal .twoPasses)
      (accepted : acceptsMargin side threshold (areaMargin frame.visible.board) = true) :
      Certificate side threshold frame
  | twoEye {frame : Frame n} (detected : TwoEye.Detected frame.visible.board side)
      (scoring : ScoringStatus frame)
      (relaxed : acceptsMargin side threshold (TwoEye.bound detected.geometry side) = true) :
      Certificate side threshold frame
  | twoEyeFamily {frame : Frame n} (detected : TwoEyeFamily.Detected frame.visible.board side)
      (scoring : ScoringStatus frame)
      (relaxed : acceptsMargin side threshold detected.bound = true) :
      Certificate side threshold frame
  | eyeCoalition {frame : Frame n} (detected : EyeCoalition.Detected frame.visible.board side)
      (scoring : ScoringStatus frame)
      (relaxed : acceptsMargin side threshold (EyeCoalition.bound detected.geometry side) = true) :
      Certificate side threshold frame
  | choose {frame : Frame n} (owned : frame.visible.toMove = side)
      (reply : ScoringReply frame) (child : Certificate side threshold reply.target) :
      Certificate side threshold frame
  | all {frame : Frame n} (playing : frame.visible.status = .playing)
      (opponent : frame.visible.toMove ≠ side)
      (children : (port : Fin (scoringExpansion frame).length) →
        Certificate side threshold ((scoringExpansion frame).get port).2) :
      Certificate side threshold frame
  | vitalChambers {frame : Frame n} (detected : VitalChambers.Detected frame.visible.board side)
      (scoring : ScoringStatus frame)
      (relaxed : acceptsMargin side threshold (VitalChambers.bound detected.geometry side) = true) :
      Certificate side threshold frame

namespace Certificate

/-- Membership is executable and contains every solved descendant and every
retained two-eye closure, preserving full history at the finite explicit nodes. -/
def invariant {n : Nat} {side : Polarity} {threshold : Int} {frame : Frame n}
    (certificate : Certificate side threshold frame) (target : Frame n) : Bool :=
  match certificate with
  | .terminal _ _ => decide (target = frame)
  | .twoEye detected _ _ => TwoEye.invariant detected.geometry side target
  | .twoEyeFamily detected _ _ => TwoEyeFamily.invariant detected.family side target
  | .eyeCoalition detected _ _ => EyeCoalition.invariant detected.geometry side target
  | .vitalChambers detected _ _ => VitalChambers.invariant detected.geometry side target
  | .choose _ _ child => decide (target = frame) || child.invariant target
  | .all _ _ children => decide (target = frame) ||
      (List.finRange (scoringExpansion frame).length).any
        (fun port => (children port).invariant target)

theorem root_inside {n : Nat} {side : Polarity} {threshold : Int} {frame : Frame n}
    (certificate : Certificate side threshold frame) : certificate.invariant frame = true := by
  cases certificate with
  | terminal finished accepted => simp [invariant]
  | twoEye detected scoring relaxed =>
      exact (TwoEye.invariant_iff detected.geometry side frame).mpr ⟨scoring, detected.holds⟩
  | twoEyeFamily detected scoring relaxed =>
      exact (TwoEyeFamily.invariant_iff detected.family side frame).mpr ⟨scoring, detected.holds⟩
  | eyeCoalition detected scoring relaxed =>
      exact (EyeCoalition.invariant_iff detected.geometry side frame).mpr ⟨scoring, detected.holds⟩
  | vitalChambers detected scoring relaxed =>
      exact (VitalChambers.invariant_iff detected.geometry side frame).mpr ⟨scoring, detected.holds⟩
  | choose owned reply child => simp [invariant]
  | all playing opponent children => simp [invariant]

theorem closed {n : Nat} {side : Polarity} {threshold : Int} {frame : Frame n}
    (certificate : Certificate side threshold frame) :
    ClosedUnderNativeForcing side threshold certificate.invariant := by
  induction certificate with
  | @terminal root finished accepted =>
      intro current inside
      have same : current = root := of_decide_eq_true inside
      subst current
      simpa only [forcingRead, finished, terminalGood, beq_self_eq_true, Bool.true_and]
        using accepted
  | @twoEye root detected scoring relaxed =>
      intro current inside
      exact forcingRead_threshold_mono side threshold _ relaxed current _
        (TwoEye.closed detected.geometry side current inside)
  | @twoEyeFamily root detected scoring relaxed =>
      intro current inside
      exact forcingRead_threshold_mono side threshold _ relaxed current _
        (TwoEyeFamily.closed detected.family side current inside)
  | @eyeCoalition root detected scoring relaxed =>
      intro current inside
      exact forcingRead_threshold_mono side threshold _ relaxed current _
        (EyeCoalition.closed detected.geometry side current inside)
  | @vitalChambers root detected scoring relaxed =>
      intro current inside
      exact forcingRead_threshold_mono side threshold _ relaxed current _
        (VitalChambers.closed detected.geometry side current inside)
  | @choose root owned reply child ih =>
      intro current inside
      have cases := Bool.or_eq_true_iff.mp inside
      rcases cases with atRoot | inChild
      · have same : current = root := of_decide_eq_true atRoot
        subst current
        have playing := nonresigning_step_playing reply.notResign reply.step
        simp only [forcingRead, playing]
        apply (preimage_own side root _ owned).mpr
        refine ⟨reply.move, reply.target, reply.step, reply.notResign, ?_⟩
        simp only [invariant, child.root_inside, Bool.or_true]
      · exact forcingRead_post_mono side threshold current child.invariant _
          (fun target good => by simp only [invariant, good, Bool.or_true]) (ih current inChild)
  | @all root playing opponent children ih =>
      intro current inside
      have cases := Bool.or_eq_true_iff.mp inside
      rcases cases with atRoot | inChildren
      · have same : current = root := of_decide_eq_true atRoot
        subst current
        simp only [forcingRead, playing]
        apply (preimage_opponent side root _ opponent).mpr
        intro move target step scoring
        have member := mem_scoringExpansion_iff.mpr ⟨step, scoring⟩
        obtain ⟨index, bounded, same⟩ := List.getElem_of_mem member
        let port : Fin (scoringExpansion root).length := ⟨index, bounded⟩
        have childInside : (children port).invariant target = true := by
          have childRoot := (children port).root_inside
          simpa only [List.get_eq_getElem, port, same] using childRoot
        apply Bool.or_eq_true_iff.mpr
        exact Or.inr (List.any_eq_true.mpr ⟨port, List.mem_finRange port, childInside⟩)
      · obtain ⟨port, _, inChild⟩ := List.any_eq_true.mp inChildren
        exact forcingRead_post_mono side threshold current (children port).invariant _
          (fun target good => Bool.or_eq_true_iff.mpr (Or.inr
            (List.any_eq_true.mpr ⟨port, List.mem_finRange port, good⟩)))
          (ih port current inChild)

/-- The existing native compiler computes each own move from the retained
relation and the current legal expansion. -/
def closure {n : Nat} {side : Polarity} {threshold : Int} {frame : Frame n}
    (certificate : Certificate side threshold frame) :=
  compileSurvival side threshold certificate.invariant certificate.closed

def policy {n : Nat} {side : Polarity} {threshold : Int} {frame : Frame n}
    (certificate : Certificate side threshold frame) : ExecutablePolicy n :=
  certificate.closure.policy

theorem guarantee {n : Nat} {side : Polarity} {threshold : Int} {frame : Frame n}
    (certificate : Certificate side threshold frame) (scoring : ScoringStatus frame)
    (opponent : ExecutablePolicy n) :
    acceptsMargin side threshold
      (areaMargin (executePolicies (versus side certificate.policy opponent)
        frame scoring).replay.final.visible.board) = true :=
  certificate.closure.against_every_policy certificate.root_inside scoring opponent

/-- The retained computation key forgets exactly the history detail already
proved irrelevant by `forcing_face_congr`; actual moves still use the full frame. -/
def faceInvariant {n : Nat} {side : Polarity} {threshold : Int} {frame : Frame n}
    (certificate : Certificate side threshold frame) (state : PositionFace.State n) : Bool :=
  match certificate with
  | .terminal _ _ => decide (state = PositionFace.read frame)
  | .twoEye detected _ _ =>
      (state.visible.status == .playing || state.visible.status == .terminal .twoPasses) &&
        decide (TwoEye.Holds detected.geometry side state.visible.board)
  | .twoEyeFamily detected _ _ =>
      (state.visible.status == .playing || state.visible.status == .terminal .twoPasses) &&
        decide (TwoEyeFamily.Holds detected.family side state.visible.board)
  | .eyeCoalition detected _ _ =>
      (state.visible.status == .playing || state.visible.status == .terminal .twoPasses) &&
        decide (EyeCoalition.Holds detected.geometry side state.visible.board)
  | .vitalChambers detected _ _ =>
      (state.visible.status == .playing || state.visible.status == .terminal .twoPasses) &&
        decide (VitalChambers.Holds detected.geometry side state.visible.board)
  | .choose _ _ child => decide (state = PositionFace.read frame) || child.faceInvariant state
  | .all _ _ children => decide (state = PositionFace.read frame) ||
      (List.finRange (scoringExpansion frame).length).any
        (fun port => (children port).faceInvariant state)

theorem faceRoot_inside {n : Nat} {side : Polarity} {threshold : Int} {frame : Frame n}
    (certificate : Certificate side threshold frame) :
    certificate.faceInvariant (PositionFace.read frame) = true := by
  cases certificate with
  | terminal finished accepted => simp [faceInvariant]
  | twoEye detected scoring relaxed =>
      exact (TwoEye.invariant_iff detected.geometry side frame).mpr ⟨scoring, detected.holds⟩
  | twoEyeFamily detected scoring relaxed =>
      exact (TwoEyeFamily.invariant_iff detected.family side frame).mpr ⟨scoring, detected.holds⟩
  | eyeCoalition detected scoring relaxed =>
      exact (EyeCoalition.invariant_iff detected.geometry side frame).mpr ⟨scoring, detected.holds⟩
  | vitalChambers detected scoring relaxed =>
      exact (VitalChambers.invariant_iff detected.geometry side frame).mpr ⟨scoring, detected.holds⟩
  | choose owned reply child => simp [faceInvariant]
  | all playing opponent children => simp [faceInvariant]

theorem faceClosed {n : Nat} {side : Polarity} {threshold : Int} {frame : Frame n}
    (certificate : Certificate side threshold frame) :
    ClosedUnderNativeForcing side threshold
      (certificate.faceInvariant ∘ PositionFace.read) := by
  induction certificate with
  | @terminal root finished accepted =>
      intro current inside
      have same : PositionFace.read current = PositionFace.read root := of_decide_eq_true inside
      rw [forcing_face_congr side threshold current root same]
      simpa only [forcingRead, finished, terminalGood, beq_self_eq_true, Bool.true_and]
        using accepted
  | @twoEye root detected scoring relaxed =>
      intro current inside
      exact forcingRead_threshold_mono side threshold _ relaxed current _
        (TwoEye.closed detected.geometry side current inside)
  | @twoEyeFamily root detected scoring relaxed =>
      intro current inside
      exact forcingRead_threshold_mono side threshold _ relaxed current _
        (TwoEyeFamily.closed detected.family side current inside)
  | @eyeCoalition root detected scoring relaxed =>
      intro current inside
      exact forcingRead_threshold_mono side threshold _ relaxed current _
        (EyeCoalition.closed detected.geometry side current inside)
  | @vitalChambers root detected scoring relaxed =>
      intro current inside
      exact forcingRead_threshold_mono side threshold _ relaxed current _
        (VitalChambers.closed detected.geometry side current inside)
  | @choose root owned reply child ih =>
      intro current inside
      have cases := Bool.or_eq_true_iff.mp inside
      rcases cases with atRoot | inChild
      · have same : PositionFace.read current = PositionFace.read root := of_decide_eq_true atRoot
        rw [forcing_face_congr side threshold current root same]
        have playing := nonresigning_step_playing reply.notResign reply.step
        simp only [forcingRead, playing]
        apply (preimage_own side root _ owned).mpr
        refine ⟨reply.move, reply.target, reply.step, reply.notResign, ?_⟩
        simp only [Function.comp_apply, faceInvariant, child.faceRoot_inside, Bool.or_true]
      · exact forcingRead_post_mono side threshold current
          (child.faceInvariant ∘ PositionFace.read) _
          (fun target good => by
            simp only [Function.comp_apply, faceInvariant] at good ⊢
            simp only [good, Bool.or_true])
          (ih current inChild)
  | @all root playing opponent children ih =>
      intro current inside
      have cases := Bool.or_eq_true_iff.mp inside
      rcases cases with atRoot | inChildren
      · have same : PositionFace.read current = PositionFace.read root := of_decide_eq_true atRoot
        rw [forcing_face_congr side threshold current root same]
        simp only [forcingRead, playing]
        apply (preimage_opponent side root _ opponent).mpr
        intro move target step scoring
        have member := mem_scoringExpansion_iff.mpr ⟨step, scoring⟩
        obtain ⟨index, bounded, same⟩ := List.getElem_of_mem member
        let port : Fin (scoringExpansion root).length := ⟨index, bounded⟩
        have childInside : (children port).faceInvariant (PositionFace.read target) = true := by
          have childRoot := (children port).faceRoot_inside
          simpa only [List.get_eq_getElem, port, same] using childRoot
        apply Bool.or_eq_true_iff.mpr
        exact Or.inr (List.any_eq_true.mpr ⟨port, List.mem_finRange port, childInside⟩)
      · obtain ⟨port, _, inChild⟩ := List.any_eq_true.mp inChildren
        exact forcingRead_post_mono side threshold current
          ((children port).faceInvariant ∘ PositionFace.read) _
          (fun target good => Bool.or_eq_true_iff.mpr (Or.inr
            (List.any_eq_true.mpr ⟨port, List.mem_finRange port, good⟩)))
          (ih port current inChild)

def faceClosure {n : Nat} {side : Polarity} {threshold : Int} {frame : Frame n}
    (certificate : Certificate side threshold frame) :=
  compileFaceSurvival side threshold certificate.faceInvariant certificate.faceClosed

def facePolicy {n : Nat} {side : Polarity} {threshold : Int} {frame : Frame n}
    (certificate : Certificate side threshold frame) : ExecutablePolicy n :=
  certificate.faceClosure.policy

/-- One solved certificate serves every native frame with the same positional
face; the generated policy responds to each actual opponent move at that frame. -/
theorem faceGuarantee {n : Nat} {side : Polarity} {threshold : Int} {frame : Frame n}
    (certificate : Certificate side threshold frame) (current : Frame n)
    (same : PositionFace.read current = PositionFace.read frame)
    (scoring : ScoringStatus current) (opponent : ExecutablePolicy n) :
    acceptsMargin side threshold
      (areaMargin (executePolicies (versus side certificate.facePolicy opponent)
        current scoring).replay.final.visible.board) = true := by
  apply certificate.faceClosure.against_every_policy _ scoring opponent
  simpa only [Function.comp_apply, same] using certificate.faceRoot_inside

end Certificate

end SaturationMonoid.ProcessGame.Go.CriticalKomi
