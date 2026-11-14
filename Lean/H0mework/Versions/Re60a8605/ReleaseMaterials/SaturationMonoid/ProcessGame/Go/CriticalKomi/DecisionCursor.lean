import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Go.CriticalKomi.SourceLeaf
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Go.CriticalKomi.BufferedReplay

/-!
An executable native threshold calculation.  Its continuation stores already
solved ports and the exact unprocessed suffix.  A successful mover reply closes
immediately; an opponent guarantee is assembled only after all original legal
ports have returned.  Observation fuel never creates an answer.
-/

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Go.CriticalKomi.DecisionCursor

private def meet (side : Polarity) (left right : Int) : Int :=
  match side with | .positive => min left right | .negative => max left right

private theorem meet_left (side : Polarity) (left right : Int) :
    acceptsMargin side (meet side left right) left = true := by
  cases side <;> simp [meet, acceptsMargin]

private theorem meet_right (side : Polarity) (left right : Int) :
    acceptsMargin side (meet side left right) right = true := by
  cases side <;> simp [meet, acceptsMargin]

private theorem meet_accepted (side : Polarity) (threshold left right : Int)
    (leftAccepted : acceptsMargin side threshold left = true)
    (rightAccepted : acceptsMargin side threshold right = true) :
    acceptsMargin side threshold (meet side left right) = true := by
  cases side <;> simp_all [meet, acceptsMargin]

/-- Already solved original ports retain their actual common guarantee. The
bound is accumulated when a child arrives; child trees are not folded again. -/
structure Certificates {n : Nat} (side : Polarity) (threshold : Int)
    (children : List (Move n × Frame n)) where
  value : Int
  accepted : acceptsMargin side threshold value = true
  childAt : (port : Fin children.length) → Certificate side value (children.get port).2

def Certificates.nil {n : Nat} {side : Polarity} {threshold : Int} :
    Certificates (n := n) side threshold [] :=
  ⟨threshold, by cases side <;> simp [acceptsMargin], fun port => Fin.elim0 port⟩

def Certificates.get {n : Nat} {side : Polarity} {threshold : Int}
    {children : List (Move n × Frame n)} (done : Certificates side threshold children)
    (port : Fin children.length) : Certificate side threshold (children.get port).2 :=
  (SourceCertificate.mk done.value (done.childAt port) done.accepted).atThreshold

/-- Append in the original enumeration order. Weakenings remain inside the
dependent reader; accumulating another integer never traverses a child all. -/
def Certificates.snocSource {n : Nat} {side : Polarity} {threshold : Int}
    {children : List (Move n × Frame n)} (done : Certificates side threshold children)
    (child : Move n × Frame n) (produced : SourceCertificate side threshold child.2) :
    Certificates side threshold (children ++ [child]) :=
  if first : children = [] then by
    subst children
    refine ⟨produced.value, produced.accepted, ?_⟩
    intro port
    have index : port.val = 0 := by
      have bounded := port.isLt
      change port.val < 1 at bounded
      omega
    simpa [List.get_eq_getElem, index] using produced.certificate
  else {
    value := meet side done.value produced.value
    accepted := meet_accepted side threshold _ _ done.accepted produced.accepted
    childAt := fun port => by
      if before : port.val < children.length then
        have same : (children ++ [child]).get port = children.get ⟨port.val, before⟩ := by
          simp [List.get_eq_getElem, before]
        rw [same]
        exact (done.childAt ⟨port.val, before⟩).weaken _ (meet_left side done.value produced.value)
      else
        have last : port.val = children.length := by
          have bounded := port.isLt
          simp only [List.length_append, List.length_singleton] at bounded
          omega
        have same : (children ++ [child]).get port = child := by
          simp [List.get_eq_getElem, last]
        rw [same]
        exact produced.certificate.weaken _ (meet_right side done.value produced.value)
  }

def Certificates.snoc {n : Nat} {side : Polarity} {threshold : Int}
    {children : List (Move n × Frame n)} (values : Certificates side threshold children)
    (child : Move n × Frame n) (value : Certificate side threshold child.2) :
    Certificates side threshold (children ++ [child]) :=
  values.snocSource child (SourceCertificate.ofCertificate value)

theorem focused_child {n : Nat} {parent : Frame n}
    {before : List (Move n × Frame n)} {child : Move n × Frame n}
    {after : List (Move n × Frame n)}
    (cover : before ++ child :: after = scoringExpansion parent) :
    LegalStep (Law.positionalSuperko 0) parent child.1 child.2 ∧ child.1 ≠ .resign := by
  apply mem_scoringExpansion_iff.mp
  rw [← cover]
  exact List.mem_append_right before List.mem_cons_self

/-- Each stored prefix contains only the opposing certificates needed if no mover reply succeeds. -/
inductive Context {n : Nat} (threshold : Int) (origin : Frame n) : Frame n → Type
  | root : Context threshold origin origin
  | white {parent : Frame n}
      (playing : parent.visible.status = .playing) (owned : parent.visible.toMove = .negative)
      (before : List (Move n × Frame n))
      (done : Certificates .positive (threshold + 1) before)
      (child : Move n × Frame n) (after : List (Move n × Frame n))
      (cover : before ++ child :: after = scoringExpansion parent)
      (up : Context threshold origin parent) : Context threshold origin child.2
  | black {parent : Frame n}
      (playing : parent.visible.status = .playing) (owned : parent.visible.toMove = .positive)
      (before : List (Move n × Frame n))
      (done : Certificates .negative threshold before)
      (child : Move n × Frame n) (after : List (Move n × Frame n))
      (cover : before ++ child :: after = scoringExpansion parent)
      (up : Context threshold origin parent) : Context threshold origin child.2

inductive Cursor {n : Nat} (threshold : Int) (origin : Frame n) : Type
  | origin (scoring : ScoringStatus origin)
  | inspect (frame : Frame n) (scoring : ScoringStatus frame) (context : Context threshold origin frame)
  | returning (frame : Frame n) (answer : SourceResult threshold frame) (context : Context threshold origin frame)

inductive Result {n : Nat} (threshold : Int) (origin : Frame n) where
  | answered (produced : SourceResult threshold origin)
  | bound (produced : UnilateralBound origin) (continued : Cursor threshold origin)
  | pending (continued : Cursor threshold origin)

/-- Matrix storage is refreshed once at the native call boundary, with the original frame index restored. -/
def focus {n : Nat} {threshold : Int} {origin : Frame n} (frame : Frame n)
    (scoring : ScoringStatus frame) (context : Context threshold origin frame) : Cursor threshold origin :=
  let buffer := BufferedReplay.capture frame
  let same := BufferedReplay.restore_capture frame
  .inspect (BufferedReplay.restore buffer) (same.symm ▸ scoring) (same.symm ▸ context)

def initial {n : Nat} (threshold : Int) (frame : Frame n) (scoring : ScoringStatus frame) :
    Cursor threshold frame := .origin scoring

private theorem expansion_nonempty {n : Nat} (frame : Frame n)
    (playing : frame.visible.status = .playing) : scoringExpansion frame ≠ [] := by
  intro empty
  have member := mem_scoringExpansion_iff.mpr
    ⟨(passReply frame playing).step, (passReply frame playing).notResign⟩
  rw [empty] at member
  contradiction

private theorem shift_cover {n : Nat} {parent : Frame n}
    {before : List (Move n × Frame n)} {child next : Move n × Frame n}
    {tail : List (Move n × Frame n)}
    (cover : before ++ child :: next :: tail = scoringExpansion parent) :
    (before ++ [child]) ++ next :: tail = scoringExpansion parent := by
  simpa only [List.append_assoc, List.singleton_append] using cover

private def inspectResult {n : Nat} {threshold : Int} {origin : Frame n}
    (frame : Frame n) (scoring : ScoringStatus frame) (context : Context threshold origin frame) :
    Result threshold origin :=
      match observed : settleResult? frame threshold scoring with
      | some answer => .pending (.returning frame answer context)
      | none =>
          have playing := settleResult_none_playing frame threshold scoring observed
          match children : scoringExpansion frame with
          | [] => False.elim (expansion_nonempty frame playing children)
          | child :: after =>
              have cover : [] ++ child :: after = scoringExpansion frame := children.symm
              have native := focused_child cover
              let nextScoring := nonresigning_step_scoringStatus native.2 native.1
              match owned : frame.visible.toMove with
              | .negative => .pending (focus child.2 nextScoring
                  (.white playing owned [] .nil child after cover context))
              | .positive => .pending (focus child.2 nextScoring
                  (.black playing owned [] .nil child after cover context))

/-- The origin's independent producer is consumed once. Its bound need not
decide this query; the accompanying continuation has already passed that stage. -/
def emitResult {n : Nat} {threshold : Int} {origin : Frame n} :
    Cursor threshold origin → Result threshold origin
  | .origin scoring =>
      match SourceLeaf.originBound? origin with
      | some produced => .bound produced (focus origin scoring .root)
      | none => inspectResult origin scoring .root
  | .inspect frame scoring context => inspectResult frame scoring context
  | .returning _ answer context =>
      match context with
      | .root => .answered answer
      | @Context.white _ _ _ parent playing owned before done child after cover up =>
          match answer with
          | .white won =>
              have native := focused_child cover
              let reply : ScoringReply parent := ⟨child.1, child.2, native.2, native.1⟩
              .pending (.returning parent (.white (SourceCertificate.choose reply owned won)) up)
          | .black counter =>
              let accumulated := done.snocSource child counter
              match after with
              | [] =>
                  have full : before ++ [child] = scoringExpansion parent := cover
                  let completed : Certificates .positive (threshold + 1) (scoringExpansion parent) :=
                    full ▸ accumulated
                  have opponent : parent.visible.toMove ≠ .positive := by rw [owned]; decide
                  .pending (.returning parent
                    (.black ⟨completed.value, .all playing opponent completed.childAt, completed.accepted⟩) up)
              | next :: tail =>
                  have nextCover := shift_cover cover
                  have native := focused_child nextCover
                  .pending (focus next.2 (nonresigning_step_scoringStatus native.2 native.1)
                    (.white playing owned (before ++ [child]) accumulated next tail nextCover up))
      | @Context.black _ _ _ parent playing owned before done child after cover up =>
          match answer with
          | .black won =>
              have native := focused_child cover
              let reply : ScoringReply parent := ⟨child.1, child.2, native.2, native.1⟩
              .pending (.returning parent (.black (SourceCertificate.choose reply owned won)) up)
          | .white counter =>
              let accumulated := done.snocSource child counter
              match after with
              | [] =>
                  have full : before ++ [child] = scoringExpansion parent := cover
                  let completed : Certificates .negative threshold (scoringExpansion parent) :=
                    full ▸ accumulated
                  have opponent : parent.visible.toMove ≠ .negative := by rw [owned]; decide
                  .pending (.returning parent
                    (.white ⟨completed.value, .all playing opponent completed.childAt, completed.accepted⟩) up)
              | next :: tail =>
                  have nextCover := shift_cover cover
                  have native := focused_child nextCover
                  .pending (focus next.2 (nonresigning_step_scoringStatus native.2 native.1)
                    (.black playing owned (before ++ [child]) accumulated next tail nextCover up))

/-- Legacy threshold readout of the same emitted event. Independent bounds do
not become answers to a stronger query; this reader preserves their continuation. -/
def emit {n : Nat} {threshold : Int} {origin : Frame n} (cursor : Cursor threshold origin) :
    Answer threshold origin ⊕ Cursor threshold origin :=
  match emitResult cursor with
  | .answered produced => .inl produced.toAnswer
  | .bound _ continued => .inr continued
  | .pending continued => .inr continued

/-- Fuel bounds observation of calculation events and returns the remaining cursor intact. -/
def observe {n : Nat} {threshold : Int} {origin : Frame n} :
    Nat → Cursor threshold origin → Answer threshold origin ⊕ Cursor threshold origin
  | 0, current => .inr current
  | fuel + 1, current =>
      match emit current with
      | .inl answer => .inl answer
      | .inr next => observe fuel next

def initial19 (threshold : Int) : Cursor threshold (Frame.initial 19) :=
  initial threshold _ (Or.inl rfl)

end SaturationMonoid.ProcessGame.Go.CriticalKomi.DecisionCursor
