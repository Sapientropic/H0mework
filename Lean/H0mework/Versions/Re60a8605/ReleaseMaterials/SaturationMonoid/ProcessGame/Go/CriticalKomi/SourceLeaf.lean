import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Go.CriticalKomi.StrategyCertificate
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Go.CriticalKomi.TwoEyeGrowth
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Go.CriticalKomi.ChamberRecognize
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Go.CriticalKomi.OnePointBirth
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Go.CriticalKomi.GroupReserve
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Go.CriticalKomi.CapturingBirth
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Go.CriticalKomi.StraightFourBirth
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Go.CriticalKomi.CoreCapturingBirth
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Go.CriticalKomi.WallResponse
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Go.CriticalKomi.VitalBirthRecognize
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Go.CriticalKomi.HookSource
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Go.CriticalKomi.ElevenLeftBridge

/-!
Source frames settle only through original two-pass scoring, a native pass that
finishes scoring, source-recognized living area, legal growth, chamber counterplay,
or a source-born two-eye completion. `none` retains an unresolved branch for the
original successor consumer.
-/

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Go.CriticalKomi

inductive Answer {n : Nat} (threshold : Int) (frame : Frame n) : Type
  | white (certificate : Certificate .negative threshold frame)
  | black (certificate : Certificate .positive (threshold + 1) frame)

namespace Answer

def policy {n : Nat} {threshold : Int} {frame : Frame n}
    (answer : Answer threshold frame) : ExecutablePolicy n :=
  match answer with
  | .white certificate => certificate.policy
  | .black certificate => certificate.policy

def Guarantees {n : Nat} {threshold : Int} {frame : Frame n}
    (answer : Answer threshold frame) (scoring : ScoringStatus frame)
    (opponent : ExecutablePolicy n) : Prop :=
  match answer with
  | .white certificate =>
      areaMargin (executePolicies (versus .negative certificate.policy opponent)
        frame scoring).replay.final.visible.board ≤ threshold
  | .black certificate =>
      threshold + 1 ≤
        areaMargin (executePolicies (versus .positive certificate.policy opponent)
          frame scoring).replay.final.visible.board

theorem guarantee {n : Nat} {threshold : Int} {frame : Frame n}
    (answer : Answer threshold frame) (scoring : ScoringStatus frame)
    (opponent : ExecutablePolicy n) : answer.Guarantees scoring opponent := by
  cases answer with
  | white certificate =>
      simpa only [Guarantees, acceptsMargin, decide_eq_true_eq] using
        certificate.guarantee scoring opponent
  | black certificate =>
      simpa only [Guarantees, acceptsMargin, decide_eq_true_eq] using
        certificate.guarantee scoring opponent

end Answer

structure SourceCertificate {n : Nat} (colour : Polarity) (threshold : Int) (frame : Frame n) where
  value : Int
  certificate : Certificate colour value frame
  accepted : acceptsMargin colour threshold value = true

/-- A source result may improve one side without deciding the current query. -/
structure UnilateralBound {n : Nat} (frame : Frame n) where
  colour : Polarity
  value : Int
  certificate : Certificate colour value frame

def UnilateralBound.ofCertificate {n : Nat} {colour : Polarity} {value : Int} {frame : Frame n}
    (certificate : Certificate colour value frame) : UnilateralBound frame :=
  ⟨colour, value, certificate⟩

namespace SourceCertificate

/-- Read a bound already carried by the produced leaf. Universal and choice
programs retain their paid threshold; this never unfolds their descendants. -/
def ofCertificate {n : Nat} {colour : Polarity} {threshold : Int} {frame : Frame n}
    (certificate : Certificate colour threshold frame) : SourceCertificate colour threshold frame :=
  match certificate with
  | .terminal finished accepted =>
      ⟨areaMargin frame.visible.board, .terminal finished (by cases colour <;> simp [acceptsMargin]), accepted⟩
  | .twoEye detected scoring accepted =>
      ⟨TwoEye.bound detected.geometry colour,
        .twoEye detected scoring (by cases colour <;> simp [acceptsMargin]), accepted⟩
  | .twoEyeFamily detected scoring accepted =>
      ⟨detected.bound, .twoEyeFamily detected scoring (by cases colour <;> simp [acceptsMargin]), accepted⟩
  | .eyeCoalition detected scoring accepted =>
      ⟨EyeCoalition.bound detected.geometry colour,
        .eyeCoalition detected scoring (by cases colour <;> simp [acceptsMargin]), accepted⟩
  | .vitalChambers detected scoring accepted =>
      ⟨VitalChambers.bound detected.geometry colour,
        .vitalChambers detected scoring (by cases colour <;> simp [acceptsMargin]), accepted⟩
  | .choose owned reply child =>
      ⟨threshold, .choose owned reply child, by cases colour <;> simp [acceptsMargin]⟩
  | .all playing opponent children =>
      ⟨threshold, .all playing opponent children, by cases colour <;> simp [acceptsMargin]⟩

def atThreshold {n : Nat} {colour : Polarity} {threshold : Int} {frame : Frame n}
    (produced : SourceCertificate colour threshold frame) : Certificate colour threshold frame :=
  if same : produced.value = threshold then same ▸ produced.certificate
  else produced.certificate.weaken threshold produced.accepted

def choose {n : Nat} {colour : Polarity} {threshold : Int} {frame : Frame n}
    (reply : ScoringReply frame) (owned : frame.visible.toMove = colour)
    (produced : SourceCertificate colour threshold reply.target) : SourceCertificate colour threshold frame :=
  ⟨produced.value, .choose owned reply produced.certificate, produced.accepted⟩

end SourceCertificate

/-- The original decision and the producer's independent margin share one
certificate occurrence. The threshold is a consumer, not the stored value. -/
inductive SourceResult {n : Nat} (threshold : Int) (frame : Frame n) where
  | white (produced : SourceCertificate .negative threshold frame)
  | black (produced : SourceCertificate .positive (threshold + 1) frame)

namespace SourceResult

def ofAnswer {n : Nat} {threshold : Int} {frame : Frame n} :
    Answer threshold frame → SourceResult threshold frame
  | .white certificate => .white (SourceCertificate.ofCertificate certificate)
  | .black certificate => .black (SourceCertificate.ofCertificate certificate)

def toAnswer {n : Nat} {threshold : Int} {frame : Frame n} :
    SourceResult threshold frame → Answer threshold frame
  | .white produced => .white produced.atThreshold
  | .black produced => .black produced.atThreshold

def toBound {n : Nat} {threshold : Int} {frame : Frame n} :
    SourceResult threshold frame → UnilateralBound frame
  | .white produced => UnilateralBound.ofCertificate produced.certificate
  | .black produced => UnilateralBound.ofCertificate produced.certificate

end SourceResult

namespace SourceLeaf

/-- One source-native origin inquiry, independent of the query threshold.
The cursor consumes this stage once even when the delivered bound is weak. -/
def originBound? {n : Nat} (frame : Frame n) : Option (UnilateralBound frame) :=
  if size : n = 19 then by
    subst n
    exact if source : HookSource.Source frame then
      (HookSource.certificate? source).map UnilateralBound.ofCertificate
    else none
  else none

/-- Preserve fixed-bound source programs before the old query adapter weakens
them. The original numeric/size guards precede the same single producer call. -/
def fixedBlackResult? {n : Nat} (frame : Frame n) (threshold value : Int)
    (produce : (source : Frame 19) → Option (Certificate .positive value source)) :
    Option (SourceResult threshold frame) :=
  if accepted : acceptsMargin .positive (threshold + 1) value = true then
    if size : n = 19 then by
      subst n
      exact (produce frame).map (fun certificate => .black ⟨value, certificate, accepted⟩)
    else none
  else none

def straightFourResult? {n : Nat} (frame : Frame n) (threshold : Int) :
    Option (SourceResult threshold frame) :=
  fixedBlackResult? frame threshold (-341) StraightFourBirth.recognize?

def wallResponseResult? {n : Nat} (frame : Frame n) (threshold : Int) :
    Option (SourceResult threshold frame) :=
  fixedBlackResult? frame threshold (-345) WallResponse.recognize?

def hookSourceResult? {n : Nat} (frame : Frame n) (threshold : Int) :
    Option (SourceResult threshold frame) :=
  fixedBlackResult? frame threshold (-341) (fun source =>
    if shape : HookSource.Source source then HookSource.certificate? shape else none)

def elevenLeftBridgeResult? {n : Nat} (frame : Frame n) (threshold : Int) :
    Option (SourceResult threshold frame) :=
  fixedBlackResult? frame threshold (-345) ElevenLeftBridge.recognize?

def terminalAnswer {n : Nat} (frame : Frame n) (threshold : Int)
    (finished : frame.visible.status = .terminal .twoPasses) : Answer threshold frame :=
  if white : areaMargin frame.visible.board ≤ threshold then
    .white (.terminal finished (decide_eq_true white))
  else
    .black (.terminal finished (decide_eq_true (by omega)))

/-- The current mover can use the preceding source pass to settle immediately. -/
def passAnswer? {n : Nat} (frame : Frame n) (threshold : Int)
    (playing : frame.visible.status = .playing) : Option (Answer threshold frame) :=
  if passed : 1 ≤ frame.visible.consecutivePasses then
    let reply := passReply frame playing
    have ends : 2 ≤ frame.visible.consecutivePasses + 1 := by omega
    have finished : reply.target.visible.status = .terminal .twoPasses := by
      simp only [reply, passReply, Frame.advance, if_pos ends]
    match owned : frame.visible.toMove with
    | .negative =>
        if accepted : areaMargin frame.visible.board ≤ threshold then
          some (.white (.choose owned reply
            (.terminal finished (decide_eq_true accepted))))
        else none
    | .positive =>
        if accepted : threshold + 1 ≤ areaMargin frame.visible.board then
          some (.black (.choose owned reply
            (.terminal finished (decide_eq_true accepted))))
        else none
  else none

/-- Visit each occupied source group once.  The visited carrier only controls
recognition work; every returned value retains the original detected witness. -/
def twoEyeScan? {n : Nat} (frame : Frame n) (threshold : Int)
    (scoring : ScoringStatus frame) :
    List (Point n) → Finset (Point n) → Option (Answer threshold frame)
  | [], _ => none
  | seed :: remaining, visited =>
      if seed ∈ visited then twoEyeScan? frame threshold scoring remaining visited
      else
        match frame.visible.board seed with
        | none => twoEyeScan? frame threshold scoring remaining visited
        | some colour =>
            let core := groupAt frame.visible.board seed
            let nextVisited := visited ∪ core
            match TwoEye.recognizeSeed? frame.visible.board colour seed with
            | none => twoEyeScan? frame threshold scoring remaining nextVisited
            | some detected =>
                match colour with
                | .negative =>
                    if accepted : TwoEye.bound detected.geometry .negative ≤ threshold then
                      some (.white (.twoEye detected scoring (decide_eq_true accepted)))
                    else twoEyeScan? frame threshold scoring remaining nextVisited
                | .positive =>
                    if accepted : threshold + 1 ≤ TwoEye.bound detected.geometry .positive then
                      some (.black (.twoEye detected scoring (decide_eq_true accepted)))
                    else twoEyeScan? frame threshold scoring remaining nextVisited

/-- The attached source point must preserve every retained eye.  Its virgin
history test generates the actual native action before the larger area closes. -/
def growthAt? {n : Nat} (frame : Frame n) (colour : Polarity) (threshold : Int)
    (playing : frame.visible.status = .playing) (owned : frame.visible.toMove = colour)
    (detected : TwoEyeFamily.Detected frame.visible.board colour)
    (geometry : {g : TwoEye.Geometry n // g ∈ detected.family}) (played : Point n) :
    Option (Certificate colour threshold frame) :=
  if empty : frame.visible.board played = none then
    if avoiding : ∀ retained ∈ detected.family,
        played ≠ retained.eye₁ ∧ played ≠ retained.eye₂ then
      if attached : TwoEye.Growth.Attached geometry.1 played then
        if virgin : TwoEye.Growth.Virgin geometry.1 colour played frame.positionHistory then
          let inside := detected.holds geometry.1 geometry.2
          let eyes := avoiding geometry.1 geometry.2
          let reply := TwoEye.Growth.reply frame playing owned inside played empty eyes.1 eyes.2
            attached virgin
          let grown : TwoEyeFamily.Detected reply.target.visible.board colour := {
            family := TwoEye.Growth.enlarge geometry.1 played :: detected.family
            holds := by
              intro retained member
              rcases List.mem_cons.mp member with same | old
              · subst retained
                exact TwoEye.Growth.reply_enlarges frame playing owned inside played empty eyes.1
                  eyes.2 attached virgin
              · exact TwoEye.Growth.own_preserves (detected.holds retained old) played empty
                  (avoiding retained old).1 (avoiding retained old).2
          }
          if accepted : acceptsMargin colour threshold grown.bound = true then
            some (.choose owned reply (.twoEyeFamily grown (Or.inl rfl) accepted))
          else none
        else none
      else none
    else none
  else none

/-- A bounded source scan attempts one native enlargement, without exploring an
opponent tree or installing a future answer when no candidate succeeds. -/
def growth? {n : Nat} (frame : Frame n) (colour : Polarity) (threshold : Int)
    (playing : frame.visible.status = .playing) (owned : frame.visible.toMove = colour)
    (detected : TwoEyeFamily.Detected frame.visible.board colour) :
    Option (Certificate colour threshold frame) :=
  detected.family.attach.findSome? (fun geometry =>
    (allPoints n).findSome? (growthAt? frame colour threshold playing owned detected geometry))

def twoEyeAnswer? {n : Nat} (frame : Frame n) (threshold : Int)
    (scoring : ScoringStatus frame) : Option (Answer threshold frame) :=
  let white := TwoEyeFamily.recognize frame.visible.board .negative
  if accepted : white.bound ≤ threshold then
    some (.white (.twoEyeFamily white scoring (decide_eq_true accepted)))
  else
    let black := TwoEyeFamily.recognize frame.visible.board .positive
    if accepted : threshold + 1 ≤ black.bound then
      some (.black (.twoEyeFamily black scoring (decide_eq_true accepted)))
    else if playing : frame.visible.status = .playing then
      match ChamberRecognize.fromFamily? frame .negative threshold playing white with
      | some certificate => some (.white certificate)
      | none =>
          match ChamberRecognize.fromFamily? frame .positive (threshold + 1) playing black with
          | some certificate => some (.black certificate)
          | none =>
              match owned : frame.visible.toMove with
              | .negative =>
                  (growth? frame .negative threshold playing owned white).map (fun certificate =>
                    .white certificate)
              | .positive =>
                  (growth? frame .positive (threshold + 1) playing owned black).map (fun certificate =>
                    .black certificate)
    else none

/-- Read the actual turn and current pure-placement potentials.  A two-point
opponent obligation is compiled only after both current completions are found. -/
def birthAnswer? {n : Nat} (frame : Frame n) (threshold : Int) :
    Option (Answer threshold frame) :=
  match OnePointBirth.recognize? frame .negative threshold with
  | some certificate => some (.white certificate)
  | none =>
      (OnePointBirth.recognize? frame .positive (threshold + 1)).map
        (fun certificate => .black certificate)

def groupBirthAnswer? {n : Nat} (frame : Frame n) (threshold : Int) :
    Option (Answer threshold frame) :=
  match GroupReserve.recognize? frame .negative threshold with
  | some certificate => some (.white certificate)
  | none =>
      (GroupReserve.recognize? frame .positive (threshold + 1)).map
        (fun certificate => .black certificate)

def cooperativeBirthAnswer? {n : Nat} (frame : Frame n) (threshold : Int) :
    Option (Answer threshold frame) :=
  match CoalitionBirth.recognize? frame .negative threshold with
  | some certificate => some (.white certificate)
  | none =>
      (CoalitionBirth.recognize? frame .positive (threshold + 1)).map
        (fun certificate => .black certificate)

def capturingBirthAnswer? {n : Nat} (frame : Frame n) (threshold : Int) :
    Option (Answer threshold frame) :=
  match CapturingBirth.recognize? frame .negative threshold with
  | some certificate => some (.white certificate)
  | none =>
      (CapturingBirth.recognize? frame .positive (threshold + 1)).map
        (fun certificate => .black certificate)

def straightFourAnswer? {n : Nat} (frame : Frame n) (threshold : Int) :
    Option (Answer threshold frame) :=
  (straightFourResult? frame threshold).map SourceResult.toAnswer

def coreCapturingBirthAnswer? {n : Nat} (frame : Frame n) (threshold : Int) :
    Option (Answer threshold frame) :=
  match CoreCapturingBirth.recognize? frame .negative threshold with
  | some certificate => some (.white certificate)
  | none =>
      (CoreCapturingBirth.recognize? frame .positive (threshold + 1)).map
        (fun certificate => .black certificate)

def vitalBirthAnswer? {n : Nat} (frame : Frame n) (threshold : Int) :
    Option (Answer threshold frame) :=
  match VitalBirthRecognize.recognize? frame .negative threshold with
  | some certificate => some (Answer.white certificate)
  | none =>
      (VitalBirthRecognize.recognize? frame .positive (threshold + 1)).map
        (fun certificate => Answer.black certificate)

def hookSourceAnswer? {n : Nat} (frame : Frame n) (threshold : Int) :
    Option (Answer threshold frame) :=
  (hookSourceResult? frame threshold).map SourceResult.toAnswer

def elevenLeftBridgeAnswer? {n : Nat} (frame : Frame n) (threshold : Int) :
    Option (Answer threshold frame) :=
  (elevenLeftBridgeResult? frame threshold).map SourceResult.toAnswer

/-- Source-generated sealing and extension programs retain the complete
original frontier and history. The requested threshold must accept their bound. -/
def wallResponseAnswer? {n : Nat} (frame : Frame n) (threshold : Int) :
    Option (Answer threshold frame) :=
  (wallResponseResult? frame threshold).map SourceResult.toAnswer

def coalitionAnswer? {n : Nat} (frame : Frame n) (threshold : Int)
    (scoring : ScoringStatus frame) : Option (Answer threshold frame) :=
  let white := (EyeCoalition.recognize? frame.visible.board .negative).bind (fun detected =>
    if accepted : acceptsMargin .negative threshold (EyeCoalition.bound detected.geometry .negative) = true then
      some (Answer.white (.eyeCoalition detected scoring accepted))
    else none)
  match white with
  | some answer => some answer
  | none =>
      (EyeCoalition.recognize? frame.visible.board .positive).bind (fun detected =>
        if accepted : acceptsMargin .positive (threshold + 1) (EyeCoalition.bound detected.geometry .positive) = true then
          some (Answer.black (.eyeCoalition detected scoring accepted))
        else none)

def vitalChambersAt? {n : Nat} (frame : Frame n) (colour : Polarity) (threshold : Int)
    (scoring : ScoringStatus frame) : Option (Certificate colour threshold frame) :=
  let own := RegionAction.stones frame.visible.board colour
  -- Every counted source point is currently own or an original singleton eye.
  let possible := (own ∪ EyeCoalition.candidateEyes frame.visible.board own).card
  let possibleBound := match colour with
    | .positive => 2 * (possible : Int) - (n * n : Nat)
    | .negative => (n * n : Nat) - 2 * (possible : Int)
  if acceptsMargin colour threshold possibleBound then
    (VitalChambers.recognize? frame.visible.board colour).bind (fun detected =>
      if accepted : acceptsMargin colour threshold (VitalChambers.bound detected.geometry colour) = true then
        some (.vitalChambers detected scoring accepted)
      else none)
  else none

def vitalChambersAnswer? {n : Nat} (frame : Frame n) (threshold : Int)
    (scoring : ScoringStatus frame) : Option (Answer threshold frame) :=
  match vitalChambersAt? frame .negative threshold scoring with
  | some certificate => some (.white certificate)
  | none => (vitalChambersAt? frame .positive (threshold + 1) scoring).map Answer.black

end SourceLeaf

/-- Source-only leaf producer.  Scoring status excludes resignation, and an
unsettled result remains an open successor obligation. -/
def settleResult? {n : Nat} (frame : Frame n) (threshold : Int) (scoring : ScoringStatus frame) :
    Option (SourceResult threshold frame) :=
  if finished : frame.visible.status = .terminal .twoPasses then
    some (SourceResult.ofAnswer (SourceLeaf.terminalAnswer frame threshold finished))
  else
    have playing : frame.visible.status = .playing := scoring.resolve_right finished
    match SourceLeaf.passAnswer? frame threshold playing with
    | some answer => some (SourceResult.ofAnswer answer)
    | none =>
        match SourceLeaf.twoEyeAnswer? frame threshold scoring with
        | some answer => some (SourceResult.ofAnswer answer)
        | none =>
            match SourceLeaf.coalitionAnswer? frame threshold scoring with
            | some answer => some (SourceResult.ofAnswer answer)
            | none =>
                match SourceLeaf.vitalChambersAnswer? frame threshold scoring with
                | some answer => some (SourceResult.ofAnswer answer)
                | none =>
                    match SourceLeaf.birthAnswer? frame threshold with
                    | some answer => some (SourceResult.ofAnswer answer)
                    | none =>
                        match SourceLeaf.groupBirthAnswer? frame threshold with
                        | some answer => some (SourceResult.ofAnswer answer)
                        | none =>
                            match SourceLeaf.cooperativeBirthAnswer? frame threshold with
                            | some answer => some (SourceResult.ofAnswer answer)
                            | none =>
                                match SourceLeaf.capturingBirthAnswer? frame threshold with
                                | some answer => some (SourceResult.ofAnswer answer)
                                | none =>
                                    match SourceLeaf.coreCapturingBirthAnswer? frame threshold with
                                    | some answer => some (SourceResult.ofAnswer answer)
                                    | none =>
                                        match SourceLeaf.straightFourResult? frame threshold with
                                        | some answer => some answer
                                        | none =>
                                            match SourceLeaf.wallResponseResult? frame threshold with
                                            | some answer => some answer
                                            | none =>
                                                match SourceLeaf.hookSourceResult? frame threshold with
                                                | some answer => some answer
                                                | none =>
                                                    match SourceLeaf.elevenLeftBridgeResult? frame threshold with
                                                    | some answer => some answer
                                                    | none => (SourceLeaf.vitalBirthAnswer? frame threshold).map SourceResult.ofAnswer

/-- Compatibility reader of the same source invocation. -/
def settle? {n : Nat} (frame : Frame n) (threshold : Int) (scoring : ScoringStatus frame) :
    Option (Answer threshold frame) :=
  (settleResult? frame threshold scoring).map SourceResult.toAnswer


theorem settleResult_none_playing {n : Nat} (frame : Frame n) (threshold : Int)
    (scoring : ScoringStatus frame) (miss : settleResult? frame threshold scoring = none) :
    frame.visible.status = .playing := by
  by_cases finished : frame.visible.status = .terminal .twoPasses
  · simp only [settleResult?, dif_pos finished, Option.some_ne_none] at miss
  · exact scoring.resolve_right finished

theorem settle_none_playing {n : Nat} (frame : Frame n) (threshold : Int)
    (scoring : ScoringStatus frame) (miss : settle? frame threshold scoring = none) :
    frame.visible.status = .playing :=
  settleResult_none_playing frame threshold scoring (Option.map_eq_none_iff.mp miss)

end SaturationMonoid.ProcessGame.Go.CriticalKomi
