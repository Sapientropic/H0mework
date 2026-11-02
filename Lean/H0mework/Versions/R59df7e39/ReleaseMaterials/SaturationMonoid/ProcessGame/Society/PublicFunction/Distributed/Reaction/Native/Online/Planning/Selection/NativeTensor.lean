import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.NativeManifest
import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Tensor
import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.NativeProfile
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2500000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.NativeTensor
open Institutions.Capitalism.Universal.Source.Program
open Distributed.Recall.Information.Agency.Protocol
variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  {seed : Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)}
  {driver : Feedback.Input seed.source.code} (cursor : Cursor seed driver)
inductive Event (Party Good Port Technology Instrument : Type) where
  | source (event : NativeSourceFrames.Event)
  | profile (value : NativeProfile.Event Party Good Port Technology Instrument)
  | manifest (value : NativeManifest.Event Party Good Port Technology Instrument)
  deriving DecidableEq

structure Emission (α Party Good Port Technology Instrument : Type) where
  private mk ::
  value : α
  work : List (Event Party Good Port Technology Instrument)
local notation "Produced" => Emission

def evaluation (bound : Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)) (start span : Nat) :
    Produced (Evaluation bound.source.code) Party Good Port Technology Instrument :=
  let frames := NativeSourceFrames.compile bound.source.input (Window.finish start span)
  let profile := NativeProfile.compileFrom bound start span frames
  let native := NativeManifest.compileFrom bound start span frames
  ⟨⟨Window.legal bound start span,
    (List.finRange bound.source.code.task.slots.length).all (fun index =>
      (Identity.firstService bound.source (Window.finish start span-1) index).isSome),
    profile.profile,native.manifest,Window.value bound start span⟩,
    frames.work.map Event.source ++ profile.work.map Event.profile ++ native.work.map Event.manifest⟩
theorem evaluation_exact (bound : Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)) (start span : Nat) :
    (evaluation bound start span).value = Window.evaluate bound start span := by
  dsimp only [evaluation]
  rw [(NativeProfile.compileFrom _ _ _ _).exact,(NativeManifest.compileFrom _ _ _ _).exact]
  rfl
def evaluationBudget (bound : Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)) (start span : Nat) :=
  NativeSourceFrames.budget bound.source.input (Window.finish start span) +
    NativeProfile.budget bound start span + NativeManifest.budget bound start span
theorem evaluation_work_bound (bound : Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)) (start span : Nat) :
    (evaluation bound start span).work.length ≤ evaluationBudget bound start span := by
  simp only [evaluation,List.length_append,List.length_map,evaluationBudget]
  have source := NativeSourceFrames.work_bound bound.source.input (Window.finish start span)
  have a := NativeProfile.workFrom_bound bound start span (NativeSourceFrames.compile bound.source.input (Window.finish start span))
  have b := NativeManifest.workFrom_bound bound start span (NativeSourceFrames.compile bound.source.input (Window.finish start span))
  omega

def present (term : Term cursor) (rival : Opponent cursor.source.val.code) (n : Nat) :
    Produced (Evaluation cursor.source.val.code) Party Good Port Technology Instrument :=
  evaluation (Planning.candidate cursor term rival n) cursor.depth n
theorem present_exact (term : Term cursor) (rival : Opponent cursor.source.val.code) (n : Nat) :
    (present cursor term rival n).value = Planning.present cursor term rival n := evaluation_exact _ _ _
def presentBudget (term : Term cursor) (rival : Opponent cursor.source.val.code) (n : Nat) :=
  evaluationBudget (Planning.candidate cursor term rival n) cursor.depth n
theorem present_work_bound (term : Term cursor) (rival : Opponent cursor.source.val.code) (n : Nat) :
    (present cursor term rival n).work.length ≤ presentBudget cursor term rival n := evaluation_work_bound _ _ _

variable {old : Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)}
  {oldDepth : Nat} {target : Authority.Sources old.base old.scope} {count : Nat}
  {word : List (Future.Recovery.Action old)} {receipt : Future.Receipt old oldDepth target count word}
def report (made : Future.Recovery.Output receipt) (start : Nat) (sameCode : target.val.code = old.source.code) :
    Produced (Future.Recovery.Assessment.Report old) Party Good Port Technology Instrument :=
  let source := evaluation made.bound start (made.walk.finish.depth-start)
  let evaluated : Evaluation target.val.code :=
    made.source_code_is_the_target_code ▸ source.value
  ⟨⟨made.walk.finish.consumed.length,sameCode ▸ evaluated⟩,source.work⟩
theorem report_exact (made : Future.Recovery.Output receipt) (start : Nat) (sameCode : target.val.code = old.source.code) :
    (report made start sameCode).value = Future.Recovery.Assessment.reportFrom made start sameCode := by
  dsimp only [report,Future.Recovery.Assessment.reportFrom,Future.Recovery.Output.evaluationFrom]
  rw [evaluation_exact]
def reportBudget (made : Future.Recovery.Output receipt) (start : Nat) :=
  evaluationBudget made.bound start (made.walk.finish.depth-start)
theorem report_work_bound (made : Future.Recovery.Output receipt) (start : Nat) (sameCode : target.val.code = old.source.code) :
    (report made start sameCode).work.length ≤ reportBudget made start := evaluation_work_bound _ _ _

variable (pricing : Future.Recovery.Pricing (Future.Recovery.Action cursor.model))
def futureWords (words : List (List (Future.Recovery.Action cursor.model))) (n : Nat)
    (word : List (Future.Recovery.Action cursor.model)) :
    Produced (Option (Future.Recovery.Assessment.Report cursor.model)) Party Good Port Technology Instrument :=
  match Future.produce cursor.model cursor.depth (wordTarget cursor words).indexed (cursor.count+n) word with
  | .inl _ => ⟨none,[]⟩
  | .inr receipt =>
    let made := Future.Recovery.produceWith pricing receipt
    let generated := report made cursor.depth rfl
    ⟨some generated.value,generated.work⟩
def futureWordsBudget (words : List (List (Future.Recovery.Action cursor.model))) (n : Nat)
    (word : List (Future.Recovery.Action cursor.model)) : Nat :=
  match Future.produce cursor.model cursor.depth (wordTarget cursor words).indexed (cursor.count+n) word with
  | .inl _ => 0
  | .inr receipt => reportBudget (Future.Recovery.produceWith pricing receipt) cursor.depth
theorem futureWords_exact (words : List (List (Future.Recovery.Action cursor.model))) (n : Nat)
    (word : List (Future.Recovery.Action cursor.model)) :
    (futureWords cursor pricing words n word).value = (Planning.restorationWords cursor pricing words n word).map Prod.fst := by
  unfold futureWords Planning.restorationWords
  generalize same : Future.produce cursor.model cursor.depth (wordTarget cursor words).indexed (cursor.count+n) word = actual
  cases actual with
  | inl _ => rfl
  | inr receipt => exact congrArg some (report_exact (Future.Recovery.produceWith pricing receipt) cursor.depth rfl)
theorem futureWords_work_bound (words : List (List (Future.Recovery.Action cursor.model))) (n : Nat)
    (word : List (Future.Recovery.Action cursor.model)) :
    (futureWords cursor pricing words n word).work.length ≤ futureWordsBudget cursor pricing words n word := by
  unfold futureWords futureWordsBudget
  generalize same : Future.produce cursor.model cursor.depth (wordTarget cursor words).indexed (cursor.count+n) word = actual
  cases actual with
  | inl _ => exact Nat.le_refl _
  | inr receipt => exact report_work_bound (Future.Recovery.produceWith pricing receipt) cursor.depth rfl

def future (term : Term cursor) (rival : Opponent cursor.source.val.code) (n : Nat)
    (word : List (Future.Recovery.Action cursor.model)) :=
  futureWords cursor pricing (forecastWords cursor.source.val.code (schedule cursor term) ⟨rival,cursor.input.budget⟩ cursor.state n) n word
def futureBudget (term : Term cursor) (rival : Opponent cursor.source.val.code) (n : Nat)
    (word : List (Future.Recovery.Action cursor.model)) :=
  futureWordsBudget cursor pricing (forecastWords cursor.source.val.code (schedule cursor term) ⟨rival,cursor.input.budget⟩ cursor.state n) n word
theorem future_exact (term : Term cursor) (rival : Opponent cursor.source.val.code) (n : Nat)
    (word : List (Future.Recovery.Action cursor.model)) :
    (future cursor pricing term rival n word).value = (tensor cursor pricing term rival n).future cursor word :=
  futureWords_exact _ _ _ _ _
theorem future_work_bound (term : Term cursor) (rival : Opponent cursor.source.val.code) (n : Nat)
    (word : List (Future.Recovery.Action cursor.model)) :
    (future cursor pricing term rival n word).work.length ≤ futureBudget cursor pricing term rival n word :=
  futureWords_work_bound _ _ _ _ _
end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.NativeTensor
