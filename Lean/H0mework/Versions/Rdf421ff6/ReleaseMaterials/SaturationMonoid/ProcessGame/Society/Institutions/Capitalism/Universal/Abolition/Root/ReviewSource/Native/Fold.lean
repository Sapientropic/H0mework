import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.ReviewSource.Native.Origin

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.ReviewSource.Native

open ResponsibilityLifecycle
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Registered

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  {input : ProgrammeSource.Input Party Good Port Technology Instrument}
  (origin : OriginAt input) (depth count prefixLimit renewalLimit : Nat)

local notation "Raw" => Compile.RawInput Party Good Port Technology Instrument

def actualInput (past : List Raw) (raw : Raw) : SourceInput (Party := Party) (Good := Good)
    (Port := Port) (Technology := Technology) (Instrument := Instrument) :=
  ⟨inferInstance, depth, count, prefixLimit, renewalLimit,
    Physical.receive (Physical.Prefix.cursor past) raw⟩

def fold {index : origin.Slot} (past : List Raw) : List Raw →
    origin.Thread depth count index → origin.Thread depth count index
  | [], prior => prior
  | raw :: rest, prior => fold (past ++ [raw]) rest
      (origin.advance depth count prior (actualInput depth count prefixLimit renewalLimit past raw))

def foldRun {index : origin.Slot} (past : List Raw) (rest : List Raw)
    (prior : origin.Thread depth count index) : (origin.process depth count).Run
    (origin.state depth count prior).current
    (origin.state depth count (fold origin depth count prefixLimit renewalLimit past rest prior)).current := by
  induction rest generalizing past prior with
  | nil => exact .nil
  | cons raw rest inherited =>
      exact (origin.run depth count prior _).concatRuns _
        (inherited (past ++ [raw]) (origin.advance depth count prior _))

theorem fold_append {index : origin.Slot} (past left right : List Raw)
    (prior : origin.Thread depth count index) :
    fold origin depth count prefixLimit renewalLimit past (left ++ right) prior =
      fold origin depth count prefixLimit renewalLimit (past ++ left) right
        (fold origin depth count prefixLimit renewalLimit past left prior) := by
  induction left generalizing past prior with
  | nil => simp only [List.nil_append, List.append_nil, fold]
  | cons raw rest inherited =>
      simp only [List.cons_append, fold]
      rw [inherited]
      simp only [List.append_assoc, List.singleton_append]

/-- Only the already consumed raw past is folded. The incoming query is
not a payment and cannot create a native event or replace the original seed. -/
def atPast (past : List Raw) (index : origin.Slot) :=
  fold origin depth count prefixLimit renewalLimit [] past (origin.seed depth count index)

theorem atPast_append (past : List Raw) (raw : Raw) (index : origin.Slot) :
    atPast origin depth count prefixLimit renewalLimit (past ++ [raw]) index =
      origin.advance depth count (atPast origin depth count prefixLimit renewalLimit past index)
        (actualInput depth count prefixLimit renewalLimit past raw) := by
  rw [atPast, fold_append]
  rfl

def runAt (past : List Raw) (index : origin.Slot) : (origin.process depth count).Run
    (origin.state depth count (origin.seed depth count index)).current
    (origin.state depth count (atPast origin depth count prefixLimit renewalLimit past index)).current :=
  foldRun origin depth count prefixLimit renewalLimit [] past _

theorem all_original_native_history_is_retained (past : List Raw) (index : origin.Slot) :
    (origin.state depth count (origin.seed depth count index)).current.history <+:
      (origin.state depth count (atPast origin depth count prefixLimit renewalLimit past index)).current.history := by
  rw [(runAt origin depth count prefixLimit renewalLimit past index).history_eq]
  exact List.prefix_append _ _

#print axioms atPast_append
#print axioms runAt
#print axioms all_original_native_history_is_retained

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.ReviewSource.Native
