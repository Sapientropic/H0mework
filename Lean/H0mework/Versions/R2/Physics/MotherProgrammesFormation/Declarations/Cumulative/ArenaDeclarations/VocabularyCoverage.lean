import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.Cumulative.ArenaDeclarations.VocabularyPresentation
import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.Cumulative.ArenaFormation.NetworkCoverage

set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherArenaVocabulary
open MotherArenaNetwork
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open scoped Classical
noncomputable section
variable {rank : Ordinal.{0}}
local notation "B" => MotherArenaHigher.Base rank
local notation "M" => MotherArenaHigher.Material rank

structure Encoding (V : Vocabulary.{0}) where
  current : V.Current ↪ B
  anchor : V.Anchor ↪ B
  incidence : V.Incidence ↪ B
  lineage : V.Lineage ↪ B
  native : (Σ c, V.NativeWriteAt c) ↪ B
  relation : (Σ c, V.RelationWriteAt c) ↪ B
  continued : (Σ c, V.ContinuedTransportAt c) ↪ B
  redirect : (Σ c, V.BorromeanRedirectAt c) ↪ B
  terminal : (Σ c, V.FaithfulTerminalAt c) ↪ B
  cofinal : V.cofinal.Event ↪ B

namespace Encoding
variable {V : Vocabulary.{0}} (e : Encoding V)

def graph (tag : Nat) (code : B) : Prop :=
  let p := (MotherArenaHigher.unpair rank) code
  let q := (MotherArenaHigher.unpair rank) p.2
  if 20 ≤ tag then ∃ v, e.cofinal v = p.1 ∧ e.current (V.cofinal.pathAt v (tag - 20)) = p.2
  else match tag with
  | 0 => ∃ c, e.current c = code
  | 1 => ∃ a, e.anchor a = code
  | 2 => ∃ a, e.incidence a = code
  | 3 => ∃ a, e.lineage a = code
  | 4 => ∃ c w, e.current c = p.1 ∧ e.native ⟨c, w⟩ = p.2
  | 5 => ∃ c w, e.current c = p.1 ∧ e.relation ⟨c, w⟩ = p.2
  | 6 => ∃ c w, e.current c = p.1 ∧ e.continued ⟨c, w⟩ = p.2
  | 7 => ∃ c w, e.current c = p.1 ∧ e.redirect ⟨c, w⟩ = p.2
  | 8 => ∃ c w, e.current c = p.1 ∧ e.terminal ⟨c, w⟩ = p.2
  | 9 => ∃ v, e.cofinal v = code
  | 10 => ∃ c, e.current c = p.1 ∧ e.anchor (V.anchorAt c) = p.2
  | 11 => ∃ c, e.current c = p.1 ∧ e.incidence (V.incidenceAt c) = p.2
  | 12 => ∃ c, e.current c = p.1 ∧ e.lineage (V.lineageAt c) = p.2
  | 13 => ∃ c w, e.current c = p.1 ∧ e.native ⟨c, w⟩ = q.1 ∧ e.current (V.nativeTarget w) = q.2
  | 14 => ∃ c w, e.current c = p.1 ∧ e.relation ⟨c, w⟩ = q.1 ∧ e.current (V.relationTarget w) = q.2
  | 15 => ∃ c w, e.current c = p.1 ∧ e.continued ⟨c, w⟩ = q.1 ∧ e.current (V.continuedTarget w) = q.2
  | 16 => ∃ c w, e.current c = p.1 ∧ e.redirect ⟨c, w⟩ = q.1 ∧ e.current (V.redirectTarget w) = q.2
  | 17 => ∃ v, e.cofinal v = p.1 ∧ e.current (V.cofinal.target v) = p.2
  | 18 => ∃ v, e.cofinal v = code ∧ V.cofinal.emit? = some v
  | _ => False

def reader (code : B) (tag : Nat) : ℝ := if e.graph tag code then 0 else 1

theorem reader_bit {m : M} (hm : (MotherArenaHigher.read rank) m = e.reader) (tag : Nat) (code : B) :
    bit m tag code ↔ e.graph tag code := by
  by_cases h : e.graph tag code <;> simp only [bit, hm, reader, h, if_true, if_false, one_ne_zero, iff_self]

end Encoding

theorem Encoding.realizes {V : Vocabulary.{0}} (e : Encoding V)
    {m : M} (hm : (MotherArenaHigher.read rank) m = e.reader) : Nonempty (Coverage.Realizes m V) := by
  let current : V.Current ≃ Current m := MotherArenaNetworkOrigin.imageEquiv e.current (bit m 0)
    (fun b => by simpa only [Encoding.graph, show ¬ (20 ≤ 0) by decide, if_false] using e.reader_bit hm 0 b)
  let anchor : V.Anchor ≃ Anchor m := MotherArenaNetworkOrigin.imageEquiv e.anchor (bit m 1)
    (fun b => by simpa only [Encoding.graph, show ¬ (20 ≤ 1) by decide, if_false] using e.reader_bit hm 1 b)
  let incidence : V.Incidence ≃ Incidence m := MotherArenaNetworkOrigin.imageEquiv e.incidence (bit m 2)
    (fun b => by simpa only [Encoding.graph, show ¬ (20 ≤ 2) by decide, if_false] using e.reader_bit hm 2 b)
  let lineage : V.Lineage ≃ Lineage m := MotherArenaNetworkOrigin.imageEquiv e.lineage (bit m 3)
    (fun b => by simpa only [Encoding.graph, show ¬ (20 ≤ 3) by decide, if_false] using e.reader_bit hm 3 b)
  let cofinal : V.cofinal.Event ≃ CofinalEvent m := MotherArenaNetworkOrigin.imageEquiv e.cofinal (bit m 9)
    (fun b => by simpa only [Encoding.graph, show ¬ (20 ≤ 9) by decide, if_false] using e.reader_bit hm 9 b)
  let nativeCode (c : V.Current) : V.NativeWriteAt c ↪ B :=
    (Function.Embedding.sigmaMk (β := V.NativeWriteAt) c).trans e.native
  let native (c : V.Current) : V.NativeWriteAt c ≃ Native m (current c) :=
    MotherArenaNetworkOrigin.imageEquiv (nativeCode c) (fun b => r2 m 4 (current c).val b) (by
      intro b
      rw [r2, e.reader_bit hm]
      simp only [Encoding.graph, show ¬ (20 ≤ 4) by decide, if_false, (MotherArenaHigher.unpair_pair rank)]
      change (∃ c' w, e.current c' = e.current c ∧ e.native ⟨c', w⟩ = b) ↔ ∃ w, e.native ⟨c, w⟩ = b
      constructor
      · rintro ⟨c', w, hc, hw⟩
        have same := e.current.injective hc
        cases same
        exact ⟨w, hw⟩
      · rintro ⟨w, hw⟩
        exact ⟨c, w, rfl, hw⟩)
  let relationCode (c : V.Current) : V.RelationWriteAt c ↪ B :=
    (Function.Embedding.sigmaMk (β := V.RelationWriteAt) c).trans e.relation
  let relation (c : V.Current) : V.RelationWriteAt c ≃ Relation m (current c) :=
    MotherArenaNetworkOrigin.imageEquiv (relationCode c) (fun b => r2 m 5 (current c).val b) (by
      intro b
      rw [r2, e.reader_bit hm]
      simp only [Encoding.graph, show ¬ (20 ≤ 5) by decide, if_false, (MotherArenaHigher.unpair_pair rank)]
      change (∃ c' w, e.current c' = e.current c ∧ e.relation ⟨c', w⟩ = b) ↔ ∃ w, e.relation ⟨c, w⟩ = b
      constructor
      · rintro ⟨c', w, hc, hw⟩
        have same := e.current.injective hc
        cases same
        exact ⟨w, hw⟩
      · rintro ⟨w, hw⟩
        exact ⟨c, w, rfl, hw⟩)
  let continuedCode (c : V.Current) : V.ContinuedTransportAt c ↪ B :=
    (Function.Embedding.sigmaMk (β := V.ContinuedTransportAt) c).trans e.continued
  let continued (c : V.Current) : V.ContinuedTransportAt c ≃ Continued m (current c) :=
    MotherArenaNetworkOrigin.imageEquiv (continuedCode c) (fun b => r2 m 6 (current c).val b) (by
      intro b
      rw [r2, e.reader_bit hm]
      simp only [Encoding.graph, show ¬ (20 ≤ 6) by decide, if_false, (MotherArenaHigher.unpair_pair rank)]
      change (∃ c' w, e.current c' = e.current c ∧ e.continued ⟨c', w⟩ = b) ↔ ∃ w, e.continued ⟨c, w⟩ = b
      constructor
      · rintro ⟨c', w, hc, hw⟩
        have same := e.current.injective hc
        cases same
        exact ⟨w, hw⟩
      · rintro ⟨w, hw⟩
        exact ⟨c, w, rfl, hw⟩)
  let redirectCode (c : V.Current) : V.BorromeanRedirectAt c ↪ B :=
    (Function.Embedding.sigmaMk (β := V.BorromeanRedirectAt) c).trans e.redirect
  let redirect (c : V.Current) : V.BorromeanRedirectAt c ≃ Redirect m (current c) :=
    MotherArenaNetworkOrigin.imageEquiv (redirectCode c) (fun b => r2 m 7 (current c).val b) (by
      intro b
      rw [r2, e.reader_bit hm]
      simp only [Encoding.graph, show ¬ (20 ≤ 7) by decide, if_false, (MotherArenaHigher.unpair_pair rank)]
      change (∃ c' w, e.current c' = e.current c ∧ e.redirect ⟨c', w⟩ = b) ↔ ∃ w, e.redirect ⟨c, w⟩ = b
      constructor
      · rintro ⟨c', w, hc, hw⟩
        have same := e.current.injective hc
        cases same
        exact ⟨w, hw⟩
      · rintro ⟨w, hw⟩
        exact ⟨c, w, rfl, hw⟩)
  let terminalCode (c : V.Current) : V.FaithfulTerminalAt c ↪ B :=
    (Function.Embedding.sigmaMk (β := V.FaithfulTerminalAt) c).trans e.terminal
  let terminal (c : V.Current) : V.FaithfulTerminalAt c ≃ Terminal m (current c) :=
    MotherArenaNetworkOrigin.imageEquiv (terminalCode c) (fun b => r2 m 8 (current c).val b) (by
      intro b
      rw [r2, e.reader_bit hm]
      simp only [Encoding.graph, show ¬ (20 ≤ 8) by decide, if_false, (MotherArenaHigher.unpair_pair rank)]
      change (∃ c' w, e.current c' = e.current c ∧ e.terminal ⟨c', w⟩ = b) ↔ ∃ w, e.terminal ⟨c, w⟩ = b
      constructor
      · rintro ⟨c', w, hc, hw⟩
        have same := e.current.injective hc
        cases same
        exact ⟨w, hw⟩
      · rintro ⟨w, hw⟩
        exact ⟨c, w, rfl, hw⟩)
  refine ⟨{
    current := current, anchor := anchor, incidence := incidence, lineage := lineage,
    native := native, relation := relation, continued := continued, redirect := redirect,
    terminal := terminal, cofinal := cofinal,
    anchor_graph := ?_, incidence_graph := ?_, lineage_graph := ?_,
    native_graph := ?_, relation_graph := ?_, continued_graph := ?_, redirect_graph := ?_,
    cofinal_target_graph := ?_, cofinal_emit_graph := ?_, cofinal_path_graph := ?_ }⟩
  · intro c a
    rw [r2, e.reader_bit hm]
    simp only [Encoding.graph, show ¬ (20 ≤ 10) by decide, if_false, (MotherArenaHigher.unpair_pair rank)]
    change (∃ c', e.current c' = e.current c ∧ e.anchor (V.anchorAt c') = a.val) ↔ a = anchor (V.anchorAt c)
    constructor
    · rintro ⟨c', hc, ha⟩
      have same := e.current.injective hc
      cases same
      exact Subtype.ext ha.symm
    · intro ha
      cases ha
      exact ⟨c, rfl, rfl⟩
  · intro c a
    rw [r2, e.reader_bit hm]
    simp only [Encoding.graph, show ¬ (20 ≤ 11) by decide, if_false, (MotherArenaHigher.unpair_pair rank)]
    change (∃ c', e.current c' = e.current c ∧ e.incidence (V.incidenceAt c') = a.val) ↔ a = incidence (V.incidenceAt c)
    constructor
    · rintro ⟨c', hc, ha⟩
      have same := e.current.injective hc
      cases same
      exact Subtype.ext ha.symm
    · intro ha
      cases ha
      exact ⟨c, rfl, rfl⟩
  · intro c a
    rw [r2, e.reader_bit hm]
    simp only [Encoding.graph, show ¬ (20 ≤ 12) by decide, if_false, (MotherArenaHigher.unpair_pair rank)]
    change (∃ c', e.current c' = e.current c ∧ e.lineage (V.lineageAt c') = a.val) ↔ a = lineage (V.lineageAt c)
    constructor
    · rintro ⟨c', hc, ha⟩
      have same := e.current.injective hc
      cases same
      exact Subtype.ext ha.symm
    · intro ha
      cases ha
      exact ⟨c, rfl, rfl⟩
  · intro c w t
    rw [r3, e.reader_bit hm]
    simp only [Encoding.graph, show ¬ (20 ≤ 13) by decide, if_false, (MotherArenaHigher.unpair_pair rank)]
    change (∃ c' w', e.current c' = e.current c ∧ e.native ⟨c', w'⟩ = e.native ⟨c, w⟩ ∧
      e.current (V.nativeTarget w') = t.val) ↔ t = current (V.nativeTarget w)
    constructor
    · rintro ⟨c', w', hc, hw, ht⟩
      have same := e.current.injective hc
      cases same
      have same := (nativeCode c).injective hw
      cases same
      exact Subtype.ext ht.symm
    · intro ht
      cases ht
      exact ⟨c, w, rfl, rfl, rfl⟩
  · intro c w t
    rw [r3, e.reader_bit hm]
    simp only [Encoding.graph, show ¬ (20 ≤ 14) by decide, if_false, (MotherArenaHigher.unpair_pair rank)]
    change (∃ c' w', e.current c' = e.current c ∧ e.relation ⟨c', w'⟩ = e.relation ⟨c, w⟩ ∧
      e.current (V.relationTarget w') = t.val) ↔ t = current (V.relationTarget w)
    constructor
    · rintro ⟨c', w', hc, hw, ht⟩
      have same := e.current.injective hc
      cases same
      have same := (relationCode c).injective hw
      cases same
      exact Subtype.ext ht.symm
    · intro ht
      cases ht
      exact ⟨c, w, rfl, rfl, rfl⟩
  · intro c w t
    rw [r3, e.reader_bit hm]
    simp only [Encoding.graph, show ¬ (20 ≤ 15) by decide, if_false, (MotherArenaHigher.unpair_pair rank)]
    change (∃ c' w', e.current c' = e.current c ∧ e.continued ⟨c', w'⟩ = e.continued ⟨c, w⟩ ∧
      e.current (V.continuedTarget w') = t.val) ↔ t = current (V.continuedTarget w)
    constructor
    · rintro ⟨c', w', hc, hw, ht⟩
      have same := e.current.injective hc
      cases same
      have same := (continuedCode c).injective hw
      cases same
      exact Subtype.ext ht.symm
    · intro ht
      cases ht
      exact ⟨c, w, rfl, rfl, rfl⟩
  · intro c w t
    rw [r3, e.reader_bit hm]
    simp only [Encoding.graph, show ¬ (20 ≤ 16) by decide, if_false, (MotherArenaHigher.unpair_pair rank)]
    change (∃ c' w', e.current c' = e.current c ∧ e.redirect ⟨c', w'⟩ = e.redirect ⟨c, w⟩ ∧
      e.current (V.redirectTarget w') = t.val) ↔ t = current (V.redirectTarget w)
    constructor
    · rintro ⟨c', w', hc, hw, ht⟩
      have same := e.current.injective hc
      cases same
      have same := (redirectCode c).injective hw
      cases same
      exact Subtype.ext ht.symm
    · intro ht
      cases ht
      exact ⟨c, w, rfl, rfl, rfl⟩
  · intro v t
    rw [r2, e.reader_bit hm]
    simp only [Encoding.graph, show ¬ (20 ≤ 17) by decide, if_false, (MotherArenaHigher.unpair_pair rank)]
    change (∃ v', e.cofinal v' = e.cofinal v ∧ e.current (V.cofinal.target v') = t.val) ↔
      t = current (V.cofinal.target v)
    constructor
    · rintro ⟨v', hv, ht⟩
      have same := e.cofinal.injective hv
      cases same
      exact Subtype.ext ht.symm
    · intro ht
      cases ht
      exact ⟨v, rfl, rfl⟩
  · intro v
    rw [e.reader_bit hm]
    simp only [Encoding.graph, show ¬ (20 ≤ 18) by decide, if_false]
    change (∃ v', e.cofinal v' = e.cofinal v ∧ V.cofinal.emit? = some v') ↔ V.cofinal.emit? = some v
    constructor
    · rintro ⟨v', hv, selected⟩
      have same := e.cofinal.injective hv
      cases same
      exact selected
    · intro selected
      exact ⟨v, rfl, selected⟩
  · intro v n t
    rw [r2, e.reader_bit hm]
    simp only [Encoding.graph, show 20 ≤ 20 + n from Nat.le_add_right 20 n, if_true,
      (MotherArenaHigher.unpair_pair rank), Nat.add_sub_cancel_left]
    change (∃ v', e.cofinal v' = e.cofinal v ∧ e.current (V.cofinal.pathAt v' n) = t.val) ↔
      t = current (V.cofinal.pathAt v n)
    constructor
    · rintro ⟨v', hv, ht⟩
      have same := e.cofinal.injective hv
      cases same
      exact Subtype.ext ht.symm
    · intro ht
      cases ht
      exact ⟨v, rfl, rfl⟩

theorem every_embedded_vocabulary (V : Vocabulary.{0}) (encode : Encoding (rank := rank) V) :
    ∃ m : M, ∃ W : Vocabulary.{0}, formVocabulary m = some W ∧ Nonempty (Presentation V W) := by
  obtain ⟨m, hm⟩ := (MotherArenaHigher.read_surjective rank) encode.reader
  obtain ⟨realizes⟩ := encode.realizes hm
  exact ⟨m, realizes.formed⟩

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherArenaVocabulary
