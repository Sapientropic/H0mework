import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.NetworkOrigin.Presentation

set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherNetworkOrigin

open ResponsibilityLifecycle.LivingLawEvolution
open MotherNetworkFactory
open scoped Classical
noncomputable section

/-- Coverage-side addresses of the whole original carriers and relation total
spaces. No one of these fields is an input to the material factory. -/
structure Encoding (N : WorldRelationNetwork.{0}) where
  support : N.Support ↪ B
  anchor : N.Anchor ↪ B
  incidence : N.Incidence ↪ B
  lineage : N.Lineage ↪ B
  responsibility : N.Responsibility ↪ B
  claim : N.Claim ↪ B
  openAt : (Σ s r, N.OpenAt s r) ↪ B
  holdsAt : (Σ s c, N.HoldsAt s c) ↪ B
  obstructionAt : (Σ s, N.ObstructionAt s) ↪ B
  semanticChangeAt : (Σ s c d, N.SemanticChangeAt s c d) ↪ B
  dispositionAt : (Σ s k, N.DispositionAt s k) ↪ B

namespace Encoding
variable {N : WorldRelationNetwork.{0}} (e : Encoding N)

def graph (tag : Nat) (x : B) : Prop :=
  let p := MotherHigherLawFamily.unpair x
  let q := MotherHigherLawFamily.unpair p.2
  let t := MotherHigherLawFamily.unpair q.2
  match tag with
  | 0 => ∃ s, e.support s = x
  | 1 => ∃ a, e.anchor a = x
  | 2 => ∃ i, e.incidence i = x
  | 3 => ∃ l, e.lineage l = x
  | 4 => ∃ r, e.responsibility r = x
  | 5 => ∃ c, e.claim c = x
  | 6 => ∃ s r w, e.support s = p.1 ∧ e.responsibility r = q.1 ∧ e.openAt ⟨s, r, w⟩ = q.2
  | 7 => ∃ s c w, e.support s = p.1 ∧ e.claim c = q.1 ∧ e.holdsAt ⟨s, c, w⟩ = q.2
  | 8 => ∃ s w, e.support s = p.1 ∧ e.obstructionAt ⟨s, w⟩ = p.2
  | 9 => ∃ s c d w, e.support s = p.1 ∧ e.claim c = q.1 ∧ e.claim d = t.1 ∧
      e.semanticChangeAt ⟨s, c, d, w⟩ = t.2
  | 10 => ∃ s w, e.support s = p.1 ∧ e.dispositionAt ⟨s, .transfer, w⟩ = p.2
  | 11 => ∃ s w, e.support s = p.1 ∧ e.dispositionAt ⟨s, .supportSettlement, w⟩ = p.2
  | 12 => ∃ s w, e.support s = p.1 ∧ e.dispositionAt ⟨s, .lawSurfaceExtension, w⟩ = p.2
  | 13 => ∃ s, e.support s = p.1 ∧ e.anchor (N.anchorAt s) = p.2
  | 14 => ∃ s, e.support s = p.1 ∧ e.incidence (N.incidenceAt s) = p.2
  | 15 => ∃ s, e.support s = p.1 ∧ e.lineage (N.lineageAt s) = p.2
  | 16 => ∃ s r w, e.support s = p.1 ∧ e.responsibility r = q.1 ∧
      e.openAt ⟨s, r, w⟩ = t.1 ∧ e.claim (N.openClaimAt w) = t.2
  | 17 => ∃ s w, e.support s = p.1 ∧ e.obstructionAt ⟨s, w⟩ = q.1 ∧
      e.claim (N.obstructionClaim w) = q.2
  | _ => False

def budgetRead (x : B) : ℝ :=
  let address := (MotherHigherLawFamily.unpair (MotherHigherLawFamily.unpair x).2).2
  if h : ∃ w, e.openAt w = address then
    (N.openProgressBudgetAt (Classical.choose h).2.2 : ℝ)
  else 0

def reader (x : B) (tag : Nat) : ℝ :=
  if tag = 18 then e.budgetRead x else if e.graph tag x then 0 else 1

theorem reader_bit {m : M} (hm : MotherHigherLawFormation.read m = e.reader)
    (tag : Nat) (other : tag ≠ 18) (x : B) : bit m tag x ↔ e.graph tag x := by
  simp only [bit, hm, reader, if_neg other]
  by_cases h : e.graph tag x <;> simp only [h, if_true, if_false, one_ne_zero, iff_self]

theorem budgetRead_encoded
    (s : N.Support) (r : N.Responsibility) (w : N.OpenAt s r) :
    e.budgetRead
      (MotherHigherLawFamily.pair (e.support s,
        MotherHigherLawFamily.pair (e.responsibility r, e.openAt ⟨s, r, w⟩))) =
      (N.openProgressBudgetAt w : ℝ) := by
  unfold budgetRead
  dsimp only
  split
  · rename_i found
    have same : Classical.choose found = ⟨s, r, w⟩ := by
      apply e.openAt.injective
      simpa only [MotherHigherLawFamily.unpair_pair] using Classical.choose_spec found
    exact congrArg (fun a : Σ s r, N.OpenAt s r => (N.openProgressBudgetAt a.2.2 : ℝ)) same
  · rename_i absent
    exact False.elim (absent ⟨⟨s, r, w⟩, by simp only [MotherHigherLawFamily.unpair_pair]⟩)

theorem reader_budget {m : M} (hm : MotherHigherLawFormation.read m = e.reader)
    (s : N.Support) (r : N.Responsibility) (w : N.OpenAt s r) :
    Nat.floor (MotherHigherLawFormation.read m
      (MotherHigherLawFamily.pair (e.support s,
        MotherHigherLawFamily.pair (e.responsibility r, e.openAt ⟨s, r, w⟩))) 18) =
      N.openProgressBudgetAt w := by
  simp only [hm, reader, ite_true, e.budgetRead_encoded, Nat.floor_natCast]

end Encoding

def imageEquiv {A : Type} (encode : A ↪ B) (p : B → Prop)
    (complete : ∀ b, p b ↔ ∃ a, encode a = b) : A ≃ {b // p b} :=
  Equiv.ofBijective (fun a => ⟨encode a, (complete _).mpr ⟨a, rfl⟩⟩) ⟨
    fun _ _ same => encode.injective (congrArg Subtype.val same),
    fun b => by obtain ⟨a, ha⟩ := (complete b.val).mp b.property; exact ⟨a, Subtype.ext ha⟩⟩

@[simp] theorem imageEquiv_val {A : Type} (encode : A ↪ B) (p : B → Prop)
    (complete : ∀ b, p b ↔ ∃ a, encode a = b) (a : A) :
    (imageEquiv encode p complete a).val = encode a := rfl


theorem Encoding.realizes {N : WorldRelationNetwork.{0}} (e : Encoding N)
    {m : M} (hm : MotherHigherLawFormation.read m = e.reader) :
    Nonempty (Factory.Realizes m N) := by
  let support : N.Support ≃ Support m := imageEquiv e.support (bit m 0)
    (fun b => by simpa only [Encoding.graph] using e.reader_bit hm 0 (by decide) b)
  let anchor : N.Anchor ≃ Anchor m := imageEquiv e.anchor (bit m 1)
    (fun b => by simpa only [Encoding.graph] using e.reader_bit hm 1 (by decide) b)
  let incidence : N.Incidence ≃ Incidence m := imageEquiv e.incidence (bit m 2)
    (fun b => by simpa only [Encoding.graph] using e.reader_bit hm 2 (by decide) b)
  let lineage : N.Lineage ≃ Lineage m := imageEquiv e.lineage (bit m 3)
    (fun b => by simpa only [Encoding.graph] using e.reader_bit hm 3 (by decide) b)
  let responsibility : N.Responsibility ≃ Responsibility m := imageEquiv e.responsibility (bit m 4)
    (fun b => by simpa only [Encoding.graph] using e.reader_bit hm 4 (by decide) b)
  let claim : N.Claim ≃ Claim m := imageEquiv e.claim (bit m 5)
    (fun b => by simpa only [Encoding.graph] using e.reader_bit hm 5 (by decide) b)
  let openCode (s : N.Support) (r : N.Responsibility) : N.OpenAt s r ↪ B :=
    ((Function.Embedding.sigmaMk (β := N.OpenAt s) r).trans
      (Function.Embedding.sigmaMk (β := fun t => Σ a, N.OpenAt t a) s)).trans e.openAt
  let openAt (s : N.Support) (r : N.Responsibility) :
      N.OpenAt s r ≃ OpenAt m (support s) (responsibility r) :=
    imageEquiv (openCode s r) (fun b => r3 m 6 (support s).val (responsibility r).val b) (by
      intro b
      rw [r3, e.reader_bit hm 6 (by decide)]
      simp only [Encoding.graph, MotherHigherLawFamily.unpair_pair]
      change (∃ s' r' w, e.support s' = e.support s ∧ e.responsibility r' = e.responsibility r ∧
        e.openAt ⟨s', r', w⟩ = b) ↔ ∃ w, e.openAt ⟨s, r, w⟩ = b
      constructor
      · rintro ⟨s', r', w, hs, hr, hw⟩
        have hs := e.support.injective hs
        have hr := e.responsibility.injective hr
        cases hs; cases hr
        exact ⟨w, hw⟩
      · rintro ⟨w, hw⟩
        exact ⟨s, r, w, rfl, rfl, hw⟩)
  let holdsCode (s : N.Support) (c : N.Claim) : N.HoldsAt s c ↪ B :=
    ((Function.Embedding.sigmaMk (β := N.HoldsAt s) c).trans
      (Function.Embedding.sigmaMk (β := fun t => Σ a, N.HoldsAt t a) s)).trans e.holdsAt
  let holdsAt (s : N.Support) (c : N.Claim) : N.HoldsAt s c ≃ HoldsAt m (support s) (claim c) :=
    imageEquiv (holdsCode s c) (fun b => r3 m 7 (support s).val (claim c).val b) (by
      intro b
      rw [r3, e.reader_bit hm 7 (by decide)]
      simp only [Encoding.graph, MotherHigherLawFamily.unpair_pair]
      change (∃ s' c' w, e.support s' = e.support s ∧ e.claim c' = e.claim c ∧
        e.holdsAt ⟨s', c', w⟩ = b) ↔ ∃ w, e.holdsAt ⟨s, c, w⟩ = b
      constructor
      · rintro ⟨s', c', w, hs, hc, hw⟩
        have hs := e.support.injective hs
        have hc := e.claim.injective hc
        cases hs; cases hc
        exact ⟨w, hw⟩
      · rintro ⟨w, hw⟩
        exact ⟨s, c, w, rfl, rfl, hw⟩)
  let obstructionCode (s : N.Support) : N.ObstructionAt s ↪ B :=
    (Function.Embedding.sigmaMk (β := N.ObstructionAt) s).trans e.obstructionAt
  let obstructionAt (s : N.Support) : N.ObstructionAt s ≃ ObstructionAt m (support s) :=
    imageEquiv (obstructionCode s) (fun b => r2 m 8 (support s).val b) (by
      intro b
      rw [r2, e.reader_bit hm 8 (by decide)]
      simp only [Encoding.graph, MotherHigherLawFamily.unpair_pair]
      change (∃ s' w, e.support s' = e.support s ∧ e.obstructionAt ⟨s', w⟩ = b) ↔
        ∃ w, e.obstructionAt ⟨s, w⟩ = b
      constructor
      · rintro ⟨s', w, hs, hw⟩
        have hs := e.support.injective hs
        cases hs
        exact ⟨w, hw⟩
      · rintro ⟨w, hw⟩
        exact ⟨s, w, rfl, hw⟩)
  let semanticCode (s : N.Support) (c d : N.Claim) : N.SemanticChangeAt s c d ↪ B :=
    (((Function.Embedding.sigmaMk (β := N.SemanticChangeAt s c) d).trans
      (Function.Embedding.sigmaMk (β := fun a => Σ b, N.SemanticChangeAt s a b) c)).trans
      (Function.Embedding.sigmaMk (β := fun t => Σ a b, N.SemanticChangeAt t a b) s)).trans e.semanticChangeAt
  let semanticAt (s : N.Support) (c d : N.Claim) :
      N.SemanticChangeAt s c d ≃ SemanticChangeAt m (support s) (claim c) (claim d) :=
    imageEquiv (semanticCode s c d) (fun b => r4 m 9 (support s).val (claim c).val (claim d).val b) (by
      intro b
      rw [r4, e.reader_bit hm 9 (by decide)]
      simp only [Encoding.graph, MotherHigherLawFamily.unpair_pair]
      change (∃ s' c' d' w, e.support s' = e.support s ∧ e.claim c' = e.claim c ∧
        e.claim d' = e.claim d ∧ e.semanticChangeAt ⟨s', c', d', w⟩ = b) ↔
        ∃ w, e.semanticChangeAt ⟨s, c, d, w⟩ = b
      constructor
      · rintro ⟨s', c', d', w, hs, hc, hd, hw⟩
        have hs := e.support.injective hs
        have hc := e.claim.injective hc
        have hd := e.claim.injective hd
        cases hs; cases hc; cases hd
        exact ⟨w, hw⟩
      · rintro ⟨w, hw⟩
        exact ⟨s, c, d, w, rfl, rfl, rfl, hw⟩)
  let dispositionCode (s : N.Support) (k : WorldDispositionKind) : N.DispositionAt s k ↪ B :=
    ((Function.Embedding.sigmaMk (β := N.DispositionAt s) k).trans
      (Function.Embedding.sigmaMk (β := fun t => Σ a, N.DispositionAt t a) s)).trans e.dispositionAt
  let dispositionAt (s : N.Support) (k : WorldDispositionKind) :
      N.DispositionAt s k ≃ DispositionAt m (support s) k :=
    imageEquiv (dispositionCode s k) (fun b => r2 m (dispositionTag k) (support s).val b) (by
      intro b
      rw [r2, e.reader_bit hm (dispositionTag k) (by cases k <;> decide)]
      have shape : e.graph (dispositionTag k) (MotherHigherLawFamily.pair ((support s).val, b)) ↔
          ∃ s' w, e.support s' = e.support s ∧ e.dispositionAt ⟨s', k, w⟩ = b := by
        cases k <;> simp only [dispositionTag, Encoding.graph, MotherHigherLawFamily.unpair_pair]
        <;> rfl
      rw [shape]
      change (∃ s' w, e.support s' = e.support s ∧ e.dispositionAt ⟨s', k, w⟩ = b) ↔
        ∃ w, e.dispositionAt ⟨s, k, w⟩ = b
      constructor
      · rintro ⟨s', w, hs, hw⟩
        have hs := e.support.injective hs
        cases hs
        exact ⟨w, hw⟩
      · rintro ⟨w, hw⟩
        exact ⟨s, w, rfl, hw⟩)
  refine ⟨{
    support := support, anchor := anchor, incidence := incidence, lineage := lineage,
    responsibility := responsibility, claim := claim, openAt := openAt, holdsAt := holdsAt,
    obstructionAt := obstructionAt, semanticChangeAt := semanticAt, dispositionAt := dispositionAt,
    anchor_graph := ?_, incidence_graph := ?_, lineage_graph := ?_, openClaim_graph := ?_,
    obstructionClaim_graph := ?_, budget_eq := ?_ }⟩
  · intro s a
    rw [r2, e.reader_bit hm 13 (by decide)]
    simp only [Encoding.graph, MotherHigherLawFamily.unpair_pair]
    change (∃ s', e.support s' = e.support s ∧ e.anchor (N.anchorAt s') = a.val) ↔
      a = anchor (N.anchorAt s)
    constructor
    · rintro ⟨s', hs, ha⟩
      have hs := e.support.injective hs
      cases hs
      exact Subtype.ext ha.symm
    · intro ha
      cases ha
      exact ⟨s, rfl, rfl⟩
  · intro s a
    rw [r2, e.reader_bit hm 14 (by decide)]
    simp only [Encoding.graph, MotherHigherLawFamily.unpair_pair]
    change (∃ s', e.support s' = e.support s ∧ e.incidence (N.incidenceAt s') = a.val) ↔
      a = incidence (N.incidenceAt s)
    constructor
    · rintro ⟨s', hs, ha⟩
      have hs := e.support.injective hs
      cases hs
      exact Subtype.ext ha.symm
    · intro ha
      cases ha
      exact ⟨s, rfl, rfl⟩
  · intro s a
    rw [r2, e.reader_bit hm 15 (by decide)]
    simp only [Encoding.graph, MotherHigherLawFamily.unpair_pair]
    change (∃ s', e.support s' = e.support s ∧ e.lineage (N.lineageAt s') = a.val) ↔
      a = lineage (N.lineageAt s)
    constructor
    · rintro ⟨s', hs, ha⟩
      have hs := e.support.injective hs
      cases hs
      exact Subtype.ext ha.symm
    · intro ha
      cases ha
      exact ⟨s, rfl, rfl⟩
  · intro s r w c
    rw [r4, e.reader_bit hm 16 (by decide)]
    simp only [Encoding.graph, MotherHigherLawFamily.unpair_pair]
    change (∃ s' r' w', e.support s' = e.support s ∧ e.responsibility r' = e.responsibility r ∧
      e.openAt ⟨s', r', w'⟩ = e.openAt ⟨s, r, w⟩ ∧ e.claim (N.openClaimAt w') = c.val) ↔
      c = claim (N.openClaimAt w)
    constructor
    · rintro ⟨s', r', w', hs, hr, hw, hc⟩
      have hs := e.support.injective hs
      have hr := e.responsibility.injective hr
      cases hs; cases hr
      have hw : w' = w := (openCode s r).injective hw
      cases hw
      exact Subtype.ext hc.symm
    · intro hc
      cases hc
      exact ⟨s, r, w, rfl, rfl, rfl, rfl⟩
  · intro s w c
    rw [r3, e.reader_bit hm 17 (by decide)]
    simp only [Encoding.graph, MotherHigherLawFamily.unpair_pair]
    change (∃ s' w', e.support s' = e.support s ∧
      e.obstructionAt ⟨s', w'⟩ = e.obstructionAt ⟨s, w⟩ ∧ e.claim (N.obstructionClaim w') = c.val) ↔
      c = claim (N.obstructionClaim w)
    constructor
    · rintro ⟨s', w', hs, hw, hc⟩
      have hs := e.support.injective hs
      cases hs
      have hw : w' = w := (obstructionCode s).injective hw
      cases hw
      exact Subtype.ext hc.symm
    · intro hc
      cases hc
      exact ⟨s, w, rfl, rfl, rfl⟩
  · intro s r w
    exact e.reader_budget hm s r w

theorem every_embedded_network (N : WorldRelationNetwork.{0}) (encode : Encoding N) :
    ∃ m : M, ∃ generated : WorldRelationNetwork.{0},
      formNetwork m = some generated ∧ Nonempty (Presentation N generated) := by
  obtain ⟨m, hm⟩ := MotherHigherLawFormation.read_surjective encode.reader
  obtain ⟨realizes⟩ := encode.realizes hm
  exact ⟨m, realizes.formed⟩

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherNetworkOrigin
