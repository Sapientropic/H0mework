import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.Cumulative.ArenaSource.Factory

set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherArenaSource.AccountEncoding
open MotherArenaNetwork
open ResponsibilityLifecycle.LivingLawEvolution
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open scoped Classical
noncomputable section
variable {rank : Ordinal.{0}}
local notation "B" => MotherArenaHigher.Base rank
local notation "M" => MotherArenaHigher.Material rank

variable {net base events : MotherArenaHigher.Material rank} {hn : MotherArenaNetwork.Check net}
    {hv : MotherArenaVocabulary.Check base} {ha : MotherArenaActual.Check base events hv}
    {OriginalN : WorldRelationNetwork.{0}} {OriginalV : Vocabulary.{0}}
    (n : MotherNetworkOrigin.Presentation OriginalN (network net hn))
    (v : MotherArenaVocabulary.Presentation OriginalV (MotherArenaActual.V base hv))
    (source : Source OriginalN OriginalV)
    (a : MotherArenaActual.Presentation v source.actual (MotherArenaActual.actual base events hv ha))

def graph (tag : Nat) (code : B) : Prop :=
  let pair := (MotherArenaHigher.unpair rank) code
  let tail := (MotherArenaHigher.unpair rank) pair.2
  match tag with
  | 0 => ∃ c e, (v.current c).val = pair.1 ∧ (a.event c e).val = tail.1 ∧
      (n.support (source.account.supportOf e)).val = tail.2
  | 1 => ∃ x, (v.anchor x).val = pair.1 ∧ (n.anchor (source.account.anchorKey x)).val = pair.2
  | 2 => ∃ x, (v.incidence x).val = pair.1 ∧ (n.incidence (source.account.incidenceKey x)).val = pair.2
  | 3 => ∃ x, (v.lineage x).val = pair.1 ∧ (n.lineage (source.account.lineageKey x)).val = pair.2
  | 4 => (v.current source.initial).val = code
  | _ => False

def reader (code : B) (tag : Nat) : ℝ := if graph n v source a tag code then 0 else 1

theorem reader_bit {fields : M} (hm : (MotherArenaHigher.read rank) fields = reader n v source a)
    (tag : Nat) (code : B) : bit fields tag code ↔ graph n v source a tag code := by
  by_cases seen : graph n v source a tag code <;>
    simp only [bit, hm, reader, seen, if_true, if_false, one_ne_zero, iff_self]

theorem initial_at {fields : M} (hm : (MotherArenaHigher.read rank) fields = reader n v source a)
    (c : MotherArenaVocabulary.Current base) : bit fields 4 c.val ↔ c = v.current source.initial := by
  rw [reader_bit n v source a hm]
  change (v.current source.initial).val = c.val ↔ c = v.current source.initial
  constructor
  · intro same
    exact Subtype.ext same.symm
  · intro same
    cases same
    rfl

theorem support_at {fields : M} (hm : (MotherArenaHigher.read rank) fields = reader n v source a)
    (c : OriginalV.Current) (event : source.actual.OccurrenceAt c) (s : Support net) :
    r3 fields 0 (v.current c).val (a.event c event).val s.val ↔ s = n.support (source.account.supportOf event) := by
  rw [r3, reader_bit n v source a hm]
  simp only [graph, (MotherArenaHigher.unpair_pair rank)]
  constructor
  · rintro ⟨c', e, hc, he, hs⟩
    have same := v.current.injective (Subtype.ext hc)
    cases same
    have same := (a.event c).injective (Subtype.ext he)
    cases same
    exact Subtype.ext hs.symm
  · intro same
    cases same
    exact ⟨c, event, rfl, rfl, rfl⟩

theorem anchor_at {fields : M} (hm : (MotherArenaHigher.read rank) fields = reader n v source a)
    (x : OriginalV.Anchor) (t : Anchor net) :
    r2 fields 1 (v.anchor x).val t.val ↔ t = n.anchor (source.account.anchorKey x) := by
  rw [r2, reader_bit n v source a hm]
  simp only [graph, (MotherArenaHigher.unpair_pair rank)]
  constructor
  · rintro ⟨x', hx, ht⟩
    have same := v.anchor.injective (Subtype.ext hx)
    cases same
    exact Subtype.ext ht.symm
  · intro same
    cases same
    exact ⟨x, rfl, rfl⟩

theorem incidence_at {fields : M} (hm : (MotherArenaHigher.read rank) fields = reader n v source a)
    (x : OriginalV.Incidence) (t : Incidence net) :
    r2 fields 2 (v.incidence x).val t.val ↔ t = n.incidence (source.account.incidenceKey x) := by
  rw [r2, reader_bit n v source a hm]
  simp only [graph, (MotherArenaHigher.unpair_pair rank)]
  constructor
  · rintro ⟨x', hx, ht⟩
    have same := v.incidence.injective (Subtype.ext hx)
    cases same
    exact Subtype.ext ht.symm
  · intro same
    cases same
    exact ⟨x, rfl, rfl⟩

theorem lineage_at {fields : M} (hm : (MotherArenaHigher.read rank) fields = reader n v source a)
    (x : OriginalV.Lineage) (t : Lineage net) :
    r2 fields 3 (v.lineage x).val t.val ↔ t = n.lineage (source.account.lineageKey x) := by
  rw [r2, reader_bit n v source a hm]
  simp only [graph, (MotherArenaHigher.unpair_pair rank)]
  constructor
  · rintro ⟨x', hx, ht⟩
    have same := v.lineage.injective (Subtype.ext hx)
    cases same
    exact Subtype.ext ht.symm
  · intro same
    cases same
    exact ⟨x, rfl, rfl⟩

theorem graphs {fields : M} (hm : (MotherArenaHigher.read rank) fields = reader n v source a) :
    AccountGraphs net base events fields where
  initial := ⟨v.current source.initial, (initial_at n v source a hm _).mpr rfl,
    fun c selected => (initial_at n v source a hm c).mp selected⟩
  support := by
    intro c e
    obtain ⟨c, rfl⟩ := v.current.surjective c
    obtain ⟨e, rfl⟩ := (a.event c).surjective e
    exact ⟨n.support (source.account.supportOf e), (support_at n v source a hm c e _).mpr rfl,
      fun s selected => (support_at n v source a hm c e s).mp selected⟩
  anchor := by
    intro x
    obtain ⟨x, rfl⟩ := v.anchor.surjective x
    exact ⟨n.anchor (source.account.anchorKey x), (anchor_at n v source a hm x _).mpr rfl,
      fun t selected => (anchor_at n v source a hm x t).mp selected⟩
  incidence := by
    intro x
    obtain ⟨x, rfl⟩ := v.incidence.surjective x
    exact ⟨n.incidence (source.account.incidenceKey x), (incidence_at n v source a hm x _).mpr rfl,
      fun t selected => (incidence_at n v source a hm x t).mp selected⟩
  lineage := by
    intro x
    obtain ⟨x, rfl⟩ := v.lineage.surjective x
    exact ⟨n.lineage (source.account.lineageKey x), (lineage_at n v source a hm x _).mpr rfl,
      fun t selected => (lineage_at n v source a hm x t).mp selected⟩

theorem initial_value {fields : M} (hm : (MotherArenaHigher.read rank) fields = reader n v source a) :
    Classical.choose (graphs n v source a hm).initial = v.current source.initial :=
  (initial_at n v source a hm _).mp (Classical.choose_spec (graphs n v source a hm).initial).1

theorem support_value {fields : M} (hm : (MotherArenaHigher.read rank) fields = reader n v source a)
    (c : OriginalV.Current) (event : source.actual.OccurrenceAt c) :
    Classical.choose ((graphs n v source a hm).support (v.current c) (a.event c event)) =
      n.support (source.account.supportOf event) :=
  (support_at n v source a hm c event _).mp
    (Classical.choose_spec ((graphs n v source a hm).support (v.current c) (a.event c event))).1

theorem anchor_value {fields : M} (hm : (MotherArenaHigher.read rank) fields = reader n v source a)
    (x : OriginalV.Anchor) :
    Classical.choose ((graphs n v source a hm).anchor (v.anchor x)) = n.anchor (source.account.anchorKey x) :=
  (anchor_at n v source a hm x _).mp
    (Classical.choose_spec ((graphs n v source a hm).anchor (v.anchor x))).1

theorem incidence_value {fields : M} (hm : (MotherArenaHigher.read rank) fields = reader n v source a)
    (x : OriginalV.Incidence) :
    Classical.choose ((graphs n v source a hm).incidence (v.incidence x)) = n.incidence (source.account.incidenceKey x) :=
  (incidence_at n v source a hm x _).mp
    (Classical.choose_spec ((graphs n v source a hm).incidence (v.incidence x))).1

theorem lineage_value {fields : M} (hm : (MotherArenaHigher.read rank) fields = reader n v source a)
    (x : OriginalV.Lineage) :
    Classical.choose ((graphs n v source a hm).lineage (v.lineage x)) = n.lineage (source.account.lineageKey x) :=
  (lineage_at n v source a hm x _).mp
    (Classical.choose_spec ((graphs n v source a hm).lineage (v.lineage x))).1

theorem compatible {fields : M} (hm : (MotherArenaHigher.read rank) fields = reader n v source a) :
    Compatible net base events fields hn hv (graphs n v source a hm) := by
  refine ⟨?_, ?_, ?_⟩
  · intro c event
    obtain ⟨c, rfl⟩ := v.current.surjective c
    obtain ⟨event, rfl⟩ := (a.event c).surjective event
    have indexEq := congrArg (fun x : MotherArenaVocabulary.Anchor base =>
      Classical.choose ((graphs n v source a hm).anchor x)) (v.anchor_eq c)
    exact indexEq.trans ((anchor_value n v source a hm (OriginalV.anchorAt c)).trans
      ((congrArg n.anchor (source.account.anchor_commutes event)).trans
        ((n.anchor_commutes (source.account.supportOf event)).symm.trans
          (congrArg (network net hn).anchorAt (support_value n v source a hm c event).symm))))
  · intro c event
    obtain ⟨c, rfl⟩ := v.current.surjective c
    obtain ⟨event, rfl⟩ := (a.event c).surjective event
    have indexEq := congrArg (fun x : MotherArenaVocabulary.Incidence base =>
      Classical.choose ((graphs n v source a hm).incidence x)) (v.incidence_eq c)
    exact indexEq.trans ((incidence_value n v source a hm (OriginalV.incidenceAt c)).trans
      ((congrArg n.incidence (source.account.incidence_commutes event)).trans
        ((n.incidence_commutes (source.account.supportOf event)).symm.trans
          (congrArg (network net hn).incidenceAt (support_value n v source a hm c event).symm))))
  · intro c event
    obtain ⟨c, rfl⟩ := v.current.surjective c
    obtain ⟨event, rfl⟩ := (a.event c).surjective event
    have indexEq := congrArg (fun x : MotherArenaVocabulary.Lineage base =>
      Classical.choose ((graphs n v source a hm).lineage x)) (v.lineage_eq c)
    exact indexEq.trans ((lineage_value n v source a hm (OriginalV.lineageAt c)).trans
      ((congrArg n.lineage (source.account.lineage_commutes event)).trans
        ((n.lineage_commutes (source.account.supportOf event)).symm.trans
          (congrArg (network net hn).lineageAt (support_value n v source a hm c event).symm))))

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherArenaSource.AccountEncoding
