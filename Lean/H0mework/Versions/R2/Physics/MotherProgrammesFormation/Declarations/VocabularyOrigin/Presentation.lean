import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.VocabularyOrigin.Factory

set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherVocabularyOrigin
open MotherNetworkFactory
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
noncomputable section

structure Presentation (V W : Vocabulary.{0}) where
  current : V.Current ≃ W.Current
  anchor : V.Anchor ≃ W.Anchor
  incidence : V.Incidence ≃ W.Incidence
  lineage : V.Lineage ≃ W.Lineage
  native : ∀ c, V.NativeWriteAt c ≃ W.NativeWriteAt (current c)
  relation : ∀ c, V.RelationWriteAt c ≃ W.RelationWriteAt (current c)
  continued : ∀ c, V.ContinuedTransportAt c ≃ W.ContinuedTransportAt (current c)
  redirect : ∀ c, V.BorromeanRedirectAt c ≃ W.BorromeanRedirectAt (current c)
  terminal : ∀ c, V.FaithfulTerminalAt c ≃ W.FaithfulTerminalAt (current c)
  cofinal : V.cofinal.Event ≃ W.cofinal.Event
  anchor_eq : ∀ c, W.anchorAt (current c) = anchor (V.anchorAt c)
  incidence_eq : ∀ c, W.incidenceAt (current c) = incidence (V.incidenceAt c)
  lineage_eq : ∀ c, W.lineageAt (current c) = lineage (V.lineageAt c)
  native_eq : ∀ c w, W.nativeTarget (native c w) = current (V.nativeTarget w)
  relation_eq : ∀ c w, W.relationTarget (relation c w) = current (V.relationTarget w)
  continued_eq : ∀ c w, W.continuedTarget (continued c w) = current (V.continuedTarget w)
  redirect_eq : ∀ c w, W.redirectTarget (redirect c w) = current (V.redirectTarget w)
  cofinal_emit : Option.map cofinal V.cofinal.emit? = W.cofinal.emit?
  cofinal_path : ∀ e n, W.cofinal.pathAt (cofinal e) n = current (V.cofinal.pathAt e n)
  cofinal_target : ∀ e, W.cofinal.target (cofinal e) = current (V.cofinal.target e)

namespace Coverage

/-- Internal assembly evidence. The source factory does not receive it. -/
structure Realizes (m : M) (V : Vocabulary.{0}) where
  current : V.Current ≃ Current m
  anchor : V.Anchor ≃ Anchor m
  incidence : V.Incidence ≃ Incidence m
  lineage : V.Lineage ≃ Lineage m
  native : ∀ c, V.NativeWriteAt c ≃ Native m (current c)
  relation : ∀ c, V.RelationWriteAt c ≃ Relation m (current c)
  continued : ∀ c, V.ContinuedTransportAt c ≃ Continued m (current c)
  redirect : ∀ c, V.BorromeanRedirectAt c ≃ Redirect m (current c)
  terminal : ∀ c, V.FaithfulTerminalAt c ≃ Terminal m (current c)
  cofinal : V.cofinal.Event ≃ CofinalEvent m
  anchor_graph : ∀ c a, r2 m 10 (current c).val a.val ↔ a = anchor (V.anchorAt c)
  incidence_graph : ∀ c a, r2 m 11 (current c).val a.val ↔ a = incidence (V.incidenceAt c)
  lineage_graph : ∀ c a, r2 m 12 (current c).val a.val ↔ a = lineage (V.lineageAt c)
  native_graph : ∀ c w t, r3 m 13 (current c).val (native c w).val t.val ↔ t = current (V.nativeTarget w)
  relation_graph : ∀ c w t, r3 m 14 (current c).val (relation c w).val t.val ↔ t = current (V.relationTarget w)
  continued_graph : ∀ c w t, r3 m 15 (current c).val (continued c w).val t.val ↔ t = current (V.continuedTarget w)
  redirect_graph : ∀ c w t, r3 m 16 (current c).val (redirect c w).val t.val ↔ t = current (V.redirectTarget w)
  cofinal_target_graph : ∀ e t, r2 m 17 (cofinal e).val t.val ↔ t = current (V.cofinal.target e)
  cofinal_emit_graph : ∀ e, bit m 18 (cofinal e).val ↔ V.cofinal.emit? = some e
  cofinal_path_graph : ∀ e n t, r2 m (20 + n) (cofinal e).val t.val ↔ t = current (V.cofinal.pathAt e n)

theorem Realizes.check {m : M} {V : Vocabulary.{0}} (r : Realizes m V) : Check m where
  anchor := by
    intro c
    obtain ⟨c, rfl⟩ := r.current.surjective c
    exact ⟨_, (r.anchor_graph c _).mpr rfl, fun a h => (r.anchor_graph c a).mp h⟩
  incidence := by
    intro c
    obtain ⟨c, rfl⟩ := r.current.surjective c
    exact ⟨_, (r.incidence_graph c _).mpr rfl, fun a h => (r.incidence_graph c a).mp h⟩
  lineage := by
    intro c
    obtain ⟨c, rfl⟩ := r.current.surjective c
    exact ⟨_, (r.lineage_graph c _).mpr rfl, fun a h => (r.lineage_graph c a).mp h⟩
  nativeTarget := by
    intro c w
    obtain ⟨c, rfl⟩ := r.current.surjective c
    obtain ⟨w, rfl⟩ := (r.native c).surjective w
    exact ⟨_, (r.native_graph c w _).mpr rfl, fun t h => (r.native_graph c w t).mp h⟩
  relationTarget := by
    intro c w
    obtain ⟨c, rfl⟩ := r.current.surjective c
    obtain ⟨w, rfl⟩ := (r.relation c).surjective w
    exact ⟨_, (r.relation_graph c w _).mpr rfl, fun t h => (r.relation_graph c w t).mp h⟩
  continuedTarget := by
    intro c w
    obtain ⟨c, rfl⟩ := r.current.surjective c
    obtain ⟨w, rfl⟩ := (r.continued c).surjective w
    exact ⟨_, (r.continued_graph c w _).mpr rfl, fun t h => (r.continued_graph c w t).mp h⟩
  redirectTarget := by
    intro c w
    obtain ⟨c, rfl⟩ := r.current.surjective c
    obtain ⟨w, rfl⟩ := (r.redirect c).surjective w
    exact ⟨_, (r.redirect_graph c w _).mpr rfl, fun t h => (r.redirect_graph c w t).mp h⟩
  cofinalTarget := by
    intro e
    obtain ⟨e, rfl⟩ := r.cofinal.surjective e
    exact ⟨_, (r.cofinal_target_graph e _).mpr rfl, fun t h => (r.cofinal_target_graph e t).mp h⟩
  cofinalPath := by
    intro e n
    obtain ⟨e, rfl⟩ := r.cofinal.surjective e
    exact ⟨_, (r.cofinal_path_graph e n _).mpr rfl, fun t h => (r.cofinal_path_graph e n t).mp h⟩
  cofinalEmit := by
    intro e f he hf
    obtain ⟨e, rfl⟩ := r.cofinal.surjective e
    obtain ⟨f, rfl⟩ := r.cofinal.surjective f
    exact congrArg r.cofinal (Option.some.inj (((r.cofinal_emit_graph e).mp he).symm.trans
      ((r.cofinal_emit_graph f).mp hf)))

theorem Realizes.emit_eq {m : M} {V : Vocabulary.{0}} (r : Realizes m V) :
    Option.map r.cofinal V.cofinal.emit? = emitted? m := by
  cases selected : V.cofinal.emit? with
  | none =>
      have absent : emitted? m = none := by
        cases generated : emitted? m with
        | none => rfl
        | some e =>
            obtain ⟨e, rfl⟩ := r.cofinal.surjective e
            have impossible := (r.cofinal_emit_graph e).mp (emitted_selected m _ generated)
            rw [selected] at impossible
            cases impossible
      exact absent.symm
  | some e => exact (selected_emitted m r.check (r.cofinal e) ((r.cofinal_emit_graph e).mpr selected)).symm

theorem Realizes.formed {m : M} {V : Vocabulary.{0}} (r : Realizes m V) :
    ∃ W : Vocabulary.{0}, formVocabulary m = some W ∧ Nonempty (Presentation V W) := by
  refine ⟨_, MotherVocabularyOrigin.formed m r.check, ⟨?_⟩⟩
  exact {
    current := r.current, anchor := r.anchor, incidence := r.incidence, lineage := r.lineage,
    native := r.native, relation := r.relation, continued := r.continued, redirect := r.redirect,
    terminal := r.terminal, cofinal := r.cofinal,
    anchor_eq := fun c => (r.anchor_graph c _).mp (Classical.choose_spec (r.check.anchor _)).1,
    incidence_eq := fun c => (r.incidence_graph c _).mp (Classical.choose_spec (r.check.incidence _)).1,
    lineage_eq := fun c => (r.lineage_graph c _).mp (Classical.choose_spec (r.check.lineage _)).1,
    native_eq := fun c w => (r.native_graph c w _).mp (Classical.choose_spec (r.check.nativeTarget _ _)).1,
    relation_eq := fun c w => (r.relation_graph c w _).mp (Classical.choose_spec (r.check.relationTarget _ _)).1,
    continued_eq := fun c w => (r.continued_graph c w _).mp (Classical.choose_spec (r.check.continuedTarget _ _)).1,
    redirect_eq := fun c w => (r.redirect_graph c w _).mp (Classical.choose_spec (r.check.redirectTarget _ _)).1,
    cofinal_emit := r.emit_eq,
    cofinal_path := fun e n => (r.cofinal_path_graph e n _).mp (Classical.choose_spec (r.check.cofinalPath _ _)).1,
    cofinal_target := fun e => (r.cofinal_target_graph e _).mp (Classical.choose_spec (r.check.cofinalTarget _)).1 }

end Coverage
end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherVocabularyOrigin
