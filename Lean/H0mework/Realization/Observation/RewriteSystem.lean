/-
  Proposition 18: Newman's lemma for terminating rewrite systems.

  Proposition 17 isolated the graph H¹-like generator under an explicit graph
  gluing certificate.  This file supplies the missing generic rewrite-theory
  theorem behind that certificate: if a rewrite relation is terminating and
  locally confluent, then it is confluent.

  The theorem is intentionally stated for an arbitrary relation.  The concrete
  graph runtime still has to instantiate the relation, prove termination, and
  prove local confluence / cross-boundary local confluence for its critical
  pairs.
-/

import H0mework.Realization.Observation.LocalMaximality

open Relation

/-! ## Generic rewrite terminology -/

/-- Reflexive-transitive rewrite reachability. -/
abbrev RewriteStar {α : Type*} (r : α → α → Prop) : α → α → Prop :=
  ReflTransGen r

/-- Two states are joinable when they rewrite to a common successor. -/
def Joinable {α : Type*} (r : α → α → Prop) (a b : α) : Prop :=
  Relation.Join (RewriteStar r) a b

/-- Local confluence: every one-step fork is joinable. -/
def LocallyConfluent {α : Type*} (r : α → α → Prop) : Prop :=
  ∀ a b c, r a b → r a c → Joinable r b c

/-- Confluence at a source state. -/
def ConfluentAt {α : Type*} (r : α → α → Prop) (a : α) : Prop :=
  ∀ b c, RewriteStar r a b → RewriteStar r a c → Joinable r b c

/-- Confluence: every finite fork is joinable. -/
def Confluent {α : Type*} (r : α → α → Prop) : Prop :=
  ∀ a, ConfluentAt r a

/-- Termination / strong normalization: no infinite forward rewrite chain.
    This is the well-foundedness condition used by Newman. -/
def Terminating {α : Type*} (r : α → α → Prop) : Prop :=
  WellFounded (flip r)

/-! ## Path decomposition helpers -/

/-- Joinability is symmetric. -/
theorem joinable_symm {α : Type*} {r : α → α → Prop} {a b : α}
    (h : Joinable r a b) : Joinable r b a := by
  rcases h with ⟨c, hac, hbc⟩
  exact ⟨c, hbc, hac⟩

/-- If the left side of a fork is the source itself, the fork is joinable by
    choosing the right endpoint. -/
theorem joinable_of_left_refl {α : Type*} {r : α → α → Prop}
    {a c : α} (hac : RewriteStar r a c) : Joinable r a c := by
  exact ⟨c, hac, ReflTransGen.refl⟩

/-- If the right side of a fork is the source itself, the fork is joinable by
    choosing the left endpoint. -/
theorem joinable_of_right_refl {α : Type*} {r : α → α → Prop}
    {a b : α} (hab : RewriteStar r a b) : Joinable r b a := by
  exact ⟨b, ReflTransGen.refl, hab⟩

/-- Transitivity on the left leg of a join. -/
theorem joinable.trans_left {α : Type*} {r : α → α → Prop}
    {a b c : α} (hab : RewriteStar r a b) (hbc : Joinable r b c) :
    Joinable r a c := by
  rcases hbc with ⟨d, hbd, hcd⟩
  exact ⟨d, hab.trans hbd, hcd⟩

/-! ## Newman induction -/

/-- The induction step used by Newman's lemma: assuming confluence for every
    immediate successor of `a`, local confluence at `a` upgrades finite forks
    out of `a` to joinability. -/
theorem newman_induction_step {α : Type*} {r : α → α → Prop}
    (hlocal : LocallyConfluent r) (a : α)
    (ih : ∀ y, r a y → ConfluentAt r y) :
    ConfluentAt r a := by
  intro b c hab hac
  rcases ReflTransGen.cases_head hab with rfl | ⟨b₁, hab₁, hb₁b⟩
  · exact joinable_of_left_refl hac
  rcases ReflTransGen.cases_head hac with rfl | ⟨c₁, hac₁, hc₁c⟩
  · exact joinable_of_right_refl hab
  rcases hlocal a b₁ c₁ hab₁ hac₁ with ⟨d, hb₁d, hc₁d⟩
  rcases ih b₁ hab₁ b d hb₁b hb₁d with ⟨e, hbe, hde⟩
  have hc₁e : RewriteStar r c₁ e := hc₁d.trans hde
  rcases ih c₁ hac₁ c e hc₁c hc₁e with ⟨f, hcf, hef⟩
  exact ⟨f, hbe.trans hef, hcf⟩

/-- NEWMAN'S LEMMA: on a terminating rewrite relation, local confluence implies
    confluence. -/
theorem newman {α : Type*} {r : α → α → Prop}
    (hterm : Terminating r) (hlocal : LocallyConfluent r) :
    Confluent r := by
  intro a
  exact hterm.induction a (fun x ih =>
    newman_induction_step hlocal x ih)

/-! ## Critical-pair certificate form -/

/-- A certificate that reduces local confluence to a named family of critical
    forks.  In a concrete graph runtime, `critical` can be instantiated by
    ordinary local critical pairs plus cross-boundary critical pairs. -/
structure CriticalPairCertificate {α : Type*} (r : α → α → Prop) where
  critical : α → α → α → Prop
  covers : ∀ a b c, r a b → r a c → critical a b c
  joinable : ∀ a b c, critical a b c → Joinable r b c

/-- THEOREM 2: a critical-pair certificate implies local confluence. -/
theorem locallyConfluent_of_criticalPairCertificate {α : Type*}
    {r : α → α → Prop} (cert : CriticalPairCertificate r) :
    LocallyConfluent r := by
  intro a b c hab hac
  exact cert.joinable a b c (cert.covers a b c hab hac)

/-- THEOREM 3: Newman's lemma in critical-pair certificate form. -/
theorem newman_of_criticalPairCertificate {α : Type*}
    {r : α → α → Prop}
    (hterm : Terminating r) (cert : CriticalPairCertificate r) :
    Confluent r :=
  newman hterm (locallyConfluent_of_criticalPairCertificate cert)

/-! ## Graph-gluing reading of Newman -/

/-- A graph rewrite confluence certificate generated by Newman.  It packages
    the exact obligations a graph runtime must discharge: termination plus a
    critical-pair certificate for its chosen rewrite relation. -/
structure NewmanGraphConfluenceCertificate (Graph : Type*) where
  step : Graph → Graph → Prop
  terminating : Terminating step
  criticalPairs : CriticalPairCertificate step

/-- THEOREM 4: a Newman graph certificate yields graph confluence. -/
theorem graph_confluent_of_newman_certificate {Graph : Type*}
    (cert : NewmanGraphConfluenceCertificate Graph) :
    Confluent cert.step :=
  newman_of_criticalPairCertificate cert.terminating cert.criticalPairs

/-!
  Summary:
  - `newman` is the full abstract Newman theorem:
    `Terminating r -> LocallyConfluent r -> Confluent r`.
  - The proof uses well-founded induction on the fork source and the standard
    two-head decomposition of reflexive-transitive rewrite paths.
  - `newman_of_criticalPairCertificate` is the runtime-facing form: instantiate
    a critical-pair family, prove it covers one-step forks, and prove its
    members joinable.
  - Graph-specific work remains: instantiate `step`, prove termination, and
    fill `criticalPairs` with local + cross-boundary critical-pair joinability.
-/
