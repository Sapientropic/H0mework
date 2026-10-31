import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Go.Strategy.ClosureGain

/-!
# Source-generated closure invariance

A source incidence equivalence carries two exact actual updates when it
preserves the finite source face and commutes with every generated relation
comparison.  Settled and debt images, hence closure gain equality, are
derived internally rather than accepted as target premises.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Go

open Obligation

universe u v

/-! ## Source-generated update equivalence -/

/-- Canonical transport of open/debt tags along an incidence equivalence. -/
def obligationKeyEquiv {Left : Type u} {Right : Type v}
    (incidenceEquiv : Left ≃ Right) :
    ObligationKey Left ≃ ObligationKey Right where
  toFun
    | .open incidence => .open (incidenceEquiv incidence)
    | .generatedDebt incidence => .generatedDebt (incidenceEquiv incidence)
  invFun
    | .open incidence => .open (incidenceEquiv.symm incidence)
    | .generatedDebt incidence => .generatedDebt (incidenceEquiv.symm incidence)
  left_inv := by intro key; cases key <;> simp
  right_inv := by intro key; cases key <;> simp

@[simp] theorem obligationKeyEquiv_open
    {Left : Type u} {Right : Type v} (incidenceEquiv : Left ≃ Right)
    (incidence : Left) :
    obligationKeyEquiv incidenceEquiv (ObligationKey.open incidence) =
      ObligationKey.open (incidenceEquiv incidence) :=
  rfl

@[simp] theorem obligationKeyEquiv_generatedDebt
    {Left : Type u} {Right : Type v} (incidenceEquiv : Left ≃ Right)
    (incidence : Left) :
    obligationKeyEquiv incidenceEquiv
        (ObligationKey.generatedDebt incidence) =
      ObligationKey.generatedDebt (incidenceEquiv incidence) :=
  rfl

/-- Two updates are generated-equivalent when one source incidence
equivalence carries the finite source face and every exact edge comparison.
No settled/debt/target set is accepted as a premise. -/
structure GeneratedClosureUpdateEquivalence
    {n : Nat} {law : Law} {moves : List (Move n)}
    {replay : GeneratedReplay law (Frame.initial n) moves}
    {LeftIncidence : Type u} {RightIncidence : Type v}
    [DecidableEq LeftIncidence] [DecidableEq RightIncidence]
    (leftFace : OpenRelationObligationFace replay LeftIncidence)
    (rightFace : OpenRelationObligationFace replay RightIncidence)
    (leftPly rightPly : GeneratedReplay.ActualPly replay) where
  incidenceEquiv : LeftIncidence ≃ RightIncidence
  incidence_mem_iff : ∀ incidence,
    incidence ∈ leftFace.incidences ↔
      incidenceEquiv incidence ∈ rightFace.incidences
  comparison_commutes : ∀ key : leftFace.SourceKey,
    (leftFace.edgeAt leftPly key).comparison =
      (rightFace.edgeAt rightPly
        ⟨incidenceEquiv key.1,
          (incidence_mem_iff key.1).mp key.2⟩).comparison

namespace GeneratedClosureUpdateEquivalence

def mapSourceKey
    {n : Nat} {law : Law} {moves : List (Move n)}
    {replay : GeneratedReplay law (Frame.initial n) moves}
    {LeftIncidence : Type u} {RightIncidence : Type v}
    [DecidableEq LeftIncidence] [DecidableEq RightIncidence]
    {leftFace : OpenRelationObligationFace replay LeftIncidence}
    {rightFace : OpenRelationObligationFace replay RightIncidence}
    {leftPly rightPly : GeneratedReplay.ActualPly replay}
    (equivalence : GeneratedClosureUpdateEquivalence leftFace rightFace
      leftPly rightPly) : leftFace.SourceKey → rightFace.SourceKey :=
  fun key => ⟨equivalence.incidenceEquiv key.1,
    (equivalence.incidence_mem_iff key.1).mp key.2⟩

def sourceKeyEquiv
    {n : Nat} {law : Law} {moves : List (Move n)}
    {replay : GeneratedReplay law (Frame.initial n) moves}
    {LeftIncidence : Type u} {RightIncidence : Type v}
    [DecidableEq LeftIncidence] [DecidableEq RightIncidence]
    {leftFace : OpenRelationObligationFace replay LeftIncidence}
    {rightFace : OpenRelationObligationFace replay RightIncidence}
    {leftPly rightPly : GeneratedReplay.ActualPly replay}
    (equivalence : GeneratedClosureUpdateEquivalence leftFace rightFace
      leftPly rightPly) : leftFace.SourceKey ≃ rightFace.SourceKey where
  toFun := equivalence.mapSourceKey
  invFun := fun key =>
    ⟨equivalence.incidenceEquiv.symm key.1,
      (equivalence.incidence_mem_iff
        (equivalence.incidenceEquiv.symm key.1)).mpr (by
          rw [equivalence.incidenceEquiv.apply_symm_apply]
          exact key.2)⟩
  left_inv := by intro key; apply Subtype.ext; simp [mapSourceKey]
  right_inv := by intro key; apply Subtype.ext; simp [mapSourceKey]

@[simp] theorem sourceKeyEquiv_apply
    {n : Nat} {law : Law} {moves : List (Move n)}
    {replay : GeneratedReplay law (Frame.initial n) moves}
    {LeftIncidence : Type u} {RightIncidence : Type v}
    [DecidableEq LeftIncidence] [DecidableEq RightIncidence]
    {leftFace : OpenRelationObligationFace replay LeftIncidence}
    {rightFace : OpenRelationObligationFace replay RightIncidence}
    {leftPly rightPly : GeneratedReplay.ActualPly replay}
    (equivalence : GeneratedClosureUpdateEquivalence leftFace rightFace
      leftPly rightPly) (key : leftFace.SourceKey) :
    equivalence.sourceKeyEquiv key = equivalence.mapSourceKey key :=
  rfl

theorem mapSourceKey_comparison
    {n : Nat} {law : Law} {moves : List (Move n)}
    {replay : GeneratedReplay law (Frame.initial n) moves}
    {LeftIncidence : Type u} {RightIncidence : Type v}
    [DecidableEq LeftIncidence] [DecidableEq RightIncidence]
    {leftFace : OpenRelationObligationFace replay LeftIncidence}
    {rightFace : OpenRelationObligationFace replay RightIncidence}
    {leftPly rightPly : GeneratedReplay.ActualPly replay}
    (equivalence : GeneratedClosureUpdateEquivalence leftFace rightFace
      leftPly rightPly) (key : leftFace.SourceKey) :
    (leftFace.edgeAt leftPly key).comparison =
      (rightFace.edgeAt rightPly (equivalence.mapSourceKey key)).comparison :=
  equivalence.comparison_commutes key

theorem effectSettles_mapSourceKey
    {n : Nat} {law : Law} {moves : List (Move n)}
    {replay : GeneratedReplay law (Frame.initial n) moves}
    {LeftIncidence : Type u} {RightIncidence : Type v}
    [DecidableEq LeftIncidence] [DecidableEq RightIncidence]
    {leftFace : OpenRelationObligationFace replay LeftIncidence}
    {rightFace : OpenRelationObligationFace replay RightIncidence}
    {leftPly rightPly : GeneratedReplay.ActualPly replay}
    (equivalence : GeneratedClosureUpdateEquivalence leftFace rightFace
      leftPly rightPly) (key : leftFace.SourceKey) :
    (GeneratedObligationUpdate.compile leftFace leftPly).effectSettles key =
      (GeneratedObligationUpdate.compile rightFace rightPly).effectSettles
        (equivalence.mapSourceKey key) := by
  unfold GeneratedObligationUpdate.effectSettles
  rw [equivalence.mapSourceKey_comparison key]

theorem effectCreatesDebt_mapSourceKey
    {n : Nat} {law : Law} {moves : List (Move n)}
    {replay : GeneratedReplay law (Frame.initial n) moves}
    {LeftIncidence : Type u} {RightIncidence : Type v}
    [DecidableEq LeftIncidence] [DecidableEq RightIncidence]
    {leftFace : OpenRelationObligationFace replay LeftIncidence}
    {rightFace : OpenRelationObligationFace replay RightIncidence}
    {leftPly rightPly : GeneratedReplay.ActualPly replay}
    (equivalence : GeneratedClosureUpdateEquivalence leftFace rightFace
      leftPly rightPly) (key : leftFace.SourceKey) :
    (GeneratedObligationUpdate.compile leftFace leftPly).effectCreatesDebt key =
      (GeneratedObligationUpdate.compile rightFace rightPly).effectCreatesDebt
        (equivalence.mapSourceKey key) := by
  unfold GeneratedObligationUpdate.effectCreatesDebt
  rw [equivalence.mapSourceKey_comparison key]

theorem majorEffects_image
    {n : Nat} {law : Law} {moves : List (Move n)}
    {replay : GeneratedReplay law (Frame.initial n) moves}
    {LeftIncidence : Type u} {RightIncidence : Type v}
    [DecidableEq LeftIncidence] [DecidableEq RightIncidence]
    {leftFace : OpenRelationObligationFace replay LeftIncidence}
    {rightFace : OpenRelationObligationFace replay RightIncidence}
    {leftPly rightPly : GeneratedReplay.ActualPly replay}
    (equivalence : GeneratedClosureUpdateEquivalence leftFace rightFace
      leftPly rightPly) :
    (GeneratedObligationUpdate.compile leftFace leftPly).majorEffects.image
        equivalence.sourceKeyEquiv =
      (GeneratedObligationUpdate.compile rightFace rightPly).majorEffects := by
  ext key
  constructor
  · intro _member
    exact GeneratedObligationUpdate.majorEffect_complete
      (GeneratedObligationUpdate.compile rightFace rightPly) key
  · intro _member
    apply Finset.mem_image.mpr
    refine ⟨equivalence.sourceKeyEquiv.symm key,
      GeneratedObligationUpdate.majorEffect_complete
        (GeneratedObligationUpdate.compile leftFace leftPly) _, ?_⟩
    exact equivalence.sourceKeyEquiv.apply_symm_apply key

theorem settledSources_image
    {n : Nat} {law : Law} {moves : List (Move n)}
    {replay : GeneratedReplay law (Frame.initial n) moves}
    {LeftIncidence : Type u} {RightIncidence : Type v}
    [DecidableEq LeftIncidence] [DecidableEq RightIncidence]
    {leftFace : OpenRelationObligationFace replay LeftIncidence}
    {rightFace : OpenRelationObligationFace replay RightIncidence}
    {leftPly rightPly : GeneratedReplay.ActualPly replay}
    (equivalence : GeneratedClosureUpdateEquivalence leftFace rightFace
      leftPly rightPly) :
    ((GeneratedObligationUpdate.compile leftFace leftPly).majorEffects.filter
        fun key =>
          GeneratedObligationUpdate.effectSettles
            (GeneratedObligationUpdate.compile leftFace leftPly) key).image
      equivalence.sourceKeyEquiv =
      (GeneratedObligationUpdate.compile rightFace rightPly).majorEffects.filter
        fun key => GeneratedObligationUpdate.effectSettles
          (GeneratedObligationUpdate.compile rightFace rightPly) key := by
  ext rightKey
  constructor
  · intro member
    rcases Finset.mem_image.mp member with
      ⟨leftKey, leftMember, keyEq⟩
    have leftFacts := Finset.mem_filter.mp leftMember
    apply Finset.mem_filter.mpr
    refine ⟨GeneratedObligationUpdate.majorEffect_complete
      (GeneratedObligationUpdate.compile rightFace rightPly) rightKey, ?_⟩
    rw [← keyEq]
    change GeneratedObligationUpdate.effectSettles
      (GeneratedObligationUpdate.compile rightFace rightPly)
        (equivalence.mapSourceKey leftKey) = true
    rw [← equivalence.effectSettles_mapSourceKey leftKey]
    exact leftFacts.2
  · intro member
    have rightFacts := Finset.mem_filter.mp member
    apply Finset.mem_image.mpr
    let leftKey := equivalence.sourceKeyEquiv.symm rightKey
    refine ⟨leftKey, Finset.mem_filter.mpr ⟨
      GeneratedObligationUpdate.majorEffect_complete
        (GeneratedObligationUpdate.compile leftFace leftPly) leftKey, ?_⟩,
      equivalence.sourceKeyEquiv.apply_symm_apply rightKey⟩
    rw [equivalence.effectSettles_mapSourceKey leftKey]
    have mapped : equivalence.mapSourceKey leftKey = rightKey := by
      change equivalence.sourceKeyEquiv leftKey = rightKey
      exact equivalence.sourceKeyEquiv.apply_symm_apply rightKey
    rw [mapped]
    exact rightFacts.2

theorem debtSources_image
    {n : Nat} {law : Law} {moves : List (Move n)}
    {replay : GeneratedReplay law (Frame.initial n) moves}
    {LeftIncidence : Type u} {RightIncidence : Type v}
    [DecidableEq LeftIncidence] [DecidableEq RightIncidence]
    {leftFace : OpenRelationObligationFace replay LeftIncidence}
    {rightFace : OpenRelationObligationFace replay RightIncidence}
    {leftPly rightPly : GeneratedReplay.ActualPly replay}
    (equivalence : GeneratedClosureUpdateEquivalence leftFace rightFace
      leftPly rightPly) :
    ((GeneratedObligationUpdate.compile leftFace leftPly).majorEffects.filter
        fun key =>
          GeneratedObligationUpdate.effectCreatesDebt
            (GeneratedObligationUpdate.compile leftFace leftPly) key).image
      equivalence.sourceKeyEquiv =
      (GeneratedObligationUpdate.compile rightFace rightPly).majorEffects.filter
        fun key => GeneratedObligationUpdate.effectCreatesDebt
          (GeneratedObligationUpdate.compile rightFace rightPly) key := by
  ext rightKey
  constructor
  · intro member
    rcases Finset.mem_image.mp member with
      ⟨leftKey, leftMember, keyEq⟩
    have leftFacts := Finset.mem_filter.mp leftMember
    apply Finset.mem_filter.mpr
    refine ⟨GeneratedObligationUpdate.majorEffect_complete
      (GeneratedObligationUpdate.compile rightFace rightPly) rightKey, ?_⟩
    rw [← keyEq]
    change GeneratedObligationUpdate.effectCreatesDebt
      (GeneratedObligationUpdate.compile rightFace rightPly)
        (equivalence.mapSourceKey leftKey) = true
    rw [← equivalence.effectCreatesDebt_mapSourceKey leftKey]
    exact leftFacts.2
  · intro member
    have rightFacts := Finset.mem_filter.mp member
    apply Finset.mem_image.mpr
    let leftKey := equivalence.sourceKeyEquiv.symm rightKey
    refine ⟨leftKey, Finset.mem_filter.mpr ⟨
      GeneratedObligationUpdate.majorEffect_complete
        (GeneratedObligationUpdate.compile leftFace leftPly) leftKey, ?_⟩,
      equivalence.sourceKeyEquiv.apply_symm_apply rightKey⟩
    rw [equivalence.effectCreatesDebt_mapSourceKey leftKey]
    have mapped : equivalence.mapSourceKey leftKey = rightKey := by
      change equivalence.sourceKeyEquiv leftKey = rightKey
      exact equivalence.sourceKeyEquiv.apply_symm_apply rightKey
    rw [mapped]
    exact rightFacts.2

theorem settledKeys_image
    {n : Nat} {law : Law} {moves : List (Move n)}
    {replay : GeneratedReplay law (Frame.initial n) moves}
    {LeftIncidence : Type u} {RightIncidence : Type v}
    [DecidableEq LeftIncidence] [DecidableEq RightIncidence]
    {leftFace : OpenRelationObligationFace replay LeftIncidence}
    {rightFace : OpenRelationObligationFace replay RightIncidence}
    {leftPly rightPly : GeneratedReplay.ActualPly replay}
    (equivalence : GeneratedClosureUpdateEquivalence leftFace rightFace
      leftPly rightPly) :
    (GeneratedObligationUpdate.compile leftFace leftPly).settledKeys.image
        (obligationKeyEquiv equivalence.incidenceEquiv) =
      (GeneratedObligationUpdate.compile rightFace rightPly).settledKeys := by
  let leftSources :=
    (GeneratedObligationUpdate.compile leftFace leftPly).majorEffects.filter
      fun key =>
        (GeneratedObligationUpdate.compile leftFace leftPly).effectSettles key
  let rightSources :=
    (GeneratedObligationUpdate.compile rightFace rightPly).majorEffects.filter
      fun key =>
        (GeneratedObligationUpdate.compile rightFace rightPly).effectSettles key
  change (leftSources.image (fun key => ObligationKey.open key.1)).image
      (obligationKeyEquiv equivalence.incidenceEquiv) =
    rightSources.image (fun key => ObligationKey.open key.1)
  rw [Finset.image_image]
  calc
    leftSources.image
        ((obligationKeyEquiv equivalence.incidenceEquiv) ∘
          fun key => ObligationKey.open key.1) =
      leftSources.image
        ((fun key : rightFace.SourceKey => ObligationKey.open key.1) ∘
          equivalence.sourceKeyEquiv) := by
            congr 1
    _ = (leftSources.image equivalence.sourceKeyEquiv).image
        (fun key => ObligationKey.open key.1) :=
      (Finset.image_image).symm
    _ = rightSources.image (fun key => ObligationKey.open key.1) := by
      rw [show leftSources.image equivalence.sourceKeyEquiv = rightSources
        from equivalence.settledSources_image]

theorem newDebtKeys_image
    {n : Nat} {law : Law} {moves : List (Move n)}
    {replay : GeneratedReplay law (Frame.initial n) moves}
    {LeftIncidence : Type u} {RightIncidence : Type v}
    [DecidableEq LeftIncidence] [DecidableEq RightIncidence]
    {leftFace : OpenRelationObligationFace replay LeftIncidence}
    {rightFace : OpenRelationObligationFace replay RightIncidence}
    {leftPly rightPly : GeneratedReplay.ActualPly replay}
    (equivalence : GeneratedClosureUpdateEquivalence leftFace rightFace
      leftPly rightPly) :
    (GeneratedObligationUpdate.compile leftFace leftPly).newDebtKeys.image
        (obligationKeyEquiv equivalence.incidenceEquiv) =
      (GeneratedObligationUpdate.compile rightFace rightPly).newDebtKeys := by
  let leftSources :=
    (GeneratedObligationUpdate.compile leftFace leftPly).majorEffects.filter
      fun key =>
        GeneratedObligationUpdate.effectCreatesDebt
          (GeneratedObligationUpdate.compile leftFace leftPly) key
  let rightSources :=
    (GeneratedObligationUpdate.compile rightFace rightPly).majorEffects.filter
      fun key =>
        GeneratedObligationUpdate.effectCreatesDebt
          (GeneratedObligationUpdate.compile rightFace rightPly) key
  change (leftSources.image
      (fun key => ObligationKey.generatedDebt key.1)).image
      (obligationKeyEquiv equivalence.incidenceEquiv) =
    rightSources.image (fun key => ObligationKey.generatedDebt key.1)
  rw [Finset.image_image]
  calc
    leftSources.image
        ((obligationKeyEquiv equivalence.incidenceEquiv) ∘
          fun key => ObligationKey.generatedDebt key.1) =
      leftSources.image
        ((fun key : rightFace.SourceKey =>
          ObligationKey.generatedDebt key.1) ∘
            equivalence.sourceKeyEquiv) := by
              congr 1
    _ = (leftSources.image equivalence.sourceKeyEquiv).image
        (fun key => ObligationKey.generatedDebt key.1) :=
      (Finset.image_image).symm
    _ = rightSources.image
        (fun key => ObligationKey.generatedDebt key.1) := by
      rw [show leftSources.image equivalence.sourceKeyEquiv = rightSources
        from equivalence.debtSources_image]

theorem closureGain_eq
    {n : Nat} {law : Law} {moves : List (Move n)}
    {replay : GeneratedReplay law (Frame.initial n) moves}
    {LeftIncidence : Type u} {RightIncidence : Type v}
    [DecidableEq LeftIncidence] [DecidableEq RightIncidence]
    {leftFace : OpenRelationObligationFace replay LeftIncidence}
    {rightFace : OpenRelationObligationFace replay RightIncidence}
    {leftPly rightPly : GeneratedReplay.ActualPly replay}
    (equivalence : GeneratedClosureUpdateEquivalence leftFace rightFace
      leftPly rightPly) :
    closureGain (GeneratedObligationUpdate.compile leftFace leftPly) =
      closureGain (GeneratedObligationUpdate.compile rightFace rightPly) := by
  apply closureGain_keyPresentation_invariant
  exact {
    keyEquiv := obligationKeyEquiv equivalence.incidenceEquiv
    settled_image := equivalence.settledKeys_image
    debt_image := equivalence.newDebtKeys_image
  }

end GeneratedClosureUpdateEquivalence

end Go
end ProcessGame
end SaturationMonoid
