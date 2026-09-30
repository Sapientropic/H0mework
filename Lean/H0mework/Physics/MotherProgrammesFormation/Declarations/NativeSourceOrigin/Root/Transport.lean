import H0mework.Physics.MotherProgrammesFormation.Declarations.NativeSourceOrigin.Root.Coverage

set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherLedgerRoot
open MotherFullCompiler MotherSourcePrograms MotherExactPrograms MotherFullPatches MotherPatchInventory
open ResponsibilityLifecycle.LivingLawEvolution
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
noncomputable section

private theorem emitted_cast {A : Type} {E : A → Type} (emitted : (a : A) → E a)
    {a b : A} (same : a = b) : (Equiv.cast (congrArg E same)) (emitted a) = emitted b := by
  cases same
  rfl

def BranchCommutes {N : WorldRelationNetwork.{0}} {V : Vocabulary.{0}} {source : SourceNativeSource N V}
    (emitted : Emitted source) {current : V.Current} : (branch : EvolutionAt V current) → TargetFor source branch → Prop
  | .nativeWrite write, target => target = emitted (V.nativeTarget write)
  | .relationWrite write, target => target = emitted (V.relationTarget write)
  | .continuedTransport write, target => target = emitted (V.continuedTarget write)
  | .borromeanRedirect write, target => target = emitted (V.redirectTarget write)
  | .faithfulTerminal _, _ => True

theorem branch_commutes_iff {N : WorldRelationNetwork.{0}} {V : Vocabulary.{0}} {source : SourceNativeSource N V}
    (emitted : Emitted source) (point : Point source) (branch : EvolutionAt V point.1)
    (structural : source.toRootSource.actual.compile point.2 = branch)
    (body : Sigma (LedgerFor source point.2 branch)) :
    (fromGraph source point.2 ⟨branch, ⟨(bodyEquiv source point.2 branch).symm body, structural⟩⟩).CommutesWith emitted ↔
      BranchCommutes emitted branch body.1 := by
  cases branch <;> rfl

theorem compilation_commutes_iff {N : WorldRelationNetwork.{0}} {V : Vocabulary.{0}} {source : SourceNativeSource N V}
    (emitted : Emitted source) (point : Point source) (compiled : SourceNativeLedgerEvolutionAt source point.2) :
    compiled.CommutesWith emitted ↔ BranchCommutes emitted (source.toRootSource.actual.compile point.2)
      (bodyOfCompilation point compiled).1 := by
  let e := (compilationEquiv source point.2).trans (bodyEquiv source point.2 _)
  exact (Iff.of_eq (congrArg (fun value => value.CommutesWith emitted) (e.symm_apply_apply compiled))).symm.trans
    (branch_commutes_iff emitted point _ rfl (bodyOfCompilation point compiled))

variable {N G : WorldRelationNetwork.{0}} {V W : Vocabulary.{0}}
    {original : SourceNativeSource N V} {generated : SourceNativeSource G W}
    {n : MotherNetworkOrigin.Presentation N G} {v : MotherVocabularyOrigin.Presentation V W}
    (p : MotherNativeSourceOrigin.Presentation n v original generated)

def emitterEquiv : Emitted original ≃ Emitted generated := Equiv.piCongr v.current p.event

theorem emitter_at (emitted : Emitted original) (current : V.Current) :
    emitterEquiv p emitted (v.current current) = p.event current (emitted current) :=
  Equiv.piCongr_apply_apply _ _ _ _

theorem transportBranchCommutes (emitted : Emitted original) {current : V.Current}
    (branch : EvolutionAt V current) (target : TargetFor original branch)
    (commutes : BranchCommutes emitted branch target) :
    BranchCommutes (emitterEquiv p emitted) (v.evolution current branch) (targetEquiv p branch target) := by
  cases branch with
  | nativeWrite write =>
      change target = emitted (V.nativeTarget write) at commutes
      cases commutes
      exact (congrArg (Equiv.cast (congrArg generated.toRootSource.actual.OccurrenceAt (v.native_eq current write).symm))
        (emitter_at p emitted (V.nativeTarget write)).symm).trans (emitted_cast (emitterEquiv p emitted) (v.native_eq current write).symm)
  | relationWrite write =>
      change target = emitted (V.relationTarget write) at commutes
      cases commutes
      exact (congrArg (Equiv.cast (congrArg generated.toRootSource.actual.OccurrenceAt (v.relation_eq current write).symm))
        (emitter_at p emitted (V.relationTarget write)).symm).trans (emitted_cast (emitterEquiv p emitted) (v.relation_eq current write).symm)
  | continuedTransport write =>
      change target = emitted (V.continuedTarget write) at commutes
      cases commutes
      exact (congrArg (Equiv.cast (congrArg generated.toRootSource.actual.OccurrenceAt (v.continued_eq current write).symm))
        (emitter_at p emitted (V.continuedTarget write)).symm).trans (emitted_cast (emitterEquiv p emitted) (v.continued_eq current write).symm)
  | borromeanRedirect write =>
      change target = emitted (V.redirectTarget write) at commutes
      cases commutes
      exact (congrArg (Equiv.cast (congrArg generated.toRootSource.actual.OccurrenceAt (v.redirect_eq current write).symm))
        (emitter_at p emitted (V.redirectTarget write)).symm).trans (emitted_cast (emitterEquiv p emitted) (v.redirect_eq current write).symm)
  | faithfulTerminal => trivial

theorem castBranchCommutes {H : WorldRelationNetwork.{0}} {U : Vocabulary.{0}} {source : SourceNativeSource H U}
    (emitted : Emitted source) (point : Point source) {left right : EvolutionAt U point.1} (same : left = right)
    (body : Sigma (LedgerFor source point.2 left)) (commutes : BranchCommutes emitted left body.1) :
    BranchCommutes emitted right
      ((Equiv.cast (congrArg (fun branch => Sigma (LedgerFor source point.2 branch)) same)) body).1 := by
  cases same
  exact commutes

theorem fullCompilation_commutes (emitted : Emitted original) (point : Point original)
    (compiled : SourceNativeLedgerEvolutionAt original point.2) (commutes : compiled.CommutesWith emitted) :
    (fullCompilationEquiv p point.2 compiled).CommutesWith (emitterEquiv p emitted) := by
  let body := bodyOfCompilation point compiled
  let newBody : Sigma (LedgerFor generated (pointEquiv p point).2
      (v.evolution point.1 (original.toRootSource.actual.compile point.2))) :=
    ⟨targetEquiv p _ body.1, ledgerForEquiv p point.2 _ body.1 body.2⟩
  let actualBody := (Equiv.cast (congrArg
    (fun branch => Sigma (LedgerFor generated (pointEquiv p point).2 branch)) (p.compile_eq point.1 point.2).symm)) newBody
  have oldCommutes := (compilation_commutes_iff emitted point compiled).mp commutes
  have newCommutes := transportBranchCommutes p emitted _ body.1 oldCommutes
  have actualCommutes := castBranchCommutes (emitterEquiv p emitted) (pointEquiv p point)
    (p.compile_eq point.1 point.2).symm newBody newCommutes
  exact (branch_commutes_iff (emitterEquiv p emitted) (pointEquiv p point) _ rfl actualBody).mpr actualCommutes

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherLedgerRoot
