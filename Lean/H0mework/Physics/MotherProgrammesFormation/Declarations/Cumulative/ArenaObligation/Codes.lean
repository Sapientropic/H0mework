import H0mework.Physics.MotherProgrammesFormation.Declarations.Cumulative.ArenaRestructuringVocabulary.Operations
import H0mework.Physics.MotherProgrammesFormation.Declarations.NativeSourceOrigin.Restructuring.Obligation.Codes
import H0mework.Physics.MotherProgrammesFormation.Declarations.Cumulative.ArenaProjection.FullConsumer

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherArenaObligation
open MotherArenaNetwork MotherRestructuringOrigin ResponsibilityLifecycle
open MotherObligationOrigin
noncomputable section
variable {rank : Ordinal.{0}}
local notation "B" => MotherArenaHigher.Base rank
local notation "M" => MotherArenaHigher.Material rank

def productEmbedding {A C : Type} (left : A ↪ B) (right : C ↪ B) : A × C ↪ B where
  toFun := fun value => (MotherArenaHigher.pair rank) (left value.1, right value.2)
  inj' := by
    intro x y same
    have same := (MotherArenaHigher.pairEquiv rank).injective same
    exact Prod.ext (left.injective (congrArg Prod.fst same)) (right.injective (congrArg Prod.snd same))

def sigmaEmbedding {A : Type} {F : A → Type} (base : A ↪ B) (member : ∀ a, F a ↪ B) : Sigma F ↪ B where
  toFun := fun value => (MotherArenaHigher.pair rank) (base value.1, member value.1 value.2)
  inj' := by
    rintro ⟨a, x⟩ ⟨b, y⟩ same
    have pairEq := (MotherArenaHigher.pairEquiv rank).injective same
    have baseEq := base.injective (congrArg Prod.fst pairEq)
    cases baseEq
    have memberEq := (member a).injective (congrArg Prod.snd pairEq)
    cases memberEq
    rfl

def sumEmbedding {A C : Type} (left : A ↪ B) (right : C ↪ B) : A ⊕ C ↪ B where
  toFun := fun value => match value with
    | .inl a => (MotherArenaHigher.pair rank) (MotherArenaRestructuringVocabulary.natTag 0, left a)
    | .inr c => (MotherArenaHigher.pair rank) (MotherArenaRestructuringVocabulary.natTag 1, right c)
  inj' := by
    intro x y same
    cases x <;> cases y <;> have pairEq := (MotherArenaHigher.pairEquiv rank).injective same
    · exact congrArg Sum.inl (left.injective (congrArg Prod.snd pairEq))
    · have bad := MotherArenaRestructuringVocabulary.natTag_injective (congrArg Prod.fst pairEq); cases bad
    · have bad := MotherArenaRestructuringVocabulary.natTag_injective (congrArg Prod.fst pairEq); cases bad
    · exact congrArg Sum.inr (right.injective (congrArg Prod.snd pairEq))

def fieldEmbedding (base : M) (index : Fin 12) : MotherArenaRestructuringVocabulary.Field base index ↪ B :=
  ⟨Subtype.val, fun _ _ same => Subtype.ext same⟩

def evidenceEmbedding (base families : M) (index : Fin 31) (args : Args (MotherArenaRestructuringVocabulary.formedSorts base) (signature index)) :
    MotherArenaRestructuringVocabulary.formedFamilies base families index args ↪ B :=
  ⟨Subtype.val, fun _ _ same => Subtype.ext same⟩

variable (base families : MotherArenaHigher.Material rank) (ops : Operations (MotherArenaRestructuringVocabulary.formedSorts base) (MotherArenaRestructuringVocabulary.formedFamilies base families))

abbrev nativeVocabulary := vocabulary (MotherArenaRestructuringVocabulary.formedSorts base) (MotherArenaRestructuringVocabulary.formedFamilies base families) ops

def originEmbedding (source : MotherArenaRestructuringVocabulary.Field base 0) (content : MotherArenaRestructuringVocabulary.Field base 1) :
    ObligationOrigin (nativeVocabulary base families ops) source content ↪ B :=
  (originBodyEquiv (nativeVocabulary base families ops) source content).toEmbedding.trans
    (sumEmbedding
      ((⟨Subtype.val, fun _ _ same => Subtype.ext same⟩ :
        {o : MotherArenaRestructuringVocabulary.Obstruction base families source // ops.demandContent o = content} ↪ MotherArenaRestructuringVocabulary.Obstruction base families source).trans
          (evidenceEmbedding base families 0 (source, PUnit.unit)))
      (sumEmbedding (evidenceEmbedding base families 1 (source, content, PUnit.unit))
        (sumEmbedding (evidenceEmbedding base families 2 (source, content, PUnit.unit))
          (sumEmbedding (evidenceEmbedding base families 3 (source, content, PUnit.unit))
            (sumEmbedding (evidenceEmbedding base families 4 (source, content, PUnit.unit))
              (evidenceEmbedding base families 5 (source, content, PUnit.unit)))))))

def assumptionEmbedding (source : MotherArenaRestructuringVocabulary.Field base 0) (bearer : MotherArenaRestructuringVocabulary.Field base 3) (scope : MotherArenaRestructuringVocabulary.Field base 5) :
    BearerAssumption (nativeVocabulary base families ops) source bearer scope ↪ B :=
  (assumptionBodyEquiv (nativeVocabulary base families ops) source bearer scope).toEmbedding.trans
    (sumEmbedding (evidenceEmbedding base families 7 (bearer, source, scope, PUnit.unit))
      (evidenceEmbedding base families 8 (bearer, source, scope, PUnit.unit)))

def admissionEmbedding (content : MotherArenaRestructuringVocabulary.Field base 1) : AdmissionReceipt (nativeVocabulary base families ops) content ↪ B :=
  (admissionBodyEquiv (nativeVocabulary base families ops) content).toEmbedding.trans
    (sigmaEmbedding (fieldEmbedding base 0) (fun source => sigmaEmbedding (fieldEmbedding base 3) (fun bearer =>
      productEmbedding (originEmbedding base families ops source content)
        (productEmbedding (evidenceEmbedding base families 6 (source, ops.anchorScope source, PUnit.unit))
          (assumptionEmbedding base families ops source bearer (ops.anchorScope source))))))

/-- Complete generated obligations have native addresses: all current fields,
original admission data and current discharge evidence remain in the code. -/
def obligationEmbedding : AdmittedObligation (nativeVocabulary base families ops) ↪ B :=
  (obligationBodyEquiv (nativeVocabulary base families ops)).toEmbedding.trans
    (sigmaEmbedding (fieldEmbedding base 1) (fun content => sigmaEmbedding (fieldEmbedding base 2) (fun _ =>
      sigmaEmbedding (fieldEmbedding base 3) (fun _ => sigmaEmbedding (fieldEmbedding base 4) (fun _ =>
        sigmaEmbedding (fieldEmbedding base 5) (fun scope => productEmbedding (admissionEmbedding base families ops content)
          (evidenceEmbedding base families 9 (content, scope, PUnit.unit))))))))

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherArenaObligation
