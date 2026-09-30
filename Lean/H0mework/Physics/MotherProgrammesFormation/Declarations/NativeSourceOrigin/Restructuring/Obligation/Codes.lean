import H0mework.Physics.MotherProgrammesFormation.Declarations.NativeSourceOrigin.Restructuring.Obligation.Source

set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherObligationOrigin
open MotherNetworkFactory MotherRestructuringOrigin ResponsibilityLifecycle
noncomputable section

def productEmbedding {A C : Type} (left : A ↪ B) (right : C ↪ B) : A × C ↪ B where
  toFun := fun value => MotherHigherLawFamily.pair (left value.1, right value.2)
  inj' := by
    intro x y same
    have same := MotherHigherLawFamily.pair_injective same
    exact Prod.ext (left.injective (congrArg Prod.fst same)) (right.injective (congrArg Prod.snd same))

def sigmaEmbedding {A : Type} {F : A → Type} (base : A ↪ B) (member : ∀ a, F a ↪ B) : Sigma F ↪ B where
  toFun := fun value => MotherHigherLawFamily.pair (base value.1, member value.1 value.2)
  inj' := by
    rintro ⟨a, x⟩ ⟨b, y⟩ same
    have pairEq := MotherHigherLawFamily.pair_injective same
    have baseEq := base.injective (congrArg Prod.fst pairEq)
    cases baseEq
    have memberEq := (member a).injective (congrArg Prod.snd pairEq)
    cases memberEq
    rfl

def sumEmbedding {A C : Type} (left : A ↪ B) (right : C ↪ B) : A ⊕ C ↪ B where
  toFun := fun value => match value with
    | .inl a => MotherHigherLawFamily.pair (natTag 0, left a)
    | .inr c => MotherHigherLawFamily.pair (natTag 1, right c)
  inj' := by
    intro x y same
    cases x <;> cases y <;> have pairEq := MotherHigherLawFamily.pair_injective same
    · exact congrArg Sum.inl (left.injective (congrArg Prod.snd pairEq))
    · have bad := natTag_injective (congrArg Prod.fst pairEq); cases bad
    · have bad := natTag_injective (congrArg Prod.fst pairEq); cases bad
    · exact congrArg Sum.inr (right.injective (congrArg Prod.snd pairEq))

def fieldEmbedding (base : M) (index : Fin 12) : Field base index ↪ B :=
  ⟨Subtype.val, fun _ _ same => Subtype.ext same⟩

def evidenceEmbedding (base families : M) (index : Fin 31) (args : Args (formedSorts base) (signature index)) :
    formedFamilies base families index args ↪ B :=
  ⟨Subtype.val, fun _ _ same => Subtype.ext same⟩

variable (base families : M) (ops : Operations (formedSorts base) (formedFamilies base families))

abbrev nativeVocabulary := vocabulary (formedSorts base) (formedFamilies base families) ops

def originEmbedding (source : Field base 0) (content : Field base 1) :
    ObligationOrigin (nativeVocabulary base families ops) source content ↪ B :=
  (originBodyEquiv (nativeVocabulary base families ops) source content).toEmbedding.trans
    (sumEmbedding
      ((⟨Subtype.val, fun _ _ same => Subtype.ext same⟩ :
        {o : Obstruction base families source // ops.demandContent o = content} ↪ Obstruction base families source).trans
          (evidenceEmbedding base families 0 (source, PUnit.unit)))
      (sumEmbedding (evidenceEmbedding base families 1 (source, content, PUnit.unit))
        (sumEmbedding (evidenceEmbedding base families 2 (source, content, PUnit.unit))
          (sumEmbedding (evidenceEmbedding base families 3 (source, content, PUnit.unit))
            (sumEmbedding (evidenceEmbedding base families 4 (source, content, PUnit.unit))
              (evidenceEmbedding base families 5 (source, content, PUnit.unit)))))))

def assumptionEmbedding (source : Field base 0) (bearer : Field base 3) (scope : Field base 5) :
    BearerAssumption (nativeVocabulary base families ops) source bearer scope ↪ B :=
  (assumptionBodyEquiv (nativeVocabulary base families ops) source bearer scope).toEmbedding.trans
    (sumEmbedding (evidenceEmbedding base families 7 (bearer, source, scope, PUnit.unit))
      (evidenceEmbedding base families 8 (bearer, source, scope, PUnit.unit)))

def admissionEmbedding (content : Field base 1) : AdmissionReceipt (nativeVocabulary base families ops) content ↪ B :=
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
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherObligationOrigin
