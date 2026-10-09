import H0mework.Realization.ScalarCofinal.Tail
set_option autoImplicit false
noncomputable section
universe r u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGeneratedActionObservationHistory.AlgebraicDependent
open SourceGeneratedScalarCofinalKernelCompletion SourceGeneratedScalarCofinalNaturality
open CategoryTheory CategoryTheory.Limits
variable {R : Type r} [CommRing R]
variable {C B : Nat → Type u} [∀ n,AddCommGroup (C n)] [∀ n,Module R (C n)]
variable [∀ n,AddCommGroup (B n)] [∀ n,Module R (B n)]
variable (action : ∀ n,C n →ₗ[R] C (n+1)) (read : ∀ n,C n →ₗ[R] B n)

abbrev Prefix (B : Nat → Type u) (n bound : Nat) := (index : Fin (bound+1)) → B (n+index.val)

def advance (n : Nat) : (k : Nat) → C n →ₗ[R] C (n+k) :=
 Nat.rec (LinearMap.id : C n →ₗ[R] C n)
  (fun k previous => (action (n+k)).comp previous)

def evaluator (n bound : Nat) : C n →ₗ[R] Prefix B n bound :=
 LinearMap.pi fun index => (read (n+index.val)).comp (advance action n index.val)

def restriction (n bound : Nat) : Prefix B n (bound+1) →ₗ[R] Prefix B n bound :=
 LinearMap.pi fun index => LinearMap.proj index.castSucc

def data (n : Nat) : Data (R:=R) (Generator:=C n) (Carrier:=Prefix B n) where
 evaluator:=evaluator action read n
 transition:=restriction n

theorem compatible (n : Nat) : (data action read n).Compatible := by
 intro bound
 apply LinearMap.ext
 intro value
 rfl

def completion (n : Nat) := (data action read n).Completion (compatible action read n)
def sourceMap (n : Nat) : C n →ₗ[R] completion action read n :=
 ((data action read n).completionMap (compatible action read n)).hom

def readPrefix (n bound : Nat) : completion action read n →ₗ[R] Prefix B n bound :=
 ((data action read n).stageRealization bound).comp
  ((data action read n).restriction (compatible action read n) bound).hom

theorem source_prefix (n bound : Nat) (value : C n) :
 readPrefix action read n bound (sourceMap action read n value)=evaluator action read n bound value :=
 ConcreteCategory.congr_hom ((data action read n).source_to_evaluator (compatible action read n) bound) value
theorem source_fibre (n : Nat) (left right : C n) :
 sourceMap action read n left=sourceMap action read n right ↔
 ∀ k,read (n+k) (advance action n k left)=read (n+k) (advance action n k right) := by
 constructor
 · intro same k
   have observed := congrArg (fun value => readPrefix action read n k value (Fin.last k)) same
   rw [source_prefix,source_prefix] at observed
   exact observed
 · intro observed
   apply Limits.Concrete.limit_ext ((data action read n).quotientTower (compatible action read n))
   intro bound
   have l := ConcreteCategory.congr_hom ((data action read n).completionMap_restriction (compatible action read n) bound.unop) left
   have r := ConcreteCategory.congr_hom ((data action read n).completionMap_restriction (compatible action read n) bound.unop) right
   have eq : (data action read n).quotientMap bound.unop left=(data action read n).quotientMap bound.unop right := by
    apply (data action read n).stageRealization_injective bound.unop
    exact funext fun index => observed index.val
   exact l.trans (eq.trans r.symm)

def familyCast {i j : Nat} (same : i=j) : C i →ₗ[R] C j := same ▸ LinearMap.id

theorem cast_action {i j : Nat} (same : i=j) :
 (familyCast (C:=C) (R:=R) (congrArg (·+1) same)).comp (action i)=
 (action j).comp (familyCast (C:=C) (R:=R) same) := by
 cases same
 rfl

theorem advance_succ (n k : Nat) :
 advance action n (k+1)=
 (familyCast (C:=C) (R:=R) (by omega : n+1+k=n+(k+1))).comp
  ((advance action (n+1) k).comp (action n)) := by
 induction k with
 | zero => rfl
 | succ k previous =>
   apply LinearMap.ext
   intro value
   change action (n+(k+1)) (advance action n (k+1) value)=_
   rw [previous]
   have same : n+1+k=n+(k+1) := by omega
   exact (LinearMap.congr_fun (cast_action action same) (advance action (n+1) k (action n value))).symm

def dropFirst (n bound : Nat) : Prefix B n (bound+1) →ₗ[R] Prefix B (n+1) bound :=
 LinearMap.pi fun index =>
  (familyCast (C:=B) (R:=R) (by omega : n+index.val+1=n+1+index.val)).comp
   (LinearMap.proj index.succ)

theorem dropFirst_transition (n bound : Nat) :
 (dropFirst (B:=B) (R:=R) n bound).comp (restriction n (bound+1))=
 (restriction (n+1) bound).comp (dropFirst n (bound+1)) := by
 apply LinearMap.ext
 intro value
 funext index
 rfl

theorem cast_read {i j : Nat} (same : i=j) :
 (familyCast (C:=B) (R:=R) same).comp (read i)=
 (read j).comp (familyCast (C:=C) (R:=R) same) := by
 cases same
 rfl

theorem dropFirst_evaluator (n bound : Nat) :
 (dropFirst (B:=B) (R:=R) n bound).comp (evaluator action read n (bound+1))=
 (evaluator action read (n+1) bound).comp (action n) := by
 apply LinearMap.ext
 intro value
 funext index
 change familyCast (C:=B) (R:=R) _ (read (n+(index.val+1)) (advance action n (index.val+1) value))=_
 rw [advance_succ]
 have same : n+1+index.val=n+(index.val+1) := by omega
 have square := LinearMap.congr_fun (cast_read read same.symm)
  (familyCast (C:=C) (R:=R) same (advance action (n+1) index.val (action n value)))
 have inverse {i j : Nat} (h : i=j) (x : C i) :
  familyCast (C:=C) (R:=R) h.symm (familyCast (C:=C) (R:=R) h x)=x := by
  cases h
  rfl
 exact square.trans (congrArg (read (n+1+index.val)) (inverse same _))

def historyMorphism (n : Nat) :
 SourceGeneratedScalarCofinalNaturality.Morphism (SourceGeneratedScalarCofinalTail.tail (data action read n))
  (data action read (n+1)) where
 generatorMap:=action n
 stageMap:=dropFirst n
 transition_naturality:=dropFirst_transition n
 evaluator_naturality:=dropFirst_evaluator action read n

def successor (n : Nat) : completion action read n →ₗ[R] completion action read (n+1) :=
 ((historyMorphism action read n).completionMorphism
  (SourceGeneratedScalarCofinalTail.compatible (data action read n) (compatible action read n))
  (compatible action read (n+1))).hom.comp
   (SourceGeneratedScalarCofinalTail.completionMap (data action read n) (compatible action read n)).hom

theorem successor_source (n : Nat) (value : C n) :
 successor action read n (sourceMap action read n value)=sourceMap action read (n+1) (action n value) := by
 have tail := ConcreteCategory.congr_hom (SourceGeneratedScalarCofinalTail.completionMap_source
  (data action read n) (compatible action read n)) value
 have source := ConcreteCategory.congr_hom ((historyMorphism action read n).completionMorphism_source_naturality
  (SourceGeneratedScalarCofinalTail.compatible (data action read n) (compatible action read n))
  (compatible action read (n+1))) value
 exact (congrArg ((historyMorphism action read n).completionMorphism
  (SourceGeneratedScalarCofinalTail.compatible (data action read n) (compatible action read n))
  (compatible action read (n+1))).hom tail).trans source

end SourceGeneratedActionObservationHistory.AlgebraicDependent
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
