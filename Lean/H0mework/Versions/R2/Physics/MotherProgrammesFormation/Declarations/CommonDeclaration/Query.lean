import H0mework.Versions.R2.Physics.MotherDeclarationsNative.PhysicalQueryInquiry
import H0mework.Versions.R2.Physics.MotherLaws.CurrentConsumer
import Mathlib.Data.List.GetD

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option maxHeartbeats 2000000

namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherOriginalQueryValue

open MotherStreamLaws MotherTypeFormation MotherFamilyOccurrence
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion

noncomputable section

abbrev Base := MotherPhysicalLaws.Law
abbrev Query := MotherNativePhysicalQuery.Query
abbrev Word := MotherNativePhysicalQuery.Word
abbrev Term := MotherNativePhysicalQuery.Term

def pointwiseEquiv : MotherPointwiseLaws.Law ≃ (Stream → Stream) :=
  Equiv.ofBijective MotherPointwiseLaws.lawRead
    ⟨MotherPointwiseLaws.lawRead_uniformEmbedding.injective,
      MotherPointwiseLaws.lawRead_surjective⟩

/-- The current is fixed by existing mother dynamics; only the Stream input varies. -/
def input (value : Stream) : MotherPhysicalLaws.Input :=
  (MotherDurationExposure.dynamics.initial, value)

/-- A complete pointwise law is recovered from actual Base evaluation at every Stream. -/
def readPointwise (law : Base) : MotherPointwiseLaws.Law :=
  pointwiseEquiv.symm (fun value => MotherPhysicalLaws.eval law (input value))

theorem readPointwise_surjective : Function.Surjective readPointwise := by
  intro original
  obtain ⟨law, generated, _⟩ := MotherPhysicalLaws.every_law
    (fun raw => MotherPointwiseLaws.eval original raw.2)
  refine ⟨law, ?_⟩
  apply pointwiseEquiv.injective
  change pointwiseEquiv
    (pointwiseEquiv.symm (fun value => MotherPhysicalLaws.eval law (input value))) = _
  rw [Equiv.apply_symm_apply]
  funext value
  exact (generated (input value)).trans (MotherPointwiseLaws.eval_eq original value)

def readStream (law : Base) : MotherStreamFormation.Carrier :=
  CurrentSampleAction.readInverse (MotherPhysicalLaws.eval law (input 0))

theorem readStream_surjective : Function.Surjective readStream := by
  intro original
  obtain ⟨law, generated, _⟩ := MotherPhysicalLaws.every_law
    (fun _ => MotherStreamFormation.read original)
  refine ⟨law, ?_⟩
  unfold readStream
  rw [generated]
  exact CurrentSampleAction.readInverse_read original

def slot (tag outer inner coordinate : ℕ) : ℕ :=
  Nat.pair tag (Nat.pair outer (Nat.pair inner coordinate))

def sample (law : Base) (tag outer inner coordinate : ℕ) (value : Stream) : ℝ :=
  MotherPhysicalLaws.eval law (input value) (slot tag outer inner coordinate)

def readNat (law : Base) (tag outer inner : ℕ) : ℕ :=
  Nat.floor (sample law tag outer inner 0 0)

/-- Both components are reconstructed from this Base law's actual complete evaluations. -/
def readMember (law : Base) (outer inner : ℕ) : MemberMaterial :=
  (pointwiseEquiv.symm (fun value coordinate => sample law 4 outer inner coordinate value),
    CurrentSampleAction.readInverse (fun coordinate => sample law 5 outer inner coordinate 0))

def readTerm (law : Base) (outer inner : ℕ) : Term :=
  (readMember law outer inner, readNat law 3 outer inner)

def readWord (law : Base) (outer : ℕ) : Word :=
  List.ofFn (fun inner : Fin (readNat law 2 outer 0) => readTerm law outer inner.val)

def readOrbit (law : Base) (outer : ℕ) : ℕ × Word :=
  (readNat law 1 outer 0, readWord law outer)

/-- One source law forms the complete original ordered Query value. -/
def readQuery (law : Base) : Query :=
  List.ofFn (fun outer : Fin (readNat law 0 0 0) => readOrbit law outer.val)

private theorem ofFn_getD {Value : Type*} (values : List Value) (fallback : Value) :
    List.ofFn (fun index : Fin values.length => values.getD index.val fallback) = values := by
  have pointwise : (fun index : Fin values.length => values.getD index.val fallback) =
      values.get := by
    funext index
    exact List.getD_eq_get values fallback index
  rw [pointwise]
  exact List.ofFn_get values

theorem readQuery_surjective : Function.Surjective readQuery := by
  intro query
  let fallback : Term :=
    ((pointwiseEquiv.symm (fun _ => 0), CurrentSampleAction.readInverse 0), 0)
  let orbit (outer : ℕ) : ℕ × Word := query.getD outer (0, [])
  let term (outer inner : ℕ) : Term := (orbit outer).2.getD inner fallback
  let fields (tag outer inner coordinate : ℕ) (value : Stream) : ℝ :=
    match tag with
    | 0 => query.length
    | 1 => (orbit outer).1
    | 2 => (orbit outer).2.length
    | 3 => (term outer inner).2
    | 4 => MotherPointwiseLaws.eval (term outer inner).1.1 value coordinate
    | 5 => MotherStreamFormation.read (term outer inner).1.2 coordinate
    | _ => 0
  let target (raw : MotherPhysicalLaws.Input) (address : ℕ) : ℝ :=
    fields address.unpair.1 address.unpair.2.unpair.1
      address.unpair.2.unpair.2.unpair.1 address.unpair.2.unpair.2.unpair.2 raw.2
  obtain ⟨law, generated, _⟩ := MotherPhysicalLaws.every_law target
  have sampled (tag outer inner coordinate : ℕ) (value : Stream) :
      sample law tag outer inner coordinate value = fields tag outer inner coordinate value := by
    unfold sample
    rw [generated]
    simp only [target, slot, Nat.unpair_pair, input]
  have countRead : readNat law 0 0 0 = query.length := by
    simp only [readNat, sampled, fields, Nat.floor_natCast]
  have stageRead (outer : ℕ) : readNat law 1 outer 0 = (orbit outer).1 := by
    simp only [readNat, sampled, fields, Nat.floor_natCast]
  have lengthRead (outer : ℕ) : readNat law 2 outer 0 = (orbit outer).2.length := by
    simp only [readNat, sampled, fields, Nat.floor_natCast]
  have addressRead (outer inner : ℕ) : readNat law 3 outer inner = (term outer inner).2 := by
    simp only [readNat, sampled, fields, Nat.floor_natCast]
  have memberRead (outer inner : ℕ) : readMember law outer inner = (term outer inner).1 := by
    apply Prod.ext
    · apply pointwiseEquiv.injective
      change pointwiseEquiv
        (pointwiseEquiv.symm (fun value coordinate => sample law 4 outer inner coordinate value)) = _
      rw [Equiv.apply_symm_apply]
      funext value coordinate
      rw [sampled]
      change MotherPointwiseLaws.eval (term outer inner).1.1 value coordinate =
        MotherPointwiseLaws.lawRead (term outer inner).1.1 value coordinate
      exact congrFun (MotherPointwiseLaws.eval_eq _ value) coordinate
    · change CurrentSampleAction.readInverse
        (fun coordinate => sample law 5 outer inner coordinate 0) = (term outer inner).1.2
      have samples : (fun coordinate => sample law 5 outer inner coordinate 0) =
          MotherStreamFormation.read (term outer inner).1.2 := by
        funext coordinate
        exact sampled 5 outer inner coordinate 0
      rw [samples]
      exact CurrentSampleAction.readInverse_read _
  have termRead (outer inner : ℕ) : readTerm law outer inner = term outer inner := by
    exact Prod.ext (memberRead outer inner) (addressRead outer inner)
  have wordRead (outer : ℕ) : readWord law outer = (orbit outer).2 := by
    unfold readWord
    rw [lengthRead]
    simp_rw [termRead]
    exact ofFn_getD (orbit outer).2 fallback
  have orbitRead (outer : ℕ) : readOrbit law outer = orbit outer :=
    Prod.ext (stageRead outer) (wordRead outer)
  refine ⟨law, ?_⟩
  unfold readQuery
  rw [countRead]
  simp_rw [orbitRead]
  exact ofFn_getD query (0, [])

abbrev CompiledAt (typeLaw actionLaw : Base) (parent : MotherVisit) (query : Query) :=
  type_of% ((MotherNativePhysicalQuery.nativeInquiry typeLaw actionLaw parent).compileInquiry query)

/-- The literal original compiler consumes the newly formed complete query. -/
def compileRead (typeLaw actionLaw : Base) (parent : MotherVisit) (law : Base) :
    Σ query : Query, CompiledAt typeLaw actionLaw parent query :=
  ⟨readQuery law,
    (MotherNativePhysicalQuery.nativeInquiry typeLaw actionLaw parent).compileInquiry (readQuery law)⟩

theorem every_original_query_compiled (typeLaw actionLaw : Base) (parent : MotherVisit)
    (query : Query) :
    ∃ law : Base, compileRead typeLaw actionLaw parent law =
      ⟨query, (MotherNativePhysicalQuery.nativeInquiry typeLaw actionLaw parent).compileInquiry query⟩ := by
  obtain ⟨law, formed⟩ := readQuery_surjective query
  refine ⟨law, ?_⟩
  unfold compileRead
  cases formed
  rfl

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherOriginalQueryValue
