import H0mework.Versions.R26b91feb.ReleaseMaterials.Scratch.FlyCNS.C3RootState
import H0mework.Versions.R26b91feb.ReleaseMaterials.Scratch.FlyCNS.C3BoundKernel
import H0mework.Versions.R26b91feb.ReleaseMaterials.Scratch.FlyCNS.SourceFiniteMinimalModel
import Mathlib.Tactic

set_option autoImplicit false
namespace FlyCNS.C3Reachable
open C3Successful

set_option maxHeartbeats 2000000 in
theorem signed_word_roundtrip (value : Int64) :
    (C3Integer.Word.mk 8 (C3Raw.signed #[value])).int 0=value := by
  simp [C3Raw.signed,C3Integer.Word.int,C3Integer.Word.bits,Array.forIn_eq_foldlM,
    ByteArray.get!,ByteArray.push,List.range'_succ,List.foldl]
  apply Int64.toBitVec_inj.mp 
  simp only [Int64.toBitVec_or,UInt64.toBitVec_mod,UInt64.toBitVec_toInt64,UInt64.toBitVec_shiftLeft,
    UInt64.toBitVec_shiftRight,Int64.toBitVec_toUInt64]

  apply BitVec.eq_of_getLsbD_eq_iff.mpr
  intro i within
  have byte_bit (n j : Nat) : (n%256).testBit j=(decide (j<8) && n.testBit j) :=
    Nat.testBit_mod_two_pow n 8 j
  have word_bit (n j : Nat) : (n%18446744073709551616).testBit j=(decide (j<64) && n.testBit j) :=
    Nat.testBit_mod_two_pow n 64 j
  interval_cases i <;> simp [BitVec.getLsbD,BitVec.toNat_umod,byte_bit,word_bit,Nat.testBit_shiftLeft,Nat.testBit_shiftRight]

theorem signed_word_bits (value : Int64) :
    (C3Integer.Word.mk 8 (C3Raw.signed #[value])).bits 0=value.toUInt64 := by
  have h := signed_word_roundtrip value
  change ((C3Integer.Word.mk 8 (C3Raw.signed #[value])).bits 0).toInt64=value at h
  have q := congrArg Int64.toUInt64 h
  simpa using q

def counter (n : Nat) : C3Integer.Word := ⟨8,C3Raw.signed #[Int64.ofNat n]⟩
theorem counter_bits (n : Nat) (bound : n<2^64) : ((counter n).bits 0).toNat=n := by
  rw [counter,signed_word_bits]
  change (UInt64.ofNat n).toNat=n
  change n%2^64=n
  exact Nat.mod_eq_of_lt bound
theorem counter_int (n : Nat) : (counter n).int 0=Int64.ofNat n := signed_word_roundtrip _

/-- The original complete result is generated recursively. A failed prefix
keeps its original error; no successor or future table is supplied. -/
def generate (m : C3Macro.Material) (seed : Except String Current) : Nat → Except String Current
  | 0 => seed
  | n+1 => do
    let before ← generate m seed n
    let result ← C3Successful.successor m before
    return result.current

theorem finish_visit {m : C3Macro.Material} {before : Current} {operation : C3Native.Operation}
    {g : C3Macro.Generated} {result : Result}
    (paid : C3Successful.finish m before operation g=.ok result) :
    result.current.original.visit=g.current.visit := by
  unfold C3Successful.finish at paid
  simp only [bind,pure,Except.bind,Except.pure] at paid
  cases hs : C3History.capture g.current.programme.environmentHistory.toList with
  | error why => simp only [hs] at paid; contradiction
  | ok slots =>
    simp only [hs] at paid
    cases hd : C3Document.generate before.original.sourceDocument (C3History.events slots)
      g.current.programme.numerical.neural.plasticChanges with
    | error why => simp only [hd] at paid; contradiction
    | ok document =>
      simp only [hd] at paid
      cases paid
      rfl

theorem finish_body {m : C3Macro.Material} {before : Current} {operation : C3Native.Operation}
    {g : C3Macro.Generated} {result : Result}
    (paid : C3Successful.finish m before operation g=.ok result) :
    result.current.original.bodyWords=g.current.bodyWords := by
  unfold C3Successful.finish at paid
  simp only [bind,pure,Except.bind,Except.pure] at paid
  cases hs : C3History.capture g.current.programme.environmentHistory.toList with
  | error why => simp only [hs] at paid; contradiction
  | ok slots =>
    simp only [hs] at paid
    cases hd : C3Document.generate before.original.sourceDocument (C3History.events slots)
      g.current.programme.numerical.neural.plasticChanges with
    | error why => simp only [hd] at paid; contradiction
    | ok document => simp only [hd] at paid;cases paid;rfl

theorem controller_body {operation : C3Native.Operation} {before admitted : C3Macro.Current}
    (paid : C3Macro.controller operation before=.ok admitted) : admitted.bodyWords=before.bodyWords := by
  cases operation <;> simp only [C3Macro.controller] at paid
  · cases paid;rfl
  · split at paid <;> (try contradiction);cases paid;rfl
  · split at paid <;> (try contradiction);cases paid;rfl

theorem generated_body_counter (before : Vector C3Integer.Word 25) (after : C3Native.State) (ticks : Nat) :
    (C3Registered.generatedBodies before after ticks).get ⟨20,by decide⟩=
      ⟨8,C3Raw.signed #[(before.get ⟨20,by decide⟩).int 0+Int64.ofNat (10*ticks)]⟩ := by
  unfold C3Registered.generatedBodies
  simp only [Vector.get,Fin.val_cast,Vector.toArray_ofFn,Array.getElem_ofFn]
  rfl

set_option maxHeartbeats 2000000 in
theorem generated_counter {m : C3Macro.Material} {operation : C3Native.Operation} {before : C3Macro.Current}
    {g : C3Macro.Generated} {n : Nat}
    (original : before.bodyWords.get ⟨20,by decide⟩=counter n)
    (paid : C3Macro.generate m operation before=.ok g) :
    g.current.bodyWords.get ⟨20,by decide⟩=counter (n+10*C3Macro.neuralTicks operation) := by
  unfold C3Macro.generate at paid
  split at paid
  next bad => contradiction
  next legal =>
    cases hc : C3Macro.controller operation before with
    | error why => simp [hc] at paid
    | ok admitted =>
      simp only [hc] at paid
      simp only [Vector.get,Fin.val_cast] at paid original
      cases hr : C3Macro.runCycles m before admitted.programme ((before.bodyWords.toArray[20]).bits 0).toNat (C3Macro.neuralTicks operation) with
      | error why =>
        simp only [Vector.getElem_toArray] at paid
        simp only [Vector.getElem_toArray] at hr
        rw [hr] at paid
        contradiction
      | ok later =>
        cases later with
        | mk programme cycles =>
          simp only [Vector.getElem_toArray] at hr
          simp only [Vector.getElem_toArray] at paid
          rw [hr] at paid
          cases paid
          rw [generated_body_counter]
          have old : before.bodyWords.get ⟨20,by decide⟩=counter n := by simpa [Vector.get,Fin.val_cast] using original
          rw [old,counter_int]
          simp only [counter,Int64.ofNat_add]

theorem action_visit {m : C3Macro.Material} {operation : C3Native.Operation} {before : Current} {result : Result}
    (paid : C3Successful.action m operation before=.ok result) :
    result.current.original.visit=before.original.visit+1 := by
  unfold C3Successful.action at paid
  split at paid
  next bad => contradiction
  next legal =>
    simp only [bind,Except.bind] at paid
    split at paid
    next overflow => contradiction
    next bounded =>
      cases hg : C3Macro.generate m operation { before.original with programme := { before.original.programme with environmentHistory:=C3History.events before.history } } with
      | error why => simp [hg] at paid
      | ok g =>
        simp only [hg] at paid
        calc
          result.current.original.visit=g.current.visit := finish_visit paid
          _=({ before.original with programme := { before.original.programme with environmentHistory:=C3History.events before.history } }).visit+1 := C3Macro.generated_visit hg
          _=before.original.visit+1 := rfl


theorem action_counter {m : C3Macro.Material} {operation : C3Native.Operation} {before : Current}
    {result : Result} {n : Nat}
    (original : before.original.bodyWords.get ⟨20,by decide⟩=counter n)
    (paid : C3Successful.action m operation before=.ok result) :
    result.current.original.bodyWords.get ⟨20,by decide⟩=counter (n+10*C3Macro.neuralTicks operation) := by
  unfold C3Successful.action at paid
  split at paid
  next bad => contradiction
  next legal =>
    simp only [bind,Except.bind] at paid
    split at paid
    next overflow => contradiction
    next bounded =>
      cases hg : C3Macro.generate m operation { before.original with programme := { before.original.programme with environmentHistory:=C3History.events before.history } } with
      | error why => simp [hg] at paid
      | ok g =>
        simp only [hg] at paid
        rw [finish_body paid]
        exact generated_counter (before:={ before.original with programme := { before.original.programme with environmentHistory:=C3History.events before.history } }) original hg

theorem action_signed_bound {m : C3Macro.Material} {operation : C3Native.Operation} {before : Current}
    {result : Result} {n : Nat} (range : n<2^64)
    (original : before.original.bodyWords.get ⟨20,by decide⟩=counter n)
    (paid : C3Successful.action m operation before=.ok result) : n+10*C3Macro.neuralTicks operation≤C3Clock.signedLimit := by
  unfold C3Successful.action at paid
  split at paid
  next bad => contradiction
  next legal =>
    simp only [bind,Except.bind] at paid
    split at paid
    next overflow => contradiction
    next bounded =>
      simp only [original,counter_bits n range] at bounded
      omega

theorem wrong_letter (m : C3Macro.Material) (before : Current) (operation : C3Native.Operation)
    (different : C3Native.operationAt before.original.visit≠operation) :
    C3Successful.action m operation before=.error "operation not admitted at this source incidence" := by
  unfold C3Successful.action
  have flag : (C3Native.operationAt before.original.visit != operation)=true := by
    cases h : C3Native.operationAt before.original.visit <;> cases operation <;> simp_all
  rw [if_pos flag]
  rfl

/-- Every accepted word has the same complete source-generated endpoint
as its fixed autonomous prefix. Unregistered words retain the original error. -/
inductive Reachable (m : C3Macro.Material) (seed : Current) : Nat → Current → Prop
  | initial : Reachable m seed 0 seed
  | next {n : Nat} {before : Current} {result : Result}
      (previous : Reachable m seed n before)
      (generated : C3Successful.successor m before=.ok result) :
      Reachable m seed (n+1) result.current

theorem reachable_visit {m : C3Macro.Material} {seed : Current} {n : Nat} {current : Current}
    (occurred : Reachable m seed n current) : current.original.visit=seed.original.visit+n := by
  induction occurred with
  | initial => simp
  | next previous generated ih =>
    have step := action_visit generated
    omega

def ClockAligned (current : Current) : Prop :=
  current.original.bodyWords.get ⟨20,by decide⟩=counter (C3Clock.generate current.original.visit).physics

theorem clock_increment (visit : Nat) :
    (C3Clock.generate (visit+1)).physics=(C3Clock.generate visit).physics+
      10*C3Macro.neuralTicks (C3Native.operationAt visit) := by
  simp only [C3Clock.generate,C3Clock.next,C3Clock.generated_visit,C3Native.operationAt]
  by_cases first : visit=55
  · subst visit;simp [C3Macro.neuralTicks]
  by_cases second : visit=58
  · subst visit;simp [C3Macro.neuralTicks]
  simp [first,second,C3Macro.neuralTicks]

theorem action_legal {m : C3Macro.Material} {operation : C3Native.Operation} {before : Current} {result : Result}
    (paid : C3Successful.action m operation before=.ok result) :
    operation=C3Native.operationAt before.original.visit := by
  by_contra wrong
  have failed := wrong_letter m before operation (Ne.symm wrong)
  rw [failed] at paid
  contradiction

theorem reachable_clock {m : C3Macro.Material} {seed : Current} {n : Nat} {current : Current}
    (initial : ClockAligned seed)
    (initial_bound : (C3Clock.generate seed.original.visit).physics≤C3Clock.signedLimit)
    (occurred : Reachable m seed n current) :
    ClockAligned current ∧ (C3Clock.generate current.original.visit).physics≤C3Clock.signedLimit := by
  induction occurred with
  | initial => exact ⟨initial,initial_bound⟩
  | @next n before result previous paid ih =>
    have range : (C3Clock.generate before.original.visit).physics<2^64 := by
      have h:=ih.2
      unfold C3Clock.signedLimit at h
      omega
    have bounded:=action_signed_bound range ih.1 paid
    have countereq:=action_counter ih.1 paid
    have visit:=action_visit paid
    constructor
    · unfold ClockAligned
      rw [countereq,visit,clock_increment]
    · rw [visit,clock_increment]
      exact bounded

theorem reachable_visit_bound {m : C3Macro.Material} {seed : Current} {n : Nat} {current : Current}
    (initial : ClockAligned seed)
    (initial_bound : (C3Clock.generate seed.original.visit).physics≤C3Clock.signedLimit)
    (occurred : Reachable m seed n current) : current.original.visit≤C3Clock.signedLimit/1000+2 := by
  exact C3Clock.successful_visit_bound current.original.visit
    (by simpa [C3Clock.successfulSave] using (reachable_clock initial initial_bound occurred).2)

theorem generate_reachable {m : C3Macro.Material} {seed current : Current} {n : Nat}
    (generated : generate m (.ok seed) n=.ok current) : Reachable m seed n current := by
  induction n generalizing current with
  | zero => cases generated;exact .initial
  | succ n ih =>
    simp only [generate,bind,pure,Except.bind,Except.pure] at generated
    cases hb : generate m (.ok seed) n with
    | error why => simp only [hb] at generated;contradiction
    | ok before =>
      simp only [hb] at generated
      cases hn : C3Successful.successor m before with
      | error why => simp only [hn] at generated;contradiction
      | ok result =>
        simp only [hn] at generated
        cases generated
        exact .next (ih hb) hn

theorem reachable_generated {m : C3Macro.Material} {seed current : Current} {n : Nat}
    (occurred : Reachable m seed n current) : generate m (.ok seed) n=.ok current := by
  induction occurred with
  | initial => rfl
  | next previous paid ih => simp [generate,ih,paid,bind,Except.bind,pure,Except.pure]

theorem reachable_unique {m : C3Macro.Material} {seed left right : Current} {n : Nat}
    (first : Reachable m seed n left) (second : Reachable m seed n right) : left=right := by
  have same : Except.ok (ε:=String) left=.ok right := (reachable_generated first).symm.trans (reachable_generated second)
  exact Except.ok.inj same

theorem word_ext (left right : C3Integer.Word) (width : left.width=right.width) (bytes : left.bytes=right.bytes) : left=right := by
  cases left;cases right;simp_all

structure Seed where
  private mk ::
  initial : Current
  visit : initial.original.visit=2
  physics : initial.original.bodyWords.get ⟨20,by decide⟩=counter 2000

def admitSeed (current : Current) : Except String Seed :=
  if visit : current.original.visit=2 then
    let word:=current.original.bodyWords.get ⟨20,by decide⟩
    if width : word.width=8 then
      if bytes : word.bytes=(counter 2000).bytes then
        .ok ⟨current,visit,by exact word_ext word (counter 2000) width bytes⟩
      else .error "source boundary changed its original physics2000"
    else .error "source boundary changed its original signed counter dtype"
  else .error "source finite carrier starts at the original current2"

def fromRoot (source : SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.FlyCNS.ContentReentryIO.Source) :
    Except String Seed := do
  let current ← SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.FlyCNS.C3RootState.decode source source.initial
  admitSeed current

theorem Seed.clock (seed : Seed) : ClockAligned seed.initial := by
  unfold ClockAligned
  rw [seed.visit]
  exact seed.physics

theorem Seed.signed_bound (seed : Seed) :
    (C3Clock.generate seed.initial.original.visit).physics≤C3Clock.signedLimit := by
  rw [seed.visit]
  decide

def stateBound : Nat := C3Clock.signedLimit/1000+3

abbrev Carrier (m : C3Macro.Material) (seed : Seed) :=
  {current : Current // ∃ n,Reachable m seed.initial n current}

def address {m : C3Macro.Material} {seed : Seed} (state : Carrier m seed) : Fin stateBound :=
  ⟨state.val.original.visit,by
    rcases state.property with ⟨n,h⟩
    have b:=reachable_visit_bound seed.clock seed.signed_bound h
    unfold stateBound
    omega⟩

theorem address_injective (m : C3Macro.Material) (seed : Seed) :
    Function.Injective (address (m:=m) (seed:=seed)) := by
  intro left right equal
  rcases left.property with ⟨a,ha⟩
  rcases right.property with ⟨b,hb⟩
  have visits := congrArg Fin.val equal
  have va:=reachable_visit ha
  have vb:=reachable_visit hb
  have ab : a=b := by change left.val.original.visit=right.val.original.visit at visits;omega
  subst b
  exact Subtype.ext (reachable_unique ha hb)

@[instance_reducible] noncomputable def carrierFinite (m : C3Macro.Material) (seed : Seed) : Fintype (Carrier m seed) :=
  Fintype.ofInjective address (address_injective m seed)

end FlyCNS.C3Reachable
