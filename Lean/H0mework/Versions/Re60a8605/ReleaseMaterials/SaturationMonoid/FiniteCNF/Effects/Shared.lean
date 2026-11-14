import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.FiniteCNF.Effects.Gate

set_option autoImplicit false
namespace SaturationMonoid.ComplexityProjection.SATSource.EffectDAG
open InterferenceProgram

abbrev Refs := Nat × Nat
abbrev Stock := Reduce.State

private def put (stock : Stock) (node : Node) : Stock × Nat := Reduce.smartIntern stock node

def xorGate (stock : Stock) (a b : Nat) : Stock × Nat :=
  if a=b then (stock,0) else if a=0 then (stock,b) else if b=0 then (stock,a) else
    put stock (.bxor (min a b) (max a b))

def notGate (stock : Stock) (a : Nat) : Stock × Nat :=
  if a=0 then (stock,1) else if a=1 then (stock,0) else
    match stock.code[a]? with
    | some (.bnot b) => (stock,b)
    | _ => put stock (.bnot a)

def andGate (stock : Stock) (a b : Nat) : Stock × Nat :=
  if a=0 ∨ b=0 then (stock,0) else if a=1 then (stock,b) else if b=1 ∨ a=b then (stock,a) else
    if stock.code[a]?=some (.bnot b) ∨ stock.code[b]?=some (.bnot a) then (stock,0) else
      put stock (.band (min a b) (max a b))

def add (stock : Stock) (left right : Refs) : Stock × Refs :=
  let base := xorGate stock left.1 right.1
  let delta := xorGate base.1 left.2 right.2
  (delta.1,(base.2,delta.2))

def multiply (stock : Stock) (left right : Refs) : Stock × Refs :=
  let base := andGate stock left.1 right.1
  let first := andGate base.1 left.1 right.2
  let second := andGate first.1 left.2 right.1
  let mixed := andGate second.1 left.2 right.2
  let cross := xorGate mixed.1 first.2 second.2
  let delta := xorGate cross.1 cross.2 mixed.2
  (delta.1,(base.2,delta.2))

def invert (stock : Stock) (value : Refs) : Stock × Refs :=
  let base := notGate stock value.1
  (base.1,(base.2,value.2))

def select (stock : Stock) (control left right : Refs) : Stock × Refs :=
  let difference := add stock left right
  let action := multiply difference.1 control difference.2
  add action.1 left action.2

structure Frame where
  stock : Stock
  mapping : Array Refs
  deriving Repr

def initial : Frame := ⟨(Reduce.smartIntern Reduce.initial (.constant 1)).1,#[]⟩

def operation (address : Nat) (stock : Stock) (read : Nat → Refs) (node : Node) : Option (Stock × Refs) :=
  match node with
    | .add _ _ => none
    | .constant value => some (stock,((if truth value then 1 else 0),0))
    | .input i =>
        if i=address then some (stock,(0,1)) else
          let generated := put stock (.input i)
          some (generated.1,(generated.2,0))
    | .mul a b | .band a b => some (multiply stock (read a) (read b))
    | .bxor a b => some (add stock (read a) (read b))
    | .bnot a => some (invert stock (read a))
    | .neg a => some (stock,read a)
    | .phase _ => some (stock,(1,0))
    | .select c a b => some (select stock (read c) (read a) (read b))

def emit (address : Nat) (frame : Frame) (node : Node) : Option Frame :=
  (operation address frame.stock (fun i => frame.mapping.getD i (0,0)) node).map
    (fun generated => ⟨generated.1,frame.mapping.push generated.2⟩)

def build (address : Nat) : List Node → Frame → Option Frame
  | [],frame => some frame
  | node::rest,frame => do build address rest (← emit address frame node)

def generate (program : Program) (address : Nat) : Option (Stock × Refs) := do
  let frame ← build address program.code.toList initial
  pure (frame.stock,frame.mapping.getD program.weight.val (0,0))

def existentialRoot (stock : Stock) (value : Refs) : Stock × Nat :=
  let complement := notGate stock value.1
  let newPart := andGate complement.1 complement.2 value.2
  xorGate newPart.1 value.1 newPart.2

def program (stock : Stock) (root : Nat) : Program :=
  if valid : 0 < stock.code.size ∧ root < stock.code.size then
    ⟨stock.code,⟨root,valid.2⟩,⟨0,valid.1⟩⟩
  else Affine.Boolean.constant false

def eliminate (source : Program) (address : Nat) : Program :=
  match generate source address with
  | none => Affine.Boolean.existential source address
  | some (stock,refs) =>
      let generated := existentialRoot stock refs
      Cone.pruneCone (program generated.1 generated.2)

def read (stock : Stock) (point : Nat → Bool) (i : Nat) : Bool := truth ((run point stock.code).getD i 0)

def Good (stock : Stock) : Prop := Reduce.Valid stock ∧ Reduce.Forward stock.code ∧
  2 ≤ stock.code.size ∧ ∀ point, (run point stock.code).getD 1 0=1

def Extends (before after : Stock) : Prop := before.code.size ≤ after.code.size ∧
  ∀ point i, i < before.code.size → read after point i=read before point i

theorem extends_refl (stock : Stock) : Extends stock stock := ⟨le_rfl,fun _ _ _ => rfl⟩

theorem extends_trans (a b c : Stock) (first : Extends a b) (second : Extends b c) : Extends a c := by
  refine ⟨first.1.trans second.1,?_⟩
  intro point i inside
  rw [second.2 point i (inside.trans_le first.1),first.2 point i inside]

theorem read_zero (stock : Stock) (good : Good stock) (point : Nat → Bool) : read stock point 0=false := by
  rw [read,good.1.1 point]
  rfl

theorem read_one (stock : Stock) (good : Good stock) (point : Nat → Bool) : read stock point 1=true := by
  rw [read,good.2.2.2 point]
  rfl

theorem put_good (stock : Stock) (good : Good stock) (node : Node) (inside : Reduce.Within stock.code.size node) :
    Good (put stock node).1 := by
  have nonempty : 0 < stock.code.size := by have size := good.2.2.1; omega
  have generated := Reduce.smartIntern_sound stock good.1 node inside nonempty
  refine ⟨generated.1,?_,?_,?_⟩
  · exact Reduce.intern_forward stock good.2.1 (Reduce.foldNode stock node) (Reduce.foldNode_within stock node inside)
  · exact good.2.2.1.trans generated.2.1
  · intro point
    rw [put,Reduce.smartIntern_preserves stock good.1 node inside nonempty point 1 (by have size := good.2.2.1; omega)]
    exact good.2.2.2 point

theorem put_extends (stock : Stock) (good : Good stock) (node : Node) (inside : Reduce.Within stock.code.size node) :
    Extends stock (put stock node).1 := by
  have nonempty : 0 < stock.code.size := by have size := good.2.2.1; omega
  have generated := Reduce.smartIntern_sound stock good.1 node inside nonempty
  refine ⟨generated.2.1,?_⟩
  intro point i earlier
  exact congrArg truth (Reduce.smartIntern_preserves stock good.1 node inside nonempty point i earlier)

theorem put_bound (stock : Stock) (good : Good stock) (node : Node) (inside : Reduce.Within stock.code.size node) :
    (put stock node).2 < (put stock node).1.code.size :=
  (Reduce.smartIntern_sound stock good.1 node inside (by have size := good.2.2.1; omega)).2.2.2.1

theorem put_read (stock : Stock) (good : Good stock) (node : Node) (inside : Reduce.Within stock.code.size node) (point : Nat → Bool) :
    read (put stock node).1 point (put stock node).2=truth (node.run point (run point stock.code)) :=
  congrArg truth ((Reduce.smartIntern_sound stock good.1 node inside (by have size := good.2.2.1; omega)).2.2.2.2.2 point)

theorem put_size (stock : Stock) (node : Node) : (put stock node).1.code.size ≤ stock.code.size+1 :=
  (Reduce.smartIntern_sizes stock node).1

theorem initial_good : Good initial.stock := by
  have added := Reduce.smartIntern_sound Reduce.initial Reduce.initial_valid (.constant 1)
    (by simp [Reduce.Within,Node.refs]) (by decide)
  refine ⟨added.1,?_,by decide,?_⟩
  · exact Reduce.intern_forward Reduce.initial Reduce.initial_forward (.constant 1) (by simp [Reduce.Within,Node.refs])
  · intro point
    rfl

theorem xorGate_spec (stock : Stock) (good : Good stock) (a b : Nat)
    (left : a < stock.code.size) (right : b < stock.code.size) :
    Good (xorGate stock a b).1 ∧ Extends stock (xorGate stock a b).1 ∧
      (xorGate stock a b).2 < (xorGate stock a b).1.code.size ∧
      ∀ point, read (xorGate stock a b).1 point (xorGate stock a b).2=(read stock point a ^^ read stock point b) := by
  simp only [xorGate]
  split
  · rename_i same
    refine ⟨good,extends_refl stock,?_,?_⟩
    · change 0 < stock.code.size
      have size := good.2.2.1
      omega
    intro point
    simp only [read_zero stock good point,same,Bool.xor_self]
  · split
    · rename_i zero
      refine ⟨good,extends_refl stock,right,?_⟩
      intro point
      simp only [zero,read_zero stock good point,Bool.false_xor]
    · split
      · rename_i zero
        refine ⟨good,extends_refl stock,left,?_⟩
        intro point
        simp only [zero,read_zero stock good point,Bool.xor_false]
      · have inside : Reduce.Within stock.code.size (.bxor (min a b) (max a b)) := by
          simp only [Reduce.Within,Node.refs,List.mem_cons,List.not_mem_nil,or_false]
          intro i member
          rcases member with rfl | rfl <;> omega
        refine ⟨put_good stock good _ inside,put_extends stock good _ inside,put_bound stock good _ inside,?_⟩
        intro point
        rw [put_read stock good _ inside point]
        simp only [Node.run,truth_bit]
        rcases le_total a b with ordered | ordered
        · rw [Nat.min_eq_left ordered,Nat.max_eq_right ordered]
          rfl
        · rw [Nat.min_eq_right ordered,Nat.max_eq_left ordered]
          exact Bool.xor_comm _ _

theorem negated_read (stock : Stock) (good : Good stock) (a b : Nat) (inside : a < stock.code.size)
    (node : stock.code[a]?=some (.bnot b)) (point : Nat → Bool) : read stock point a=!(read stock point b) := by
  have source := ArenaAction.run_equation stock.code good.2.1 point a inside
  have shape : stock.code.getD a (.constant 0)=.bnot b := by rw [Array.getD_eq_getD_getElem?,node]; rfl
  rw [shape] at source
  rw [read,source]
  exact truth_bit _

theorem negated_bound (stock : Stock) (good : Good stock) (a b : Nat) (inside : a < stock.code.size)
    (node : stock.code[a]?=some (.bnot b)) : b < stock.code.size := by
  have shape : stock.code[a]=.bnot b := by simpa only [Array.getElem?_eq_getElem inside,Option.some.injEq] using node
  have before := good.2.1 a inside
  rw [shape] at before
  exact (before b (by simp [Node.refs])).trans inside

theorem notGate_spec (stock : Stock) (good : Good stock) (a : Nat) (inside : a < stock.code.size) :
    Good (notGate stock a).1 ∧ Extends stock (notGate stock a).1 ∧
      (notGate stock a).2 < (notGate stock a).1.code.size ∧
      ∀ point, read (notGate stock a).1 point (notGate stock a).2=!(read stock point a) := by
  simp only [notGate]
  split
  · rename_i zero
    refine ⟨good,extends_refl stock,?_,?_⟩
    · change 1 < stock.code.size
      have size := good.2.2.1
      omega
    · intro point
      rw [zero,read_one stock good point,read_zero stock good point]
      rfl
  · split
    · rename_i one
      refine ⟨good,extends_refl stock,?_,?_⟩
      · change 0 < stock.code.size
        have size := good.2.2.1
        omega
      · intro point
        rw [one,read_zero stock good point,read_one stock good point]
        rfl
    · split
      · rename_i b node
        refine ⟨good,extends_refl stock,negated_bound stock good a b inside node,?_⟩
        intro point
        rw [negated_read stock good a b inside node point,Bool.not_not]
      · have bounded : Reduce.Within stock.code.size (.bnot a) := by simp [Reduce.Within,Node.refs,inside]
        refine ⟨put_good stock good _ bounded,put_extends stock good _ bounded,put_bound stock good _ bounded,?_⟩
        intro point
        rw [put_read stock good _ bounded point]
        exact truth_bit _

theorem andGate_spec (stock : Stock) (good : Good stock) (a b : Nat)
    (left : a < stock.code.size) (right : b < stock.code.size) :
    Good (andGate stock a b).1 ∧ Extends stock (andGate stock a b).1 ∧
      (andGate stock a b).2 < (andGate stock a b).1.code.size ∧
      ∀ point, read (andGate stock a b).1 point (andGate stock a b).2=(read stock point a && read stock point b) := by
  have zeroBound : 0 < stock.code.size := by have size := good.2.2.1; omega
  simp only [andGate]
  split
  · rename_i zero
    refine ⟨good,extends_refl stock,zeroBound,?_⟩
    intro point
    rcases zero with zero | zero
    · simp only [zero,read_zero stock good point,Bool.false_and]
    · simp only [zero,read_zero stock good point,Bool.and_false]
  · split
    · rename_i one
      refine ⟨good,extends_refl stock,right,?_⟩
      intro point
      simp only [one,read_one stock good point,Bool.true_and]
    · split
      · rename_i simple
        refine ⟨good,extends_refl stock,left,?_⟩
        intro point
        rcases simple with one | same
        · simp only [one,read_one stock good point,Bool.and_true]
        · simp only [same,Bool.and_self]
      · split
        · rename_i complement
          refine ⟨good,extends_refl stock,zeroBound,?_⟩
          intro point
          rw [read_zero stock good point]
          rcases complement with opposite | opposite
          · rw [negated_read stock good a b left opposite point]
            simp
          · rw [negated_read stock good b a right opposite point]
            simp
        · have inside : Reduce.Within stock.code.size (.band (min a b) (max a b)) := by
            simp only [Reduce.Within,Node.refs,List.mem_cons,List.not_mem_nil,or_false]
            intro i member
            rcases member with rfl | rfl <;> omega
          refine ⟨put_good stock good _ inside,put_extends stock good _ inside,put_bound stock good _ inside,?_⟩
          intro point
          rw [put_read stock good _ inside point]
          simp only [Node.run,truth_bit]
          rcases le_total a b with ordered | ordered
          · rw [Nat.min_eq_left ordered,Nat.max_eq_right ordered]
            rfl
          · rw [Nat.min_eq_right ordered,Nat.max_eq_left ordered]
            exact Bool.and_comm _ _

def PairWithin (stock : Stock) (value : Refs) : Prop := value.1 < stock.code.size ∧ value.2 < stock.code.size
def pairRead (stock : Stock) (point : Nat → Bool) (value : Refs) : EffectGate.Pair := (read stock point value.1,read stock point value.2)

theorem pairWithin_mono (before after : Stock) (change : Extends before after) (value : Refs) (inside : PairWithin before value) :
    PairWithin after value := ⟨inside.1.trans_le change.1,inside.2.trans_le change.1⟩

theorem pairRead_preserves (before after : Stock) (change : Extends before after) (value : Refs) (inside : PairWithin before value) (point : Nat → Bool) :
    pairRead after point value=pairRead before point value := by
  simp only [pairRead,change.2 point value.1 inside.1,change.2 point value.2 inside.2]

theorem add_spec (stock : Stock) (good : Good stock) (left right : Refs)
    (leftIn : PairWithin stock left) (rightIn : PairWithin stock right) :
    Good (add stock left right).1 ∧ Extends stock (add stock left right).1 ∧
      PairWithin (add stock left right).1 (add stock left right).2 ∧
      ∀ point, pairRead (add stock left right).1 point (add stock left right).2=EffectGate.add (pairRead stock point left) (pairRead stock point right) := by
  let base := xorGate stock left.1 right.1
  let delta := xorGate base.1 left.2 right.2
  have first := xorGate_spec stock good left.1 right.1 leftIn.1 rightIn.1
  have second := xorGate_spec base.1 first.1 left.2 right.2 (leftIn.2.trans_le first.2.1.1) (rightIn.2.trans_le first.2.1.1)
  change Good delta.1 ∧ Extends stock delta.1 ∧ PairWithin delta.1 (base.2,delta.2) ∧ _
  refine ⟨second.1,extends_trans stock base.1 delta.1 first.2.1 second.2.1,
    ⟨first.2.2.1.trans_le second.2.1.1,second.2.2.1⟩,?_⟩
  intro point
  apply Prod.ext
  · change read delta.1 point base.2=(_ ^^ _)
    rw [second.2.1.2 point base.2 first.2.2.1,first.2.2.2 point]
    rfl
  · change read delta.1 point delta.2=(_ ^^ _)
    rw [second.2.2.2 point,first.2.1.2 point left.2 leftIn.2,first.2.1.2 point right.2 rightIn.2]
    rfl

theorem invert_spec (stock : Stock) (good : Good stock) (value : Refs) (inside : PairWithin stock value) :
    Good (invert stock value).1 ∧ Extends stock (invert stock value).1 ∧
      PairWithin (invert stock value).1 (invert stock value).2 ∧
      ∀ point, pairRead (invert stock value).1 point (invert stock value).2=EffectGate.invert (pairRead stock point value) := by
  let generated := notGate stock value.1
  have result := notGate_spec stock good value.1 inside.1
  refine ⟨result.1,result.2.1,⟨result.2.2.1,inside.2.trans_le result.2.1.1⟩,?_⟩
  intro point
  apply Prod.ext
  · exact result.2.2.2 point
  · exact result.2.1.2 point value.2 inside.2

theorem multiply_spec (stock : Stock) (good : Good stock) (left right : Refs)
    (leftIn : PairWithin stock left) (rightIn : PairWithin stock right) :
    Good (multiply stock left right).1 ∧ Extends stock (multiply stock left right).1 ∧
      PairWithin (multiply stock left right).1 (multiply stock left right).2 ∧
      ∀ point, pairRead (multiply stock left right).1 point (multiply stock left right).2=
        EffectGate.multiply (pairRead stock point left) (pairRead stock point right) := by
  let base := andGate stock left.1 right.1
  let first := andGate base.1 left.1 right.2
  let second := andGate first.1 left.2 right.1
  let mixed := andGate second.1 left.2 right.2
  let cross := xorGate mixed.1 first.2 second.2
  let delta := xorGate cross.1 cross.2 mixed.2
  have hb := andGate_spec stock good left.1 right.1 leftIn.1 rightIn.1
  have hf := andGate_spec base.1 hb.1 left.1 right.2 (leftIn.1.trans_le hb.2.1.1) (rightIn.2.trans_le hb.2.1.1)
  have ef : Extends stock first.1 := extends_trans stock base.1 first.1 hb.2.1 hf.2.1
  have hs := andGate_spec first.1 hf.1 left.2 right.1 (leftIn.2.trans_le ef.1) (rightIn.1.trans_le ef.1)
  have es : Extends stock second.1 := extends_trans stock first.1 second.1 ef hs.2.1
  have hm := andGate_spec second.1 hs.1 left.2 right.2 (leftIn.2.trans_le es.1) (rightIn.2.trans_le es.1)
  have em : Extends stock mixed.1 := extends_trans stock second.1 mixed.1 es hm.2.1
  have efm : Extends first.1 mixed.1 := extends_trans first.1 second.1 mixed.1 hs.2.1 hm.2.1
  have hc := xorGate_spec mixed.1 hm.1 first.2 second.2 (hf.2.2.1.trans_le efm.1) (hs.2.2.1.trans_le hm.2.1.1)
  have ec : Extends stock cross.1 := extends_trans stock mixed.1 cross.1 em hc.2.1
  have hd := xorGate_spec cross.1 hc.1 cross.2 mixed.2 hc.2.2.1 (hm.2.2.1.trans_le hc.2.1.1)
  have ed : Extends stock delta.1 := extends_trans stock cross.1 delta.1 ec hd.2.1
  have ebm : Extends base.1 mixed.1 := extends_trans base.1 first.1 mixed.1 hf.2.1 efm
  have ebc : Extends base.1 cross.1 := extends_trans base.1 mixed.1 cross.1 ebm hc.2.1
  have ebd : Extends base.1 delta.1 := extends_trans base.1 cross.1 delta.1 ebc hd.2.1
  change Good delta.1 ∧ Extends stock delta.1 ∧ PairWithin delta.1 (base.2,delta.2) ∧ _
  refine ⟨hd.1,ed,⟨hb.2.2.1.trans_le ebd.1,hd.2.2.1⟩,?_⟩
  intro point
  have firstRead : read mixed.1 point first.2=(read stock point left.1 && read stock point right.2) := by
    rw [efm.2 point first.2 hf.2.2.1,hf.2.2.2 point,hb.2.1.2 point left.1 leftIn.1,hb.2.1.2 point right.2 rightIn.2]
  have secondRead : read mixed.1 point second.2=(read stock point left.2 && read stock point right.1) := by
    rw [hm.2.1.2 point second.2 hs.2.2.1,hs.2.2.2 point,ef.2 point left.2 leftIn.2,ef.2 point right.1 rightIn.1]
  have mixedRead : read cross.1 point mixed.2=(read stock point left.2 && read stock point right.2) := by
    rw [hc.2.1.2 point mixed.2 hm.2.2.1,hm.2.2.2 point,es.2 point left.2 leftIn.2,es.2 point right.2 rightIn.2]
  apply Prod.ext
  · change read delta.1 point base.2=(_ && _)
    rw [ebd.2 point base.2 hb.2.2.1,hb.2.2.2 point]
    rfl
  · change read delta.1 point delta.2=(((_ && _) ^^ (_ && _)) ^^ (_ && _))
    rw [hd.2.2.2 point,hc.2.2.2 point,firstRead,secondRead,mixedRead]
    rfl

theorem select_spec (stock : Stock) (good : Good stock) (control left right : Refs)
    (controlIn : PairWithin stock control) (leftIn : PairWithin stock left) (rightIn : PairWithin stock right) :
    Good (select stock control left right).1 ∧ Extends stock (select stock control left right).1 ∧
      PairWithin (select stock control left right).1 (select stock control left right).2 ∧
      ∀ point, pairRead (select stock control left right).1 point (select stock control left right).2=
        EffectGate.select (pairRead stock point control) (pairRead stock point left) (pairRead stock point right) := by
  let difference := add stock left right
  let action := multiply difference.1 control difference.2
  have first := add_spec stock good left right leftIn rightIn
  have second := multiply_spec difference.1 first.1 control difference.2
    (pairWithin_mono stock difference.1 first.2.1 control controlIn) first.2.2.1
  have next : Extends stock action.1 := extends_trans stock difference.1 action.1 first.2.1 second.2.1
  have last := add_spec action.1 second.1 left action.2
    (pairWithin_mono stock action.1 next left leftIn) second.2.2.1
  refine ⟨last.1,extends_trans stock action.1 _ next last.2.1,last.2.2.1,?_⟩
  intro point
  change pairRead (add action.1 left action.2).1 point (add action.1 left action.2).2=_
  rw [last.2.2.2 point,second.2.2.2 point,first.2.2.2 point,
    pairRead_preserves stock action.1 next left leftIn point,
    pairRead_preserves stock difference.1 first.2.1 control controlIn point]
  rfl

def native (address : Nat) (point : Nat → Bool) (read : Nat → EffectGate.Pair) : Node → Option EffectGate.Pair
  | .add _ _ => none
  | .constant value => some (truth value,false)
  | .input i => if i=address then some (false,true) else some (point i,false)
  | .mul a b | .band a b => some (EffectGate.multiply (read a) (read b))
  | .bxor a b => some (EffectGate.add (read a) (read b))
  | .bnot a => some (EffectGate.invert (read a))
  | .neg a => some (read a)
  | .phase _ => some (true,false)
  | .select c a b => some (EffectGate.select (read c) (read a) (read b))

theorem operation_spec (address : Nat) (stock : Stock) (good : Good stock) (mapping : Nat → Refs)
    (bounded : ∀ i, PairWithin stock (mapping i)) (node : Node) (output : Stock × Refs)
    (generated : operation address stock mapping node=some output) :
    Good output.1 ∧ Extends stock output.1 ∧ PairWithin output.1 output.2 ∧
      ∀ point, native address point (fun i => pairRead stock point (mapping i)) node=some (pairRead output.1 point output.2) := by
  have zero : 0 < stock.code.size := by have size := good.2.2.1; omega
  have one : 1 < stock.code.size := by have size := good.2.2.1; omega
  cases node with
  | add a b => cases generated
  | constant value =>
      simp only [operation,Option.some.injEq] at generated
      subst output
      refine ⟨good,extends_refl stock,?_,?_⟩
      · change (if truth value then 1 else 0) < stock.code.size ∧ 0 < stock.code.size
        split <;> exact ⟨by omega,zero⟩
      · intro point
        cases valueRead : truth value <;> simp [native,pairRead,valueRead,read_zero stock good point,read_one stock good point]
  | input i =>
      simp only [operation] at generated
      split at generated
      · rename_i same
        cases Option.some.inj generated
        exact ⟨good,extends_refl stock,⟨zero,one⟩,fun point => by simp [native,same,pairRead,read_zero stock good point,read_one stock good point]⟩
      · rename_i different
        cases Option.some.inj generated
        have within : Reduce.Within stock.code.size (.input i) := by simp [Reduce.Within,Node.refs]
        have next := put_good stock good (.input i) within
        refine ⟨next,put_extends stock good _ within,⟨put_bound stock good _ within,zero.trans_le (put_extends stock good _ within).1⟩,?_⟩
        intro point
        simp only [native,if_neg different,pairRead,read_zero _ next point,put_read stock good _ within point,Node.run,truth_bit]
  | mul a b =>
      cases Option.some.inj generated
      have actual := multiply_spec stock good (mapping a) (mapping b) (bounded a) (bounded b)
      exact ⟨actual.1,actual.2.1,actual.2.2.1,fun point => congrArg some (actual.2.2.2 point).symm⟩
  | band a b =>
      cases Option.some.inj generated
      have actual := multiply_spec stock good (mapping a) (mapping b) (bounded a) (bounded b)
      exact ⟨actual.1,actual.2.1,actual.2.2.1,fun point => congrArg some (actual.2.2.2 point).symm⟩
  | bxor a b =>
      cases Option.some.inj generated
      have actual := add_spec stock good (mapping a) (mapping b) (bounded a) (bounded b)
      exact ⟨actual.1,actual.2.1,actual.2.2.1,fun point => congrArg some (actual.2.2.2 point).symm⟩
  | bnot a =>
      cases Option.some.inj generated
      have actual := invert_spec stock good (mapping a) (bounded a)
      exact ⟨actual.1,actual.2.1,actual.2.2.1,fun point => congrArg some (actual.2.2.2 point).symm⟩
  | neg a =>
      cases Option.some.inj generated
      exact ⟨good,extends_refl stock,bounded a,fun _ => rfl⟩
  | phase a =>
      cases Option.some.inj generated
      exact ⟨good,extends_refl stock,⟨one,zero⟩,fun point => by simp [native,pairRead,read_zero stock good point,read_one stock good point]⟩
  | select c a b =>
      cases Option.some.inj generated
      have actual := select_spec stock good (mapping c) (mapping a) (mapping b) (bounded c) (bounded a) (bounded b)
      exact ⟨actual.1,actual.2.1,actual.2.2.1,fun point => congrArg some (actual.2.2.2 point).symm⟩

def Models (value : EffectGate.Pair) (before after : Int) : Prop :=
  value.1=truth before ∧ (value.1^^value.2)=truth after

theorem truth_mul (a b : Int) : truth (a*b)=(truth a && truth b) := by
  by_cases az : a=0 <;> by_cases bz : b=0 <;> simp [truth_eq_decide,az,bz]

theorem truth_neg (a : Int) : truth (-a)=truth a := by simp [truth_eq_decide]

theorem truth_sign (a : Int) : truth (sign a)=true := by
  unfold sign
  split <;> rfl

theorem truth_select (control left right : Int) :
    (if truth control then truth right else truth left)=truth (if control=0 then left else right) := by
  by_cases zero : control=0 <;> simp [truth_eq_decide,zero]

theorem native_models (address : Nat) (point : Nat → Bool) (before after : Array Int)
    (values : Nat → EffectGate.Pair) (model : ∀ i, Models (values i) (before.getD i 0) (after.getD i 0))
    (node : Node) (value : EffectGate.Pair) (generated : native address point values node=some value) :
    Models value (node.run (Function.update point address false) before) (node.run (Function.update point address true) after) := by
  cases node with
  | add a b => cases generated
  | constant z =>
      cases Option.some.inj generated
      simp [Models,Node.run]
  | input i =>
      simp only [native] at generated
      split at generated
      · rename_i same
        cases Option.some.inj generated
        simp [Models,Node.run,same,truth_bit]
      · rename_i different
        cases Option.some.inj generated
        simp [Models,Node.run,Function.update_of_ne different,truth_bit]
  | mul a b =>
      cases Option.some.inj generated
      refine ⟨?_,?_⟩
      · change ((values a).1 && (values b).1)=truth (before.getD a 0*before.getD b 0)
        rw [(model a).1,(model b).1,truth_mul]
      · change ((EffectGate.multiply (values a) (values b)).1^^(EffectGate.multiply (values a) (values b)).2)=truth (after.getD a 0*after.getD b 0)
        rw [EffectGate.multiply_update,(model a).2,(model b).2,truth_mul]
  | band a b =>
      cases Option.some.inj generated
      refine ⟨?_,?_⟩
      · change ((values a).1 && (values b).1)=truth (bit (truth (before.getD a 0) && truth (before.getD b 0)))
        rw [(model a).1,(model b).1,truth_bit]
      · rw [EffectGate.multiply_update]
        simp only [Node.run,truth_bit,(model a).2,(model b).2]
  | bxor a b =>
      cases Option.some.inj generated
      refine ⟨?_,?_⟩
      · change ((values a).1^^(values b).1)=truth (bit (truth (before.getD a 0)^^truth (before.getD b 0)))
        rw [(model a).1,(model b).1,truth_bit]
      · rw [EffectGate.add_update]
        simp only [Node.run,truth_bit,(model a).2,(model b).2]
  | bnot a =>
      cases Option.some.inj generated
      refine ⟨?_,?_⟩
      · change (!(values a).1)=truth (bit (!truth (before.getD a 0)))
        rw [(model a).1,truth_bit]
      · rw [EffectGate.invert_update]
        simp only [Node.run,truth_bit,(model a).2]
  | neg a =>
      cases Option.some.inj generated
      simpa only [Models,Node.run,truth_neg] using model a
  | phase a =>
      cases Option.some.inj generated
      simp [Models,Node.run,truth_sign]
  | select c a b =>
      cases Option.some.inj generated
      refine ⟨?_,?_⟩
      · rw [EffectGate.select_base,(model c).1,(model a).1,(model b).1]
        exact truth_select _ _ _
      · rw [EffectGate.select_update,(model c).2,(model a).2,(model b).2]
        exact truth_select _ _ _

structure View (frame : Frame) (point : Nat → Bool) (before after : Array Int) : Prop where
  good : Good frame.stock
  beforeSize : frame.mapping.size=before.size
  afterSize : frame.mapping.size=after.size
  bounded : ∀ i, PairWithin frame.stock (frame.mapping.getD i (0,0))
  models : ∀ i, Models (pairRead frame.stock point (frame.mapping.getD i (0,0))) (before.getD i 0) (after.getD i 0)

theorem pairGet_push (values : Array Refs) (value : Refs) (i : Nat) :
    (values.push value).getD i (0,0)=if i=values.size then value else values.getD i (0,0) := by
  simp only [Array.getD_eq_getD_getElem?]
  by_cases same : i=values.size <;> simp [Array.getElem?_push,same]

theorem emit_view (address : Nat) (frame : Frame) (point : Nat → Bool) (before after : Array Int)
    (view : View frame point before after) (node : Node) (output : Frame) (generated : emit address frame node=some output) :
    View output point (before.push (node.run (Function.update point address false) before))
      (after.push (node.run (Function.update point address true) after)) := by
  cases result : operation address frame.stock (fun i => frame.mapping.getD i (0,0)) node with
  | none => simp only [emit,result,Option.map_none,reduceCtorEq] at generated
  | some resultValue =>
      simp only [emit,result,Option.map_some,Option.some.injEq] at generated
      subst output
      have actual := operation_spec address frame.stock view.good _ view.bounded node resultValue result
      refine ⟨actual.1,by simpa using congrArg Nat.succ view.beforeSize,
        by simpa using congrArg Nat.succ view.afterSize,?_,?_⟩
      · intro i
        change PairWithin resultValue.1 ((frame.mapping.push resultValue.2).getD i (0,0))
        rw [pairGet_push]
        split
        · exact actual.2.2.1
        · exact pairWithin_mono frame.stock resultValue.1 actual.2.1 _ (view.bounded i)
      · intro i
        change Models (pairRead resultValue.1 point ((frame.mapping.push resultValue.2).getD i (0,0))) _ _
        rw [pairGet_push,getD_push_any,getD_push_any,← view.beforeSize,← view.afterSize]
        by_cases same : i=frame.mapping.size
        · simp only [if_pos same]
          exact native_models address point before after _ view.models node _ (actual.2.2.2 point)
        · simp only [if_neg same]
          rw [pairRead_preserves frame.stock resultValue.1 actual.2.1 _ (view.bounded i) point]
          exact view.models i

theorem initial_view (point : Nat → Bool) : View initial point #[] #[] := by
  refine ⟨initial_good,rfl,rfl,?_,?_⟩
  · intro i
    change 0 < initial.stock.code.size ∧ 0 < initial.stock.code.size
    constructor <;> decide
  · intro i
    change Models (pairRead initial.stock point (0,0)) 0 0
    simp only [Models,pairRead,read_zero initial.stock initial_good point,Bool.false_xor]
    exact ⟨rfl,rfl⟩

theorem build_view (address : Nat) (code : List Node) (frame : Frame) (point : Nat → Bool) (before after : Array Int)
    (view : View frame point before after) (output : Frame) (generated : build address code frame=some output) :
    View output point (runCode (Function.update point address false) before code)
      (runCode (Function.update point address true) after code) := by
  induction code generalizing frame before after with
  | nil =>
      have equal : frame=output := Option.some.inj generated
      subst output
      exact view
  | cons node rest ih =>
      cases emitted : emit address frame node with
      | none => simp [build,emitted] at generated
      | some next =>
          have nextView := emit_view address frame point before after view node next emitted
          simp only [build,emitted] at generated
          exact ih next _ _ nextView generated

theorem program_truth (program : Program) (point : Nat → Bool) :
    truth (program.eval point)=truth ((run point program.code).getD program.weight.val 0) := by
  simp only [Program.eval,truth_mul,truth_sign,Bool.and_true]

theorem generate_spec (source : Program) (address : Nat) (stock : Stock) (value : Refs)
    (generated : generate source address=some (stock,value)) :
    Good stock ∧ PairWithin stock value ∧ ∀ point,
      (pairRead stock point value).1=truth (source.eval (Function.update point address false)) ∧
      ((pairRead stock point value).1^^(pairRead stock point value).2)=truth (source.eval (Function.update point address true)) := by
  cases built : build address source.code.toList initial with
  | none => simp [generate,built] at generated
  | some frame =>
      simp only [generate,built] at generated
      change some (frame.stock,frame.mapping.getD source.weight.val (0,0))=some (stock,value) at generated
      have sameStock : frame.stock=stock := congrArg Prod.fst (Option.some.inj generated)
      have sameValue : frame.mapping.getD source.weight.val (0,0)=value := congrArg Prod.snd (Option.some.inj generated)
      subst stock
      subst value
      have view := build_view address source.code.toList initial (fun _ => false) #[] #[] (initial_view _) frame built
      refine ⟨view.good,?_,?_⟩
      · exact view.bounded source.weight.val
      · intro point
        have actual := build_view address source.code.toList initial point #[] #[] (initial_view point) frame built
        rw [program_truth,program_truth]
        exact actual.models source.weight.val

theorem existentialRoot_spec (stock : Stock) (good : Good stock) (value : Refs) (inside : PairWithin stock value) :
    Good (existentialRoot stock value).1 ∧ Extends stock (existentialRoot stock value).1 ∧
      (existentialRoot stock value).2 < (existentialRoot stock value).1.code.size ∧
      ∀ point, read (existentialRoot stock value).1 point (existentialRoot stock value).2=
        (read stock point value.1 || (read stock point value.1^^read stock point value.2)) := by
  let complement := notGate stock value.1
  let newPart := andGate complement.1 complement.2 value.2
  have first := notGate_spec stock good value.1 inside.1
  have second := andGate_spec complement.1 first.1 complement.2 value.2 first.2.2.1 (inside.2.trans_le first.2.1.1)
  have continued : Extends stock newPart.1 := extends_trans stock complement.1 newPart.1 first.2.1 second.2.1
  have last := xorGate_spec newPart.1 second.1 value.1 newPart.2 (inside.1.trans_le continued.1) second.2.2.1
  refine ⟨last.1,extends_trans stock newPart.1 _ continued last.2.1,last.2.2.1,?_⟩
  intro point
  change read (xorGate newPart.1 value.1 newPart.2).1 point (xorGate newPart.1 value.1 newPart.2).2=_
  rw [last.2.2.2 point,second.2.2.2 point,first.2.2.2 point,
    continued.2 point value.1 inside.1,first.2.1.2 point value.2 inside.2]
  exact EffectGate.existential_read (pairRead stock point value)

theorem program_read (stock : Stock) (good : Good stock) (root : Nat) (inside : root < stock.code.size) (point : Nat → Bool) :
    truth ((program stock root).eval point)=read stock point root := by
  have valid : 0 < stock.code.size ∧ root < stock.code.size := ⟨by have size := good.2.2.1; omega,inside⟩
  rw [program,dif_pos valid,program_truth]
  rfl

theorem eliminate_read (source : Program) (address : Nat) (point : Nat → Bool) :
    truth ((eliminate source address).eval point)=
      (truth (source.eval (Function.update point address false)) || truth (source.eval (Function.update point address true))) := by
  cases generated : generate source address with
  | none => simp only [eliminate,generated,Affine.Boolean.eval_existential,truth_bit]
  | some output =>
      rcases output with ⟨stock,refs⟩
      have paired := generate_spec source address stock refs generated
      have reader := existentialRoot_spec stock paired.1 refs paired.2.1
      simp only [eliminate,generated,Cone.eval_pruneCone]
      rw [program_read _ reader.1 _ reader.2.2.1 point,reader.2.2.2 point]
      have original := paired.2.2 point
      dsimp only [pairRead] at original
      rw [original.2,original.1]

theorem eliminate_original (source : Program) (address : Nat) (point : Nat → Bool) :
    truth ((eliminate source address).eval point)=truth ((Affine.Boolean.existential source address).eval point) := by
  rw [eliminate_read,Affine.Boolean.eval_existential,truth_bit]

theorem eliminate_correct (source : Program) (address : Nat) :
    (∃ point, truth ((eliminate source address).eval point)=true) ↔ ∃ point, truth (source.eval point)=true := by
  constructor
  · rintro ⟨point,accepted⟩
    rw [eliminate_read,Bool.or_eq_true] at accepted
    rcases accepted with left | right
    · exact ⟨Function.update point address false,left⟩
    · exact ⟨Function.update point address true,right⟩
  · rintro ⟨point,accepted⟩
    refine ⟨point,?_⟩
    rw [eliminate_read,Bool.or_eq_true]
    have same : Function.update point address (point address)=point := Function.update_eq_self address point
    cases value : point address with
    | false =>
        left
        rw [value] at same
        simpa only [same] using accepted
    | true =>
        right
        rw [value] at same
        simpa only [same] using accepted

theorem xorGate_size (stock : Stock) (a b : Nat) : (xorGate stock a b).1.code.size ≤ stock.code.size+1 := by
  simp only [xorGate]
  split
  · exact Nat.le_succ _
  · split
    · exact Nat.le_succ _
    · split
      · exact Nat.le_succ _
      · exact put_size _ _

theorem notGate_size (stock : Stock) (a : Nat) : (notGate stock a).1.code.size ≤ stock.code.size+1 := by
  simp only [notGate]
  split
  · exact Nat.le_succ _
  · split
    · exact Nat.le_succ _
    · split
      · exact Nat.le_succ _
      · exact put_size _ _

theorem andGate_size (stock : Stock) (a b : Nat) : (andGate stock a b).1.code.size ≤ stock.code.size+1 := by
  simp only [andGate]
  split
  · exact Nat.le_succ _
  · split
    · exact Nat.le_succ _
    · split
      · exact Nat.le_succ _
      · split
        · exact Nat.le_succ _
        · exact put_size _ _

theorem add_size (stock : Stock) (left right : Refs) : (add stock left right).1.code.size ≤ stock.code.size+2 := by
  have first := xorGate_size stock left.1 right.1
  have second := xorGate_size (xorGate stock left.1 right.1).1 left.2 right.2
  simp only [add]
  omega

theorem invert_size (stock : Stock) (value : Refs) : (invert stock value).1.code.size ≤ stock.code.size+1 := notGate_size stock value.1

theorem multiply_size (stock : Stock) (left right : Refs) : (multiply stock left right).1.code.size ≤ stock.code.size+6 := by
  let base := andGate stock left.1 right.1
  let first := andGate base.1 left.1 right.2
  let second := andGate first.1 left.2 right.1
  let mixed := andGate second.1 left.2 right.2
  let cross := xorGate mixed.1 first.2 second.2
  have a := andGate_size stock left.1 right.1
  have b := andGate_size base.1 left.1 right.2
  have c := andGate_size first.1 left.2 right.1
  have d := andGate_size second.1 left.2 right.2
  have e := xorGate_size mixed.1 first.2 second.2
  have f := xorGate_size cross.1 cross.2 mixed.2
  change (xorGate cross.1 cross.2 mixed.2).1.code.size ≤ _
  dsimp only [base,first,second,mixed,cross] at *
  omega

theorem select_size (stock : Stock) (control left right : Refs) : (select stock control left right).1.code.size ≤ stock.code.size+10 := by
  have first := add_size stock left right
  have second := multiply_size (add stock left right).1 control (add stock left right).2
  have last := add_size (multiply (add stock left right).1 control (add stock left right).2).1 left
    (multiply (add stock left right).1 control (add stock left right).2).2
  simp only [select]
  omega

theorem operation_size (address : Nat) (stock : Stock) (mapping : Nat → Refs) (node : Node) (output : Stock × Refs)
    (generated : operation address stock mapping node=some output) : output.1.code.size ≤ stock.code.size+10 := by
  cases node with
  | add a b => cases generated
  | constant z => cases Option.some.inj generated; exact Nat.le_add_right _ _
  | input i =>
      simp only [operation] at generated
      split at generated
      · cases Option.some.inj generated; exact Nat.le_add_right _ _
      · cases Option.some.inj generated
        change (put stock (.input i)).1.code.size ≤ stock.code.size+10
        have size := put_size stock (.input i)
        omega
  | mul a b => cases Option.some.inj generated; have size := multiply_size stock (mapping a) (mapping b); omega
  | band a b => cases Option.some.inj generated; have size := multiply_size stock (mapping a) (mapping b); omega
  | bxor a b => cases Option.some.inj generated; have size := add_size stock (mapping a) (mapping b); omega
  | bnot a => cases Option.some.inj generated; have size := invert_size stock (mapping a); omega
  | neg a => cases Option.some.inj generated; exact Nat.le_add_right _ _
  | phase a => cases Option.some.inj generated; exact Nat.le_add_right _ _
  | select c a b => cases Option.some.inj generated; exact select_size stock (mapping c) (mapping a) (mapping b)

theorem emit_size (address : Nat) (frame : Frame) (node : Node) (output : Frame) (generated : emit address frame node=some output) :
    output.stock.code.size ≤ frame.stock.code.size+10 := by
  cases result : operation address frame.stock (fun i => frame.mapping.getD i (0,0)) node with
  | none => simp only [emit,result,Option.map_none,reduceCtorEq] at generated
  | some value =>
      simp only [emit,result,Option.map_some,Option.some.injEq] at generated
      subst output
      exact operation_size address frame.stock _ node value result

theorem build_size (address : Nat) (code : List Node) (frame output : Frame) (generated : build address code frame=some output) :
    output.stock.code.size ≤ frame.stock.code.size+10*code.length := by
  induction code generalizing frame with
  | nil =>
      cases Option.some.inj generated
      omega
  | cons node rest ih =>
      cases first : emit address frame node with
      | none => simp [build,first] at generated
      | some next =>
          simp only [build,first] at generated
          have source := emit_size address frame node next first
          have tail := ih next generated
          simp only [List.length_cons]
          omega

theorem generate_size (source : Program) (address : Nat) (stock : Stock) (value : Refs)
    (generated : generate source address=some (stock,value)) : stock.code.size ≤ 2+10*source.code.size := by
  cases built : build address source.code.toList initial with
  | none => simp [generate,built] at generated
  | some frame =>
      simp only [generate,built] at generated
      change some (frame.stock,frame.mapping.getD source.weight.val (0,0))=some (stock,value) at generated
      have same : frame.stock=stock := congrArg Prod.fst (Option.some.inj generated)
      have count := build_size address source.code.toList initial frame built
      rw [same] at count
      simpa only [show initial.stock.code.size=2 from rfl,Array.length_toList] using count

theorem existentialRoot_size (stock : Stock) (value : Refs) : (existentialRoot stock value).1.code.size ≤ stock.code.size+3 := by
  let complement := notGate stock value.1
  let newPart := andGate complement.1 complement.2 value.2
  have first := notGate_size stock value.1
  have second := andGate_size complement.1 complement.2 value.2
  have last := xorGate_size newPart.1 value.1 newPart.2
  change (xorGate newPart.1 value.1 newPart.2).1.code.size ≤ _
  dsimp only [complement,newPart] at *
  omega

theorem program_size (stock : Stock) (good : Good stock) (root : Nat) (inside : root < stock.code.size) :
    (program stock root).code.size=stock.code.size := by
  have valid : 0 < stock.code.size ∧ root < stock.code.size := ⟨by have size := good.2.2.1; omega,inside⟩
  simp only [program,dif_pos valid]

theorem eliminate_size (source : Program) (address : Nat) : (eliminate source address).code.size ≤ 10*source.code.size+9 := by
  cases generated : generate source address with
  | none =>
      simp only [eliminate,generated,Affine.Boolean.existential_size]
      omega
  | some output =>
      rcases output with ⟨stock,refs⟩
      have paired := generate_spec source address stock refs generated
      have reader := existentialRoot_spec stock paired.1 refs paired.2.1
      have first := generate_size source address stock refs generated
      have last := existentialRoot_size stock refs
      have pruned := Cone.pruneCone_size (program (existentialRoot stock refs).1 (existentialRoot stock refs).2)
      rw [program_size _ reader.1 _ reader.2.2.1] at pruned
      simp only [eliminate,generated]
      omega

end SaturationMonoid.ComplexityProjection.SATSource.EffectDAG
