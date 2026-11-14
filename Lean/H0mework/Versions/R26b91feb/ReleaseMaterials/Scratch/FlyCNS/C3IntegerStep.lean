import Lean
import Init.Data.SInt.Basic
import Init.Data.Float.Model.Float

/-! Concrete C7 integer primitive. The only inputs are original material
words, the complete neural/plastic registers and present pending afferents.
No spike, plastic-after, localIndex current or target state is supplied. -/

set_option autoImplicit false

namespace FlyCNS.C3Integer

abbrev I := Int64
abbrev A := Array I
def Q : I := 1048576

structure Word where
  width : Nat
  bytes : ByteArray
  deriving Inhabited

def Word.bits (word : Word) (index : Nat) : UInt64 := Id.run do
  let mut value : UInt64 := 0
  for b in [:word.width] do
    value := value ||| (word.bytes.get! (index * word.width + b)).toUInt64 <<< UInt64.ofNat (8*b)
  return value

def Word.int (word : Word) (index : Nat) : I :=
  if word.width = 1 then (word.bits index).toUInt8.toInt8.toInt64
  else if word.width = 4 then (word.bits index).toUInt32.toInt32.toInt64
  else (word.bits index).toInt64

structure Material where
  constants : Std.HashMap String Word
  parameters : Std.HashMap String I
  plasticSlot : Std.HashMap Nat Nat

def Material.word (m : Material) (key : String) : Word := m.constants[key]?.getD ⟨8, ByteArray.empty⟩
def Material.i (m : Material) (key : String) (index : Nat) : I := (m.word key).int index
def Material.n (m : Material) (key : String) (index : Nat) : Nat := (m.i key index).toInt.toNat
def Material.p (m : Material) (key : String) : I := m.parameters[key]?.getD 0
def count (word : Word) : Nat := word.bytes.size / word.width
def getA (a : A) (index : Nat) : I := a[index]?.getD 0
def addAt (a : A) (index : Nat) (value : I) : A := a.set! index (getA a index + value)
def zeros (n : Nat) : A := Array.replicate n 0
def sign (x : I) : I := if x < 0 then -1 else if x > 0 then 1 else 0

/-- NumPy signed `//` rounds down; native signed division truncates. -/
def floorDiv (a b : I) : I :=
  let q := a / b
  if a % b != 0 && (a < 0) != (b < 0) then q - 1 else q

def ceilDiv (a b : I) : I := floorDiv (a + b - 1) b
def signedScale (v fraction : I) : I :=
  let magnitude := v.abs
  let scaled := floorDiv magnitude Q * fraction + floorDiv ((magnitude % Q) * fraction) Q
  if v < 0 then -scaled else scaled

def flux (v tau : I) : I := sign v * ceilDiv v.abs tau
def decay (v tau : I) : I := if tau > 0 then v - flux v tau else v
def clip (value low high : I) : I := min high (max low value)
def floatOfI (value : I) : Float :=
  if value < 0 then -((-value).toUInt64.toFloat) else value.toUInt64.toFloat

def addressed (seed : UInt64) (tick neuron : Nat) : Nat :=
  let a := seed ^^^ (UInt64.ofNat (tick + 1) * 0x9E3779B97F4A7C15)
  let b := a ^^^ (UInt64.ofNat (neuron + 1) * 0xBF58476D1CE4E5B9)
  let c := (b ^^^ (b >>> 30)) * 0xBF58476D1CE4E5B9
  let d := (c ^^^ (c >>> 27)) * 0x94D049BB133111EB
  ((d ^^^ (d >>> 31)) >>> 11).toNat

/-- Compare the exact dyadic addressed sample with the binary64 pending
probability using bits. No floating evaluator supplies a sensory decision. -/
def hits (top53 : Nat) (probability : UInt64) : Bool :=
  let e := ((probability >>> 52) &&& 2047).toNat
  let f := (probability &&& 0xFFFFFFFFFFFFF).toNat
  if probability >>> 63 != 0 then false
  else if e = 2047 then f == 0
  else
    let mantissa := if e = 0 then f else f + 2^52
    let exponent := max e 1
    if exponent ≥ 1022 then decide (top53 < mantissa * 2^(exponent - 1022))
    else decide (top53 * 2^(1022 - exponent) < mantissa)

structure Pending where
  sensory : Array Nat
  probability : Array UInt64
  auxiliary : Array Nat
  uv : A

structure State where
  neural : Array A
  installation : Word
  plastic : Array A
  rules : A
  plasticChanges : Nat

structure Events where
  fired : Array Nat
  inputCells : Array Nat
  inputUV : A
  gradedCells : Array Nat
  gradedFraction : A
  gradedDose : A
  terminalCells : Array Nat
  terminalGain : A

structure Next where
  state : State
  events : Events

def baseWeight (m : Material) (s : State) (pre edge : Nat) : I :=
  match m.plasticSlot[edge]? with
  | some site => m.i "plastic.base" site + getA (s.plastic[4]?.getD #[]) site
  | none => m.i "graph.sign" pre * m.i "graph.counts" edge * m.p "synapse_scale_uv"

def physicalWeight (m : Material) (s : State) (gain : A) (pre edge : Nat) : I :=
  let post := m.n "graph.indices" edge
  let weight := baseWeight m s pre edge
  if m.i "gamma.slot" pre ≥ 0 then
    if m.i "gamma.slot" post ≥ 0 then 0
    else if m.i "mbon.mask" post != 0 then floorDiv (weight * getA gain pre) Q else weight
  else weight

def deposit (m : Material) (target : A) (position : Nat) (value : I) : A := Id.run do
  let start := m.n "spatial.input_ptr" position
  let stop := m.n "spatial.input_ptr" (position+1)
  let contacts := Int64.ofNat (stop-start)
  let per := floorDiv value.abs contacts
  let remainder := (value.abs % contacts).toInt.toNat
  let mut result := target
  for contact in [start:stop] do
    let piece := per + if contact-start < remainder then 1 else 0
    let node := m.n "spatial.input_nodes" contact
    result := addAt result node (if value < 0 then -piece else piece)
  return result

def spread (m : Material) (impulse : A) : A := Id.run do
  let n := impulse.size
  let mut down := impulse
  for reverse in [:n] do
    let node := m.n "spatial.order" (n-reverse-1)
    let parent := m.i "spatial.parent" node
    if parent ≥ 0 then
      down := addAt down parent.toInt.toNat (signedScale (getA down node) (m.i "spatial.attenuation_q" node))
  let mut total := down
  for position in [:n] do
    let node := m.n "spatial.order" position
    let parent := m.i "spatial.parent" node
    if parent ≥ 0 then
      let attenuation := m.i "spatial.attenuation_q" node
      total := addAt total node (signedScale (getA total parent.toInt.toNat - signedScale (getA down node) attenuation) attenuation)
  return total

def nearestEvenBits (bits : UInt64) : I :=
  let e := ((bits >>> 52) &&& 2047).toNat
  let f := (bits &&& 0xFFFFFFFFFFFFF).toNat
  let mantissa := if e = 0 then f else f + 2^52
  let magnitude := if max e 1 ≥ 1075 then mantissa * 2^(max e 1 - 1075) else
    let divisor := 2^(1075-max e 1)
    let q := mantissa / divisor
    let r := mantissa % divisor
    q + if 2*r > divisor || (2*r == divisor && q % 2 == 1) then 1 else 0
  if bits >>> 63 == 0 then Int64.ofNat magnitude else -Int64.ofNat magnitude

/-- NumPy's pairwise binary64 summation order. Arithmetic has the pinned
Lean binary64 model, not an oracle for a localIndex mean or after voltage. -/
def pairwise (a : A) (start length fuel : Nat) : Float := Id.run do
  if length < 8 then
    let mut result := Float.ofBits 0x8000000000000000
    for index in [start:start+length] do
      result := result + floatOfI (getA a index)
    return result
  else if length ≤ 128 then
    let mut lanes := Array.ofFn fun i : Fin 8 => floatOfI (getA a (start+i.val))
    let chunks := length / 8
    for chunk in [1:chunks] do
      for lane in [:8] do
        lanes := lanes.set! lane (lanes[lane]! + floatOfI (getA a (start+8*chunk+lane)))
    let mut result := ((lanes[0]!+lanes[1]!)+(lanes[2]!+lanes[3]!)) +
      ((lanes[4]!+lanes[5]!)+(lanes[6]!+lanes[7]!))
    for index in [start+8*chunks:start+length] do
      result := result + floatOfI (getA a index)
    return result
  else
    match fuel with
    | 0 => return floatOfI 0
    | fuel+1 =>
      let left := (length/2/8)*8
      return pairwise a start left fuel + pairwise a (start+left) (length-left) fuel

def mean (a : A) (start stop : Nat) : I :=
  nearestEvenBits (pairwise a start (stop-start) (stop-start) / (UInt64.ofNat (stop-start)).toFloat).toBits

def plasticStep (m : Material) (s : State) (active : Array Bool) (gain : A) (tick : I) : Array A × Nat := Id.run do
  let old := s.plastic
  let rules := s.rules
  let rule := fun domain column => getA rules (domain*11+column)
  let mut modulation := zeros (old[1]!.size)
  for connection in [:count (m.word "plastic.dan_pre")] do
    if active[m.n "plastic.dan_pre" connection]?.getD false then
      modulation := addAt modulation (m.n "plastic.dan_domain" connection) (m.i "plastic.dan_contact_q" connection)
  let dopamine := (old[1]!).mapIdx fun domain value => decay value (rule domain 1)
  let mut newDA := dopamine
  for domain in [:dopamine.size] do
    newDA := newDA.set! domain (min Q (getA dopamine domain + min Q (getA modulation domain)))
  let mut eligibility := old[0]!
  let mut labile := old[2]!
  let mut stable := old[3]!
  let mut delta := old[4]!
  let mut last := old[5]!
  let mut changes := 0
  for edge in [:eligibility.size] do
    let domain := m.n "plastic.edge_domain" edge
    let pre := m.n "plastic.pre" edge
    let g := getA gain pre
    let spiked := active[pre]?.getD false
    let mut e := decay (getA eligibility edge) (rule domain 0)
    if spiked then e := min Q (e + floorDiv (rule domain 2 * g) Q)
    let mut l := decay (getA labile edge) (rule domain 6)
    let mut v := decay (getA stable edge) (rule domain 8)
    let received := min Q (getA modulation domain)
    if rule domain 3 > 0 then
      l := l - floorDiv (floorDiv (e * floorDiv (received * g) Q) Q) (rule domain 3)
    if spiked && rule domain 4 > 0 then
      l := l + floorDiv (floorDiv (getA dopamine domain * g) Q) (rule domain 4)
    if rule domain 5 > 0 && e == 0 && received > 0 then
      l := l - sign l * floorDiv (floorDiv (l.abs * received) Q) (rule domain 5)
    if rule domain 7 > 0 then
      let moved := sign l * floorDiv l.abs (rule domain 7)
      l := l - moved
      v := v + moved
    let total := Q + l + v
    l := l + clip total (rule domain 9) (rule domain 10) - total
    if l != getA labile edge || v != getA stable edge then last := last.set! edge tick
    let d := floorDiv (m.i "plastic.base" edge * (Q+l+v)) Q - m.i "plastic.base" edge
    if d != getA delta edge then changes := changes+1
    eligibility := eligibility.set! edge e
    labile := labile.set! edge l
    stable := stable.set! edge v
    delta := delta.set! edge d
  return (#[eligibility,newDA,labile,stable,delta,last,modulation], changes)

def step (m : Material) (s : State) (pending : Pending) : Next := Id.run do
  let nn := s.neural
  let n := nn[0]!.size
  let cursor := (getA nn[5]! 0).toInt.toNat
  let tick := getA nn[6]! 0
  let seed := (getA nn[7]! 0).toUInt64
  let apls := count (m.word "spatial.apl_neurons")
  let nodes := nn[14]!.size
  let mut voltage := nn[0]!
  let mut conductance := nn[1]!
  let mut refractory := nn[2]!
  let mut delayNodes := nn[3]!
  let mut delayCounts := nn[4]!
  let mut adaptation := nn[9]!
  let mut release := nn[10]!
  let mut daRise := nn[11]!
  let mut daDecay := nn[12]!
  let mut daFraction := nn[13]!
  let mut localV := nn[14]!
  let mut localG := nn[15]!
  let mut localR := nn[16]!
  let mut localD := nn[17]!
  let mut localF := nn[18]!
  let mut gammaRise := nn[19]!
  let mut gammaActivation := nn[20]!
  let mut delayed := Array.replicate n false
  for i in [: (getA delayCounts cursor).toInt.toNat] do
    delayed := delayed.set! (getA delayNodes (cursor*n+i)).toInt.toNat true
  let mut available := release
  let mut gain := Array.replicate n Q
  for cell in [:n] do
    available := available.set! cell (getA release cell + ceilDiv (Q-getA release cell) (m.p "recovery_tau_ticks"))
  for slot in [:gammaActivation.size] do
    gain := gain.set! (m.n "gamma.indices" slot) (floorDiv (Q*Q) (Q+getA gammaActivation slot))
  let mut fast := zeros nodes
  let mut slow := zeros nodes
  for edge in [:count (m.word "gamma.lateral")] do
    let pre := m.n "gamma.lateral_pre" edge
    if delayed[pre]! then
      let slot := m.n "gamma.lateral_slot" edge
      let dose := floorDiv (floorDiv (baseWeight m s pre (m.n "gamma.lateral" edge) * getA available pre) Q * getA gain pre) Q
      gammaRise := addAt gammaRise slot (floorDiv (dose*Q) (m.i "gamma.contacts" slot*m.p "synapse_scale_uv"))
  for position in [:count (m.word "spatial.input_edges")] do
    let pre := m.n "spatial.input_pre" position
    if delayed[pre]! then
      let value := signedScale (physicalWeight m s gain pre (m.n "spatial.input_edges" position)) (getA available pre)
      if m.i "dopamine.mask" pre != 0 then
        let apl := m.n "spatial.apl_neurons" (m.n "spatial.input_slots" position)
        slow := deposit m slow position (value*m.i "dopamine.sign" apl*Q*m.p "g_tau_steps")
      else fast := deposit m fast position value
  let localFraction := localV.map fun v => min Q (floorDiv (max 0 (v-m.p "rest_uv")*Q) (m.p "threshold_uv"-m.p "rest_uv"))
  let mut fTotal := zeros apls
  let mut dTotal := zeros apls
  let mut cTotal := zeros apls
  for position in [:count (m.word "spatial.output_edges")] do
    let slot := m.n "spatial.output_slots" position
    let cell := m.n "spatial.apl_neurons" slot
    let start := m.n "spatial.output_ptr" position
    let stop := m.n "spatial.output_ptr" (position+1)
    let mut doses : I := 0
    for contact in [start:stop] do
      let f := getA localFraction (m.n "spatial.output_nodes" contact)
      let d := floorDiv (signedScale (getA available cell) f) (m.p "refractory_steps"+1)
      fTotal := addAt fTotal slot f
      doses := doses+d
    dTotal := addAt dTotal slot doses
    cTotal := addAt cTotal slot (Int64.ofNat (stop-start))
    let edge := m.n "spatial.output_edges" position
    let value := signedScale (physicalWeight m s gain cell edge) (floorDiv doses (Int64.ofNat (stop-start)))
    let localIndex := m.i "spatial.output_local_input" position
    if localIndex ≥ 0 then fast := deposit m fast localIndex.toInt.toNat value
    else conductance := addAt conductance (m.n "spatial.output_targets" position) value
  let fractions := fTotal.mapIdx fun slot value => floorDiv value (max 1 (getA cTotal slot))
  let doses := dTotal.mapIdx fun slot value => floorDiv value (max 1 (getA cTotal slot))
  let releaseAfter := fractions.mapIdx fun slot value =>
    let cell := m.n "spatial.apl_neurons" slot
    let loss := floorDiv (signedScale (m.i "depletion" cell) value) (m.p "refractory_steps"+1)
    signedScale (getA available cell) (Q-loss)
  let mut inputCells : Array Nat := #[]
  let mut inputUV : A := #[]
  for index in [:pending.sensory.size] do
    let cell := pending.sensory[index]!
    if hits (addressed seed tick.toInt.toNat cell) pending.probability[index]! then
      inputCells := inputCells.push cell
      inputUV := inputUV.push (m.p "pulse_uv")
  inputCells := inputCells ++ pending.auxiliary
  inputUV := inputUV ++ pending.uv
  for input in [:inputCells.size] do
    let cell := inputCells[input]!
    let pulse := getA inputUV input
    voltage := addAt voltage cell pulse
    for slot in [:apls] do
      if cell == m.n "spatial.apl_neurons" slot then
        for node in [m.n "spatial.tree_offsets" slot:m.n "spatial.tree_offsets" (slot+1)] do
          localV := addAt localV node pulse
  release := available
  for pre in [:n] do
    adaptation := adaptation.set! pre (getA adaptation pre-ceilDiv (getA adaptation pre) (m.i "adaptation.tau" pre))
    if delayed[pre]! then
      for edge in [m.n "graph.indptr" pre:m.n "graph.indptr" (pre+1)] do
        let post := m.n "graph.indices" edge
        if m.i "apl.mask" post == 0 then
          let weight := physicalWeight m s gain pre edge
          let amount := floorDiv (weight.abs*getA release pre) Q
          let effective := if weight < 0 then -amount else amount
          if m.i "dopamine.mask" pre == 0 then conductance := addAt conductance post effective
          else daRise := addAt daRise post (effective*m.i "dopamine.sign" post*Q*m.p "g_tau_steps")
      release := release.set! pre (floorDiv (getA release pre*(Q-m.i "depletion" pre)) Q)
  let mut fired : Array Nat := #[]
  let mut active := Array.replicate n false
  for cell in [:n] do
    let flow := flux (getA daRise cell) (m.p "dopamine.rise_tau_ticks")
    daRise := daRise.set! cell (getA daRise cell-flow)
    daDecay := addAt daDecay cell flow
    let flow := flux (getA daDecay cell) (m.p "dopamine.decay_tau_ticks")
    daDecay := daDecay.set! cell (getA daDecay cell-flow)
    daFraction := addAt daFraction cell flow
    let current := sign (getA daFraction cell)*floorDiv (getA daFraction cell).abs Q
    daFraction := daFraction.set! cell (getA daFraction cell-current*Q)
    if getA refractory cell == 0 then
      let g := getA conductance cell
      voltage := addAt voltage cell (floorDiv (m.p "rest_uv"-getA voltage cell+g+current-getA adaptation cell) (m.p "tau_steps"))
      conductance := conductance.set! cell (sign g*floorDiv (g.abs*(m.p "g_tau_steps"-1)) (m.p "g_tau_steps"))
      if m.i "apl.mask" cell == 0 && getA voltage cell > m.p "threshold_uv" then
        fired := fired.push cell
        active := active.set! cell true
        voltage := voltage.set! cell (m.p "rest_uv")
        conductance := conductance.set! cell 0
        refractory := refractory.set! cell (m.p "refractory_steps")
        adaptation := addAt adaptation cell (m.i "adaptation.impulse" cell)
    else refractory := refractory.set! cell (getA refractory cell-1)
  for cell in [:n] do delayNodes := delayNodes.set! (cursor*n+cell) 0
  for index in [:fired.size] do delayNodes := delayNodes.set! (cursor*n+index) (Int64.ofNat fired[index]!)
  delayCounts := delayCounts.set! cursor (Int64.ofNat fired.size)
  fast := spread m fast
  slow := spread m slow
  for node in [:nodes] do
    localG := addAt localG node (getA fast node)
    localR := addAt localR node (getA slow node)
    let flow := flux (getA localR node) (m.p "dopamine.rise_tau_ticks")
    localR := localR.set! node (getA localR node-flow)
    localD := addAt localD node flow
    let flow := flux (getA localD node) (m.p "dopamine.decay_tau_ticks")
    localD := localD.set! node (getA localD node-flow)
    localF := addAt localF node flow
    let current := sign (getA localF node)*floorDiv (getA localF node).abs Q
    localF := localF.set! node (getA localF node-current*Q)
    let g := getA localG node
    localV := addAt localV node (floorDiv (m.p "rest_uv"-getA localV node+g+current) (m.p "tau_steps"))
    localG := localG.set! node (sign g*floorDiv (g.abs*(m.p "g_tau_steps"-1)) (m.p "g_tau_steps"))
  for slot in [:apls] do
    let cell := m.n "spatial.apl_neurons" slot
    release := release.set! cell (getA releaseAfter slot)
    let start := m.n "spatial.tree_offsets" slot
    let stop := m.n "spatial.tree_offsets" (slot+1)
    voltage := voltage.set! cell (mean localV start stop)
    conductance := conductance.set! cell (mean localG start stop)
    daRise := daRise.set! cell (mean localR start stop)
    daDecay := daDecay.set! cell (mean localD start stop)
    daFraction := daFraction.set! cell (mean localF start stop)
  let (plastic, changes) := plasticStep m s active gain tick
  for slot in [:gammaRise.size] do
    let incoming := ceilDiv (getA gammaRise slot) (m.p "gamma.rise_tau_ticks")
    gammaRise := gammaRise.set! slot (getA gammaRise slot-incoming)
    gammaActivation := gammaActivation.set! slot (min Q (getA gammaActivation slot-ceilDiv (getA gammaActivation slot) (m.p "gamma.decay_tau_ticks")+incoming))
  let after := nn.set! 0 voltage |>.set! 1 conductance |>.set! 2 refractory |>.set! 3 delayNodes |>.set! 4 delayCounts
    |>.set! 5 #[Int64.ofNat ((cursor+1)%delayCounts.size)] |>.set! 6 #[tick+1]
    |>.set! 9 adaptation |>.set! 10 release |>.set! 11 daRise |>.set! 12 daDecay |>.set! 13 daFraction
    |>.set! 14 localV |>.set! 15 localG |>.set! 16 localR |>.set! 17 localD |>.set! 18 localF
    |>.set! 19 gammaRise |>.set! 20 gammaActivation
  let mut gradedCells : Array Nat := #[]
  let mut gradedFraction : A := #[]
  let mut gradedDose : A := #[]
  for slot in [:apls] do
    if getA doses slot > 0 then
      gradedCells := gradedCells.push (m.n "spatial.apl_neurons" slot)
      gradedFraction := gradedFraction.push (getA fractions slot)
      gradedDose := gradedDose.push (getA doses slot)
  let mut terminalCells : Array Nat := #[]
  let mut terminalGain : A := #[]
  for cell in fired do
    if m.i "gamma.slot" cell ≥ 0 then
      terminalCells := terminalCells.push cell
      terminalGain := terminalGain.push (getA gain cell)
  return ⟨⟨after,s.installation,plastic,s.rules,s.plasticChanges+changes⟩,
    ⟨fired,inputCells,inputUV,gradedCells,gradedFraction,gradedDose,terminalCells,terminalGain⟩⟩

/-- The twelve source fields are split into seven plastic arrays, rules
and these four current afferent arrays. Their evolution after this primitive
belongs to the actual body/world operator, not to a hidden neural register. -/
structure Registers where
  state : State
  pending : Pending

def advance (m : Material) (registers : Registers) : Registers :=
  ⟨(step m registers.state registers.pending).state,registers.pending⟩

theorem advance_pending (m : Material) (registers : Registers) :
    (advance m registers).pending = registers.pending := by
  simp only [advance]

end FlyCNS.C3Integer
