import H0mework.Versions.R26b91feb.ReleaseMaterials.Scratch.FlyCNS.C3SparseStep

/-! Original C7 no-equality/no-dry-friction, pyramidal sparse Newton
and NoSlip constraint operator. Present matrices/properties come from the
fixed source's position/velocity stages; no constraint solution is input. -/

set_option autoImplicit false

namespace FlyCNS.C3Constraint
open FlyCNS.C3Actuation FlyCNS.C3Sparse

def one : Float := Float.ofBits 0x3FF0000000000000
def two : Float := Float.ofBits 0x4000000000000000
def half : Float := Float.ofBits 0x3FE0000000000000

structure Material where
  iterations : Nat
  tolerance : Float
  searchIterations : Nat
  searchTolerance : Float
  noSlipIterations : Nat
  noSlipTolerance : Float
  meanInertia : Float

structure Frame where
  mass : Matrix
  jacobian : Matrix
  projection : Matrix
  factor : Array Float
  diagonalInverse : Array Float
  smoothForce : Array Float
  smoothAcceleration : Array Float
  warmstart : Array Float
  reference : Array Float
  diagonal : Array Float
  regularizer : Array Float
  contactWidth : Array Nat

structure Faces where
  force : Array Float
  state : Array Nat
  cost : Float

def faces (diagonal residual : Array Float) : Faces := Id.run do
  let mut force := diagonal.mapIdx fun i d => -d*residual[i]!
  let mut state := Array.replicate diagonal.size 0
  let mut cost := zero
  for i in [:diagonal.size] do
    if residual[i]! >= zero then force := force.set! i zero
    else
      cost := fused ((half*diagonal[i]!)*residual[i]!) residual[i]! cost
      state := state.set! i 1
  return ⟨force,state,cost⟩

def residual (j : Matrix) (a reference : Array Float) : Array Float :=
  (multiply j a).mapIdx fun i value => value-reference[i]!

def gauss (ma smooth a acceleration : Array Float) : Float := Id.run do
  let mut cost := zero
  for i in [:ma.size] do cost := fused (half*(ma[i]!-smooth[i]!)) (a[i]!-acceleration[i]!) cost
  return cost

structure Context where
  acceleration : Array Float
  ma : Array Float
  jar : Array Float
  force : Array Float
  state : Array Nat
  gaussCost : Float
  cost : Float
  gradient : Array Float
  direction : Array Float
  factor : Matrix
  updates : Nat := 0

def update (frame : Frame) (ctx : Context) : Context :=
  let current := faces frame.diagonal ctx.jar
  let force := multiply (transpose frame.jacobian) current.force
  let gc := gauss ctx.ma frame.smoothForce ctx.acceleration frame.smoothAcceleration
  {ctx with
    force := current.force
    state := current.state
    gaussCost := gc
    cost := current.cost+gc
    gradient := ctx.ma.mapIdx fun i v => (v-frame.smoothForce[i]!)-force[i]!}

def activeDiagonal (frame : Frame) (state : Array Nat) : Array Float :=
  frame.diagonal.mapIdx fun i value => if state[i]! == 1 then value else zero

def factor (frame : Frame) (state : Array Nat) : Matrix :=
  (cholesky (hessian frame.mass frame.jacobian (activeDiagonal frame state))).matrix

def incremental (frame : Frame) (ctx : Context) (oldState : Array Nat) : Context := Id.run do
  let mut l := ctx.factor
  let mut count := 0
  for i in [:ctx.state.size] do
    if (oldState[i]! == 1) != (ctx.state[i]! == 1) then
      let mut row := Array.replicate frame.mass.rows zero
      let scale := frame.diagonal[i]!.sqrt
      for k in [frame.jacobian.starts[i]!:frame.jacobian.starts[i]!+frame.jacobian.counts[i]!] do
        row := row.set! frame.jacobian.columns[k]! (frame.jacobian.values[k]!*scale)
      let changed := cholUpdate l row (ctx.state[i]! == 1)
      l := changed.matrix
      count := count+1
      if changed.rank < frame.mass.rows then return {ctx with factor:=factor frame ctx.state,updates:=ctx.state.size}
  return {ctx with factor:=l,updates:=count}

structure Quadratics where
  gauss : Array Float
  contacts : Array (Array Float)
  jar : Array Float
  jv : Array Float

def prepare (frame : Frame) (ctx : Context) (mv jv : Array Float) : Quadratics :=
  let g := #[ctx.gaussCost,dot ctx.direction ctx.ma-dot frame.smoothForce ctx.direction,half*dot ctx.direction mv]
  let q := frame.diagonal.mapIdx fun i d =>
    let dj := d*ctx.jar[i]!
    #[half*(ctx.jar[i]!*dj),jv[i]!*dj,half*((jv[i]!*d)*jv[i]!)]
  ⟨g,q,ctx.jar,jv⟩

structure Point where
  alpha : Float := zero
  cost : Float := zero
  derivative : Float := zero
  curvature : Float := zero
  deriving Inhabited

def evaluate (q : Quadratics) (alpha : Float) : Point := Id.run do
  let mut total := q.gauss
  for i in [:q.jar.size] do
    if fused alpha q.jv[i]! q.jar[i]! < zero then
      total := total.mapIdx fun j value => value+q.contacts[i]![j]!
  let cost := fused (alpha*alpha) total[2]! (alpha*total[1]!) + total[0]!
  let derivative := fused (two*alpha) total[2]! total[1]!
  let curvature := two*total[2]!
  return ⟨alpha,cost,derivative,if curvature <= zero then minimum else curvature⟩

def nextPoint (q : Quadratics) (p : Point) : Point := evaluate q (p.alpha-p.derivative/p.curvature)

def bracket (q : Quadratics) (p : Point) (candidates : Array Point) (next : Point) : Point × Point × Bool := Id.run do
  let mut result := p
  let mut changed := false
  for c in candidates do
    if (result.derivative < zero && c.derivative < zero && result.derivative < c.derivative) ||
      (result.derivative > zero && c.derivative > zero && result.derivative > c.derivative) then
      result := c
      changed := true
  return (result,if changed then nextPoint q result else next,changed)

structure Search where
  alpha : Float
  mv : Array Float
  jv : Array Float

def search (m : Material) (frame : Frame) (ctx : Context) (scale : Float) : Search := Id.run do
  let norm := (dot ctx.direction ctx.direction).sqrt
  let mv := symmetricMultiply frame.mass ctx.direction
  let jv := multiply frame.jacobian ctx.direction
  if norm < minimum then return ⟨zero,mv,jv⟩
  let threshold := ((m.tolerance*m.searchTolerance)*norm)/scale
  let q := prepare frame ctx mv jv
  let p0 := evaluate q zero
  let mut p1 := nextPoint q p0
  let mut evaluations := 2
  if p1.derivative.abs < threshold then return ⟨p1.alpha,mv,jv⟩
  let direction := if p1.derivative < zero then one else -one
  let mut p2 := p0
  for _ in [:m.searchIterations] do
    if p1.derivative*direction > -threshold || evaluations >= m.searchIterations then break
    p2 := p1
    p1 := nextPoint q p1
    evaluations := evaluations+1
    if p1.derivative.abs < threshold then return ⟨p1.alpha,mv,jv⟩
  if evaluations >= m.searchIterations then return ⟨p1.alpha,mv,jv⟩
  let mut p2next := p1
  let mut p1next := nextPoint q p1
  evaluations := evaluations+1
  for _ in [:m.searchIterations] do
    if evaluations >= m.searchIterations then break
    let midpoint := evaluate q (half*(p1.alpha+p2.alpha))
    evaluations := evaluations+1
    let candidates := #[p1next,p2next,midpoint]
    let mut best : Option Point := none
    for c in candidates do
      if c.derivative.abs < threshold then
        match best with
        | none => best := some c
        | some old => if c.cost < old.cost then best := some c
    match best with
    | some p => return ⟨p.alpha,mv,jv⟩
    | none => pure ()
    let b1 := bracket q p1 candidates p1next
    let b2 := bracket q p2 candidates p2next
    p1 := b1.1
    p1next := b1.2.1
    p2 := b2.1
    p2next := b2.2.1
    if b1.2.2 then evaluations := evaluations+1
    if b2.2.2 then evaluations := evaluations+1
    if !b1.2.2 && !b2.2.2 then return ⟨midpoint.alpha,mv,jv⟩
  if p1.cost <= p2.cost && p1.cost < p0.cost then return ⟨p1.alpha,mv,jv⟩
  if p2.cost <= p1.cost && p2.cost < p0.cost then return ⟨p2.alpha,mv,jv⟩
  return ⟨zero,mv,jv⟩

structure Newton where
  context : Context
  iterations : Nat
  initialAcceleration : Array Float
  initialResidual : Array Float
  initialState : Array Nat
  initialFactor : Matrix

def newton (m : Material) (frame : Frame) : Newton := Id.run do
  let smoothResidual := residual frame.jacobian frame.smoothAcceleration frame.reference
  let warmResidual := residual frame.jacobian frame.warmstart frame.reference
  let warmMa := symmetricMultiply frame.mass frame.warmstart
  let warm := faces frame.diagonal warmResidual
  let smooth := faces frame.diagonal smoothResidual
  -- This is the original global warmstart comparison before island Newton.
  let mut warmCost := warm.cost
  for i in [:frame.mass.rows] do
    warmCost := fused (half*(warmMa[i]!-frame.smoothForce[i]!)) (frame.warmstart[i]!-frame.smoothAcceleration[i]!) warmCost
  let initial := if warmCost > smooth.cost then frame.smoothAcceleration else frame.warmstart
  let jar := residual frame.jacobian initial frame.reference
  let ma := symmetricMultiply frame.mass initial
  let current := faces frame.diagonal jar
  let l := factor frame current.state
  let gc := gauss ma frame.smoothForce initial frame.smoothAcceleration
  let jointForce := multiply (transpose frame.jacobian) current.force
  let gradient := ma.mapIdx fun i value => (value-frame.smoothForce[i]!)-jointForce[i]!
  let mut ctx : Context := ⟨initial,ma,jar,current.force,current.state,gc,current.cost+gc,gradient,
    (cholSolve l gradient).map Neg.neg,l,current.state.size⟩
  let mut inertia := zero
  for i in [:frame.mass.rows] do inertia := inertia+frame.mass.values[frame.mass.starts[i]!+frame.mass.counts[i]!-1]!
  let scale := one/inertia
  let mut iterations := 0
  for _ in [:m.iterations] do
    let line := search m frame ctx scale
    if line.alpha == zero then break
    let old := ctx
    ctx := {ctx with
      acceleration := ctx.acceleration.mapIdx fun i a => fused ctx.direction[i]! line.alpha a
      ma := ctx.ma.mapIdx fun i a => fused line.mv[i]! line.alpha a
      jar := ctx.jar.mapIdx fun i a => fused line.jv[i]! line.alpha a}
    ctx := update frame ctx
    ctx := incremental frame ctx old.state
    let direction := (cholSolve ctx.factor ctx.gradient).map Neg.neg
    let improvement := scale*(old.cost-ctx.cost)
    let gradientNorm := scale*(dot ctx.gradient ctx.gradient).sqrt
    iterations := iterations+1
    ctx := {ctx with direction:=direction}
    if improvement < m.tolerance || gradientNorm < m.tolerance then break
  return ⟨ctx,iterations,initial,jar,current.state,l⟩

def entry (m : Matrix) (r c : Nat) : Float := Id.run do
  for i in [m.starts[r]!:m.starts[r]!+m.counts[r]!] do if m.columns[i]! == c then return m.values[i]!
  return zero

def noSlip (m : Material) (frame : Frame) (initial : Array Float) (b : Array Float) : Array Float × Nat := Id.run do
  let mut force := initial
  let scale := one/(m.meanInertia*(UInt64.ofNat frame.mass.rows).toFloat)
  let mut iterations := 0
  for iter in [:m.noSlipIterations] do
    let mut improvement := zero
    if iter == 0 then
      for i in [:force.size] do improvement := fused ((half*force[i]!)*force[i]!) frame.regularizer[i]! improvement
    for i in [:force.size] do
      let width := frame.contactWidth[i]!
      for pair in [:width/2] do
        let j := i+2*pair
        let old := #[force[j]!,force[j+1]!]
        let res := (List.range 2).toArray.map fun k =>
          let r := j+k
          let value := b[r]!+dotIndexed frame.projection.values force frame.projection.columns frame.projection.starts[r]! frame.projection.counts[r]!
          fused (-frame.regularizer[r]!) force[r]! value
        let a := #[max 1e-10 (entry frame.projection j j-frame.regularizer[j]!),entry frame.projection j (j+1),
          entry frame.projection (j+1) j,max 1e-10 (entry frame.projection (j+1) (j+1)-frame.regularizer[j+1]!)]
        let bc := #[res[0]!-dot #[a[0]!,a[1]!] old,res[1]!-dot #[a[2]!,a[3]!] old]
        let mid := half*(force[j]!+force[j+1]!)
        let k1 := ((a[0]!+a[3]!)-a[1]!)-a[2]!
        let k0 := fused mid (a[0]!-a[3]!) bc[0]! - bc[1]!
        let y := -k0/k1
        let proposed := if k1 < minimum then #[mid,mid]
          else if y < -mid then #[zero,two*mid]
          else if y > mid then #[two*mid,zero] else #[mid+y,mid-y]
        let delta := proposed.mapIdx fun k value => value-old[k]!
        let matvec := #[dot #[a[0]!,a[1]!] delta,dot #[a[2]!,a[3]!] delta]
        let change := fused half (dot delta matvec) (dot delta res)
        if change <= 1e-10 then
          force := (force.set! j proposed[0]!).set! (j+1) proposed[1]!
          improvement := improvement-change
    iterations := iterations+1
    if improvement*scale < m.noSlipTolerance then break
  return (force,iterations)

structure Result where
  acceleration : Array Float
  constraintForce : Array Float
  contactForce : Array Float
  contactState : Array Nat
  residual : Array Float
  newtonIterations : Nat
  noSlipIterations : Nat
  newton : Option Newton

def advance (m : Material) (frame : Frame) : Result := Id.run do
  if frame.diagonal.isEmpty then
    return ⟨frame.smoothAcceleration,Array.replicate frame.mass.rows zero,#[],#[],#[],0,0,none⟩
  let b := residual frame.jacobian frame.smoothAcceleration frame.reference
  let generated := newton m frame
  let dry := noSlip m frame generated.context.force b
  let force := transposeScatterMultiply frame.jacobian dry.1
  let acceleration := (solveLD frame.mass frame.factor frame.diagonalInverse force).mapIdx fun i a => a+frame.smoothAcceleration[i]!
  return ⟨acceleration,force,dry.1,dry.1.map fun f => if f <= zero then 0 else 1,b,generated.iterations,dry.2,some generated⟩

end FlyCNS.C3Constraint
