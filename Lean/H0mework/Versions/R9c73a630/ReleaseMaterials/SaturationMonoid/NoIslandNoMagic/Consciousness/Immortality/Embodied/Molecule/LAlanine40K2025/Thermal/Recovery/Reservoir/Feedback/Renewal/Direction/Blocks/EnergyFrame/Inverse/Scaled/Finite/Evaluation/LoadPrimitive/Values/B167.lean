import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B111
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B112

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v2673_pa : Scalar.QComplex := ((999999804120791441565884493961 : Int)/10^30,(-625906046262698987784293443 : Int)/10^30)
theorem v2673_pa_checked : Scalar.distance (sourceCoefficient 33 34 1 0) v2673_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2673_pb : Scalar.QComplex := ((-270064389208984697452043 : Int)/10^30,(-431477436464381418626288218 : Int)/10^30)
theorem v2673_pb_checked : Scalar.distance (sourceCoefficient 33 34 1 1) v2673_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2673_pg : Scalar.QComplex := ((-93086411661252329037076 : Int)/10^30,(58263359296257149702 : Int)/10^30)
theorem v2673_pg_checked : Scalar.distance (sourceCoefficient 33 34 1 2) v2673_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2673_mb : Scalar.QComplex := ((-642409883298080549941971 : Int)/10^30,(-431477042752207691143112362 : Int)/10^30)
theorem v2673_mb_checked : Scalar.distance (sourceCoefficient 33 34 3 1) v2673_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2673_mg : Scalar.QComplex := ((-93086326722272019997443 : Int)/10^30,(138592718409456549019 : Int)/10^30)
theorem v2673_mg_checked : Scalar.distance (sourceCoefficient 33 34 3 2) v2673_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2673_upper : Scalar.QComplex := ((999997234481497335875852538057 : Int)/10^30,(-2351814056688083433419021300 : Int)/10^30)
theorem v2673_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 33 34 5) 1) 14) v2673_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2673 : Material (33 : Basis) (34 : Basis) where
  plus := ![v2673_pa,v2673_pb,v2673_pg]
  minus := ![(Primitive.Addresses.material2673 1).one,v2673_mb,v2673_mg]
  upper := v2673_upper
  lower := (Primitive.Addresses.material2673 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2673_pa_checked.trans (by decide +kernel)
    · exact v2673_pb_checked.trans (by decide +kernel)
    · exact v2673_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 33 34 Primitive.Addresses.material2673
    · exact v2673_mb_checked.trans (by decide +kernel)
    · exact v2673_mg_checked.trans (by decide +kernel)
  upper_error := v2673_upper_checked
  lower_error := reuse_lower_error 33 34 Primitive.Addresses.material2673

def v2674_pa : Scalar.QComplex := ((999999770653907343383151611923 : Int)/10^30,(-677268139449659539289563406 : Int)/10^30)
theorem v2674_pa_checked : Scalar.distance (sourceCoefficient 33 35 1 0) v2674_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2674_pb : Scalar.QComplex := ((-292225977640363158897142 : Int)/10^30,(-431477421715033719691542306 : Int)/10^30)
theorem v2674_pb_checked : Scalar.distance (sourceCoefficient 33 35 1 1) v2674_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2674_pg : Scalar.QComplex := ((-93086408512592879678295 : Int)/10^30,(63044473160378312178 : Int)/10^30)
theorem v2674_pg_checked : Scalar.distance (sourceCoefficient 33 35 1 2) v2674_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2674_mb : Scalar.QComplex := ((-664571450749664025538729 : Int)/10^30,(-431477008878412788675941196 : Int)/10^30)
theorem v2674_mb_checked : Scalar.distance (sourceCoefficient 33 35 3 1) v2674_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2674_mg : Scalar.QComplex := ((-93086319447727811666802 : Int)/10^30,(143373827776199217745 : Int)/10^30)
theorem v2674_mg_checked : Scalar.distance (sourceCoefficient 33 35 3 2) v2674_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2674_upper : Scalar.QComplex := ((999997112368349774687424757852 : Int)/10^30,(-2403176015616433736781939244 : Int)/10^30)
theorem v2674_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 33 35 5) 1) 14) v2674_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2674 : Material (33 : Basis) (35 : Basis) where
  plus := ![v2674_pa,v2674_pb,v2674_pg]
  minus := ![(Primitive.Addresses.material2674 1).one,v2674_mb,v2674_mg]
  upper := v2674_upper
  lower := (Primitive.Addresses.material2674 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2674_pa_checked.trans (by decide +kernel)
    · exact v2674_pb_checked.trans (by decide +kernel)
    · exact v2674_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 33 35 Primitive.Addresses.material2674
    · exact v2674_mb_checked.trans (by decide +kernel)
    · exact v2674_mg_checked.trans (by decide +kernel)
  upper_error := v2674_upper_checked
  lower_error := reuse_lower_error 33 35 Primitive.Addresses.material2674

def v2675_pa : Scalar.QComplex := ((999999759589135221356695488168 : Int)/10^30,(-693413059986544171383480777 : Int)/10^30)
theorem v2675_pa_checked : Scalar.distance (sourceCoefficient 33 36 1 0) v2675_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2675_pb : Scalar.QComplex := ((-299192147803346754433287 : Int)/10^30,(-431477416765282229069814281 : Int)/10^30)
theorem v2675_pb_checked : Scalar.distance (sourceCoefficient 33 36 1 1) v2675_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2675_pg : Scalar.QComplex := ((-93086407463676162083054 : Int)/10^30,(64547346160425281248 : Int)/10^30)
theorem v2675_pg_checked : Scalar.distance (sourceCoefficient 33 36 1 2) v2675_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2675_mb : Scalar.QComplex := ((-671537614047411491816941 : Int)/10^30,(-431476997917172035075456639 : Int)/10^30)
theorem v2675_mb_checked : Scalar.distance (sourceCoefficient 33 36 3 1) v2675_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2675_mg : Scalar.QComplex := ((-93086317101899772477925 : Int)/10^30,(144876699311489998379 : Int)/10^30)
theorem v2675_mg_checked : Scalar.distance (sourceCoefficient 33 36 3 2) v2675_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2675_upper : Scalar.QComplex := ((999997073438925941426253295973 : Int)/10^30,(-2419320893010562850443496738 : Int)/10^30)
theorem v2675_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 33 36 5) 1) 14) v2675_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2675 : Material (33 : Basis) (36 : Basis) where
  plus := ![v2675_pa,v2675_pb,v2675_pg]
  minus := ![(Primitive.Addresses.material2675 1).one,v2675_mb,v2675_mg]
  upper := v2675_upper
  lower := (Primitive.Addresses.material2675 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2675_pa_checked.trans (by decide +kernel)
    · exact v2675_pb_checked.trans (by decide +kernel)
    · exact v2675_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 33 36 Primitive.Addresses.material2675
    · exact v2675_mb_checked.trans (by decide +kernel)
    · exact v2675_mg_checked.trans (by decide +kernel)
  upper_error := v2675_upper_checked
  lower_error := reuse_lower_error 33 36 Primitive.Addresses.material2675

def v2676_pa : Scalar.QComplex := ((999999754784942175916338025951 : Int)/10^30,(-700307115141451879479615891 : Int)/10^30)
theorem v2676_pa_checked : Scalar.distance (sourceCoefficient 33 37 1 0) v2676_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2676_pb : Scalar.QComplex := ((-302166777567261508577003 : Int)/10^30,(-431477414605996661414646664 : Int)/10^30)
theorem v2676_pb_checked : Scalar.distance (sourceCoefficient 33 37 1 1) v2676_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2676_pg : Scalar.QComplex := ((-93086407007152765792503 : Int)/10^30,(65189089135408446840 : Int)/10^30)
theorem v2676_pg_checked : Scalar.distance (sourceCoefficient 33 37 1 2) v2676_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2676_mb : Scalar.QComplex := ((-674512240840369443284496 : Int)/10^30,(-431476993190915757513836528 : Int)/10^30)
theorem v2676_mb_checked : Scalar.distance (sourceCoefficient 33 37 3 1) v2676_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2676_mg : Scalar.QComplex := ((-93086316091581261792089 : Int)/10^30,(145518441653563795334 : Int)/10^30)
theorem v2676_mg_checked : Scalar.distance (sourceCoefficient 33 37 3 2) v2676_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2676_upper : Scalar.QComplex := ((999997056736226277694503312545 : Int)/10^30,(-2426214929605983874469218845 : Int)/10^30)
theorem v2676_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 33 37 5) 1) 14) v2676_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2676 : Material (33 : Basis) (37 : Basis) where
  plus := ![v2676_pa,v2676_pb,v2676_pg]
  minus := ![(Primitive.Addresses.material2676 1).one,v2676_mb,v2676_mg]
  upper := v2676_upper
  lower := (Primitive.Addresses.material2676 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2676_pa_checked.trans (by decide +kernel)
    · exact v2676_pb_checked.trans (by decide +kernel)
    · exact v2676_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 33 37 Primitive.Addresses.material2676
    · exact v2676_mb_checked.trans (by decide +kernel)
    · exact v2676_mg_checked.trans (by decide +kernel)
  upper_error := v2676_upper_checked
  lower_error := reuse_lower_error 33 37 Primitive.Addresses.material2676

def v2677_pa : Scalar.QComplex := ((999999738195606268500255467643 : Int)/10^30,(-723608125245604820210006071 : Int)/10^30)
theorem v2677_pa_checked : Scalar.distance (sourceCoefficient 33 38 1 0) v2677_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2677_pb : Scalar.QComplex := ((-312220639382186003644071 : Int)/10^30,(-431477407105507374910727518 : Int)/10^30)
theorem v2677_pb_checked : Scalar.distance (sourceCoefficient 33 38 1 1) v2677_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2677_pg : Scalar.QComplex := ((-93086405425958570566870 : Int)/10^30,(67358096950775912550 : Int)/10^30)
theorem v2677_pg_checked : Scalar.distance (sourceCoefficient 33 38 1 2) v2677_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2677_mb : Scalar.QComplex := ((-684566092439197255715757 : Int)/10^30,(-431476977014399326632108085 : Int)/10^30)
theorem v2677_mb_checked : Scalar.distance (sourceCoefficient 33 38 3 1) v2677_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2677_mg : Scalar.QComplex := ((-93086312638631599140834 : Int)/10^30,(147687447296811146691 : Int)/10^30)
theorem v2677_mg_checked : Scalar.distance (sourceCoefficient 33 38 3 2) v2677_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2677_upper : Scalar.QComplex := ((999996999931485489501708816312 : Int)/10^30,(-2449515876374330590580617332 : Int)/10^30)
theorem v2677_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 33 38 5) 1) 14) v2677_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2677 : Material (33 : Basis) (38 : Basis) where
  plus := ![v2677_pa,v2677_pb,v2677_pg]
  minus := ![(Primitive.Addresses.material2677 1).one,v2677_mb,v2677_mg]
  upper := v2677_upper
  lower := (Primitive.Addresses.material2677 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2677_pa_checked.trans (by decide +kernel)
    · exact v2677_pb_checked.trans (by decide +kernel)
    · exact v2677_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 33 38 Primitive.Addresses.material2677
    · exact v2677_mb_checked.trans (by decide +kernel)
    · exact v2677_mg_checked.trans (by decide +kernel)
  upper_error := v2677_upper_checked
  lower_error := reuse_lower_error 33 38 Primitive.Addresses.material2677

def v2678_pa : Scalar.QComplex := ((999999728322950418663062077164 : Int)/10^30,(-737125515332534535529463617 : Int)/10^30)
theorem v2678_pa_checked : Scalar.distance (sourceCoefficient 33 39 1 0) v2678_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2678_pb : Scalar.QComplex := ((-318053089161819557795299 : Int)/10^30,(-431477402611159846248855116 : Int)/10^30)
theorem v2678_pb_checked : Scalar.distance (sourceCoefficient 33 39 1 1) v2678_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2678_pg : Scalar.QComplex := ((-93086404481650922348750 : Int)/10^30,(68616382515486043217 : Int)/10^30)
theorem v2678_pg_checked : Scalar.distance (sourceCoefficient 33 39 1 2) v2678_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2678_mb : Scalar.QComplex := ((-690398536168723701449734 : Int)/10^30,(-431476967486911995384259366 : Int)/10^30)
theorem v2678_mb_checked : Scalar.distance (sourceCoefficient 33 39 3 1) v2678_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2678_mg : Scalar.QComplex := ((-93086310608480531264870 : Int)/10^30,(148945731578109084750 : Int)/10^30)
theorem v2678_mg_checked : Scalar.distance (sourceCoefficient 33 39 3 2) v2678_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2678_upper : Scalar.QComplex := ((999996966729055341834441209249 : Int)/10^30,(-2463033229289387279122592789 : Int)/10^30)
theorem v2678_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 33 39 5) 1) 14) v2678_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2678 : Material (33 : Basis) (39 : Basis) where
  plus := ![v2678_pa,v2678_pb,v2678_pg]
  minus := ![(Primitive.Addresses.material2678 1).one,v2678_mb,v2678_mg]
  upper := v2678_upper
  lower := (Primitive.Addresses.material2678 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2678_pa_checked.trans (by decide +kernel)
    · exact v2678_pb_checked.trans (by decide +kernel)
    · exact v2678_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 33 39 Primitive.Addresses.material2678
    · exact v2678_mb_checked.trans (by decide +kernel)
    · exact v2678_mg_checked.trans (by decide +kernel)
  upper_error := v2678_upper_checked
  lower_error := reuse_lower_error 33 39 Primitive.Addresses.material2678

def v2679_pa : Scalar.QComplex := ((999999711305582883513858871036 : Int)/10^30,(-759861007611593271725940744 : Int)/10^30)
theorem v2679_pa_checked : Scalar.distance (sourceCoefficient 33 40 1 0) v2679_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2679_pb : Scalar.QComplex := ((-327862942637822182441150 : Int)/10^30,(-431477394814828801905553728 : Int)/10^30)
theorem v2679_pb_checked : Scalar.distance (sourceCoefficient 33 40 1 1) v2679_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2679_pg : Scalar.QComplex := ((-93086402848622490606261 : Int)/10^30,(70732748283642508740 : Int)/10^30)
theorem v2679_pg_checked : Scalar.distance (sourceCoefficient 33 40 1 2) v2679_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2679_mb : Scalar.QComplex := ((-700208379264186986975154 : Int)/10^30,(-431476951225122123580502759 : Int)/10^30)
theorem v2679_mb_checked : Scalar.distance (sourceCoefficient 33 40 3 1) v2679_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2679_mg : Scalar.QComplex := ((-93086307149124367230313 : Int)/10^30,(151062095149015864371 : Int)/10^30)
theorem v2679_mg_checked : Scalar.distance (sourceCoefficient 33 40 3 2) v2679_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2679_upper : Scalar.QComplex := ((999996910472316026147619908845 : Int)/10^30,(-2485768658336168402046252641 : Int)/10^30)
theorem v2679_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 33 40 5) 1) 14) v2679_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2679 : Material (33 : Basis) (40 : Basis) where
  plus := ![v2679_pa,v2679_pb,v2679_pg]
  minus := ![(Primitive.Addresses.material2679 1).one,v2679_mb,v2679_mg]
  upper := v2679_upper
  lower := (Primitive.Addresses.material2679 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2679_pa_checked.trans (by decide +kernel)
    · exact v2679_pb_checked.trans (by decide +kernel)
    · exact v2679_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 33 40 Primitive.Addresses.material2679
    · exact v2679_mb_checked.trans (by decide +kernel)
    · exact v2679_mg_checked.trans (by decide +kernel)
  upper_error := v2679_upper_checked
  lower_error := reuse_lower_error 33 40 Primitive.Addresses.material2679

def v2680_pa : Scalar.QComplex := ((999999700194867320981555281351 : Int)/10^30,(-774344997707687983714462706 : Int)/10^30)
theorem v2680_pa_checked : Scalar.distance (sourceCoefficient 33 41 1 0) v2680_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2680_pb : Scalar.QComplex := ((-334112458501366415941647 : Int)/10^30,(-431477389692988616669830765 : Int)/10^30)
theorem v2680_pb_checked : Scalar.distance (sourceCoefficient 33 41 1 1) v2680_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2680_pg : Scalar.QComplex := ((-93086401779004316011317 : Int)/10^30,(72081011182437140919 : Int)/10^30)
theorem v2680_pg_checked : Scalar.distance (sourceCoefficient 33 41 1 2) v2680_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2680_mb : Scalar.QComplex := ((-706457888380833446753706 : Int)/10^30,(-431476940710233122947207073 : Int)/10^30)
theorem v2680_mb_checked : Scalar.distance (sourceCoefficient 33 41 3 1) v2680_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2680_mg : Scalar.QComplex := ((-93086304916016432750130 : Int)/10^30,(152410356622758289810 : Int)/10^30)
theorem v2680_mg_checked : Scalar.distance (sourceCoefficient 33 41 3 2) v2680_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2680_upper : Scalar.QComplex := ((999996874363564083178807680524 : Int)/10^30,(-2500252607683974170207206429 : Int)/10^30)
theorem v2680_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 33 41 5) 1) 14) v2680_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2680 : Material (33 : Basis) (41 : Basis) where
  plus := ![v2680_pa,v2680_pb,v2680_pg]
  minus := ![(Primitive.Addresses.material2680 1).one,v2680_mb,v2680_mg]
  upper := v2680_upper
  lower := (Primitive.Addresses.material2680 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2680_pa_checked.trans (by decide +kernel)
    · exact v2680_pb_checked.trans (by decide +kernel)
    · exact v2680_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 33 41 Primitive.Addresses.material2680
    · exact v2680_mb_checked.trans (by decide +kernel)
    · exact v2680_mg_checked.trans (by decide +kernel)
  upper_error := v2680_upper_checked
  lower_error := reuse_lower_error 33 41 Primitive.Addresses.material2680

def v2681_pa : Scalar.QComplex := ((999999691079437613912038346400 : Int)/10^30,(-786028644096550757736135451 : Int)/10^30)
theorem v2681_pa_checked : Scalar.distance (sourceCoefficient 33 42 1 0) v2681_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2681_pb : Scalar.QComplex := ((-339153689033579573972444 : Int)/10^30,(-431477385473463424939993564 : Int)/10^30)
theorem v2681_pb_checked : Scalar.distance (sourceCoefficient 33 42 1 1) v2681_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2681_pg : Scalar.QComplex := ((-93086400899585323498647 : Int)/10^30,(73168600086214082170 : Int)/10^30)
theorem v2681_pg_checked : Scalar.distance (sourceCoefficient 33 42 1 2) v2681_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2681_mb : Scalar.QComplex := ((-711499113394705881921603 : Int)/10^30,(-431476932140354601634216061 : Int)/10^30)
theorem v2681_mb_checked : Scalar.distance (sourceCoefficient 33 42 3 1) v2681_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2681_mg : Scalar.QComplex := ((-93086303098057526911728 : Int)/10^30,(153497944362677193939 : Int)/10^30)
theorem v2681_mg_checked : Scalar.distance (sourceCoefficient 33 42 3 2) v2681_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2681_upper : Scalar.QComplex := ((999996845083234217414580155878 : Int)/10^30,(-2511936220939013376453791911 : Int)/10^30)
theorem v2681_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 33 42 5) 1) 14) v2681_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2681 : Material (33 : Basis) (42 : Basis) where
  plus := ![v2681_pa,v2681_pb,v2681_pg]
  minus := ![(Primitive.Addresses.material2681 1).one,v2681_mb,v2681_mg]
  upper := v2681_upper
  lower := (Primitive.Addresses.material2681 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2681_pa_checked.trans (by decide +kernel)
    · exact v2681_pb_checked.trans (by decide +kernel)
    · exact v2681_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 33 42 Primitive.Addresses.material2681
    · exact v2681_mb_checked.trans (by decide +kernel)
    · exact v2681_mg_checked.trans (by decide +kernel)
  upper_error := v2681_upper_checked
  lower_error := reuse_lower_error 33 42 Primitive.Addresses.material2681

def v2682_pa : Scalar.QComplex := ((999999678793671577364458809548 : Int)/10^30,(-801506427717061832192097022 : Int)/10^30)
theorem v2682_pa_checked : Scalar.distance (sourceCoefficient 33 43 1 0) v2682_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2682_pb : Scalar.QComplex := ((-345832004377800041489736 : Int)/10^30,(-431477379762764776649295419 : Int)/10^30)
theorem v2682_pb_checked : Scalar.distance (sourceCoefficient 33 43 1 1) v2682_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2682_pg : Scalar.QComplex := ((-93086399711756721756532 : Int)/10^30,(74609371667015003359 : Int)/10^30)
theorem v2682_pg_checked : Scalar.distance (sourceCoefficient 33 43 1 2) v2682_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2682_mb : Scalar.QComplex := ((-718177421324208599541024 : Int)/10^30,(-431476920666572717792972431 : Int)/10^30)
theorem v2682_mb_checked : Scalar.distance (sourceCoefficient 33 43 3 1) v2682_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2682_mg : Scalar.QComplex := ((-93086300666908383164463 : Int)/10^30,(154938714381970423593 : Int)/10^30)
theorem v2682_mg_checked : Scalar.distance (sourceCoefficient 33 43 3 2) v2682_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2682_upper : Scalar.QComplex := ((999996806084236083631773403410 : Int)/10^30,(-2527413960303066273247796901 : Int)/10^30)
theorem v2682_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 33 43 5) 1) 14) v2682_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2682 : Material (33 : Basis) (43 : Basis) where
  plus := ![v2682_pa,v2682_pb,v2682_pg]
  minus := ![(Primitive.Addresses.material2682 1).one,v2682_mb,v2682_mg]
  upper := v2682_upper
  lower := (Primitive.Addresses.material2682 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2682_pa_checked.trans (by decide +kernel)
    · exact v2682_pb_checked.trans (by decide +kernel)
    · exact v2682_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 33 43 Primitive.Addresses.material2682
    · exact v2682_mb_checked.trans (by decide +kernel)
    · exact v2682_mg_checked.trans (by decide +kernel)
  upper_error := v2682_upper_checked
  lower_error := reuse_lower_error 33 43 Primitive.Addresses.material2682

def v2683_pa : Scalar.QComplex := ((999999674083081657756040649114 : Int)/10^30,(-807362205247836862722247039 : Int)/10^30)
theorem v2683_pa_checked : Scalar.distance (sourceCoefficient 33 44 1 0) v2683_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2683_pb : Scalar.QComplex := ((-348358640602437071103019 : Int)/10^30,(-431477377566276400654370919 : Int)/10^30)
theorem v2683_pb_checked : Scalar.distance (sourceCoefficient 33 44 1 1) v2683_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2683_pg : Scalar.QComplex := ((-93086399255576871863389 : Int)/10^30,(75154465075674800092 : Int)/10^30)
theorem v2683_pg_checked : Scalar.distance (sourceCoefficient 33 44 1 2) v2683_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2683_mb : Scalar.QComplex := ((-720704054712592947422517 : Int)/10^30,(-431476916289711893260569429 : Int)/10^30)
theorem v2683_mb_checked : Scalar.distance (sourceCoefficient 33 44 3 1) v2683_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2683_mg : Scalar.QComplex := ((-93086299740337641550306 : Int)/10^30,(155483807194004367402 : Int)/10^30)
theorem v2683_mg_checked : Scalar.distance (sourceCoefficient 33 44 3 2) v2683_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2683_upper : Scalar.QComplex := ((999996791267112393763828396134 : Int)/10^30,(-2533269720982297679772561207 : Int)/10^30)
theorem v2683_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 33 44 5) 1) 14) v2683_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2683 : Material (33 : Basis) (44 : Basis) where
  plus := ![v2683_pa,v2683_pb,v2683_pg]
  minus := ![(Primitive.Addresses.material2683 1).one,v2683_mb,v2683_mg]
  upper := v2683_upper
  lower := (Primitive.Addresses.material2683 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2683_pa_checked.trans (by decide +kernel)
    · exact v2683_pb_checked.trans (by decide +kernel)
    · exact v2683_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 33 44 Primitive.Addresses.material2683
    · exact v2683_mb_checked.trans (by decide +kernel)
    · exact v2683_mg_checked.trans (by decide +kernel)
  upper_error := v2683_upper_checked
  lower_error := reuse_lower_error 33 44 Primitive.Addresses.material2683

def v2684_pa : Scalar.QComplex := ((999999671726730693885384303718 : Int)/10^30,(-810275527736639649814497023 : Int)/10^30)
theorem v2684_pa_checked : Scalar.distance (sourceCoefficient 33 45 1 0) v2684_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2684_pb : Scalar.QComplex := ((-349615673692008434743042 : Int)/10^30,(-431477376466147283385452026 : Int)/10^30)
theorem v2684_pb_checked : Scalar.distance (sourceCoefficient 33 45 1 1) v2684_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2684_pg : Scalar.QComplex := ((-93086399027234470931499 : Int)/10^30,(75425655857122468444 : Int)/10^30)
theorem v2684_pg_checked : Scalar.distance (sourceCoefficient 33 45 1 2) v2684_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2684_mb : Scalar.QComplex := ((-721961086384751562337935 : Int)/10^30,(-431476914104820243988631461 : Int)/10^30)
theorem v2684_mb_checked : Scalar.distance (sourceCoefficient 33 45 3 1) v2684_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2684_mg : Scalar.QComplex := ((-93086299277969895230783 : Int)/10^30,(155754997677426105946 : Int)/10^30)
theorem v2684_mg_checked : Scalar.distance (sourceCoefficient 33 45 3 2) v2684_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2684_upper : Scalar.QComplex := ((999996783882634618279154237773 : Int)/10^30,(-2536183035065200845541279421 : Int)/10^30)
theorem v2684_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 33 45 5) 1) 14) v2684_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2684 : Material (33 : Basis) (45 : Basis) where
  plus := ![v2684_pa,v2684_pb,v2684_pg]
  minus := ![(Primitive.Addresses.material2684 1).one,v2684_mb,v2684_mg]
  upper := v2684_upper
  lower := (Primitive.Addresses.material2684 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2684_pa_checked.trans (by decide +kernel)
    · exact v2684_pb_checked.trans (by decide +kernel)
    · exact v2684_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 33 45 Primitive.Addresses.material2684
    · exact v2684_mb_checked.trans (by decide +kernel)
    · exact v2684_mg_checked.trans (by decide +kernel)
  upper_error := v2684_upper_checked
  lower_error := reuse_lower_error 33 45 Primitive.Addresses.material2684

def v2685_pa : Scalar.QComplex := ((999999658333290685423961911649 : Int)/10^30,(-826639765492207507754864617 : Int)/10^30)
theorem v2685_pa_checked : Scalar.distance (sourceCoefficient 33 46 1 0) v2685_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2685_pb : Scalar.QComplex := ((-356676473978442443970672 : Int)/10^30,(-431477370195938842590601160 : Int)/10^30)
theorem v2685_pb_checked : Scalar.distance (sourceCoefficient 33 46 1 1) v2685_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2685_pg : Scalar.QComplex := ((-93086397727497184106182 : Int)/10^30,(76948944278865207130 : Int)/10^30)
theorem v2685_pg_checked : Scalar.distance (sourceCoefficient 33 46 1 2) v2685_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2685_mb : Scalar.QComplex := ((-729021878631219445710708 : Int)/10^30,(-431476901741461497326335438 : Int)/10^30)
theorem v2685_mb_checked : Scalar.distance (sourceCoefficient 33 46 3 1) v2685_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2685_mg : Scalar.QComplex := ((-93086296663703790756802 : Int)/10^30,(157278284410364206961 : Int)/10^30)
theorem v2685_mg_checked : Scalar.distance (sourceCoefficient 33 46 3 2) v2685_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2685_upper : Scalar.QComplex := ((999996742246024743715698551256 : Int)/10^30,(-2552547225332296433744538804 : Int)/10^30)
theorem v2685_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 33 46 5) 1) 14) v2685_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2685 : Material (33 : Basis) (46 : Basis) where
  plus := ![v2685_pa,v2685_pb,v2685_pg]
  minus := ![(Primitive.Addresses.material2685 1).one,v2685_mb,v2685_mg]
  upper := v2685_upper
  lower := (Primitive.Addresses.material2685 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2685_pa_checked.trans (by decide +kernel)
    · exact v2685_pb_checked.trans (by decide +kernel)
    · exact v2685_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 33 46 Primitive.Addresses.material2685
    · exact v2685_mb_checked.trans (by decide +kernel)
    · exact v2685_mg_checked.trans (by decide +kernel)
  upper_error := v2685_upper_checked
  lower_error := reuse_lower_error 33 46 Primitive.Addresses.material2685

def v2686_pa : Scalar.QComplex := ((999999655070193900981351156336 : Int)/10^30,(-830577806843805670789088161 : Int)/10^30)
theorem v2686_pa_checked : Scalar.distance (sourceCoefficient 33 47 1 0) v2686_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2686_pb : Scalar.QComplex := ((-358375650182141326302972 : Int)/10^30,(-431477368664019837620574371 : Int)/10^30)
theorem v2686_pb_checked : Scalar.distance (sourceCoefficient 33 47 1 1) v2686_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2686_pg : Scalar.QComplex := ((-93086397410375007822574 : Int)/10^30,(77315522476528361916 : Int)/10^30)
theorem v2686_pg_checked : Scalar.distance (sourceCoefficient 33 47 1 2) v2686_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2686_mb : Scalar.QComplex := ((-730721052880260264998745 : Int)/10^30,(-431476898743230527022990551 : Int)/10^30)
theorem v2686_mb_checked : Scalar.distance (sourceCoefficient 33 47 3 1) v2686_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2686_mg : Scalar.QComplex := ((-93086296030241258038111 : Int)/10^30,(157644862197871389826 : Int)/10^30)
theorem v2686_mg_checked : Scalar.distance (sourceCoefficient 33 47 3 2) v2686_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2686_upper : Scalar.QComplex := ((999996732186230702734692310882 : Int)/10^30,(-2556485255186835574285883475 : Int)/10^30)
theorem v2686_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 33 47 5) 1) 14) v2686_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2686 : Material (33 : Basis) (47 : Basis) where
  plus := ![v2686_pa,v2686_pb,v2686_pg]
  minus := ![(Primitive.Addresses.material2686 1).one,v2686_mb,v2686_mg]
  upper := v2686_upper
  lower := (Primitive.Addresses.material2686 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2686_pa_checked.trans (by decide +kernel)
    · exact v2686_pb_checked.trans (by decide +kernel)
    · exact v2686_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 33 47 Primitive.Addresses.material2686
    · exact v2686_mb_checked.trans (by decide +kernel)
    · exact v2686_mg_checked.trans (by decide +kernel)
  upper_error := v2686_upper_checked
  lower_error := reuse_lower_error 33 47 Primitive.Addresses.material2686

def v2687_pa : Scalar.QComplex := ((999999631910755145023172755608 : Int)/10^30,(-858008364889446445880208753 : Int)/10^30)
theorem v2687_pa_checked : Scalar.distance (sourceCoefficient 33 48 1 0) v2687_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2687_pb : Scalar.QComplex := ((-370211318477161248220822 : Int)/10^30,(-431477357745874597176254038 : Int)/10^30)
theorem v2687_pb_checked : Scalar.distance (sourceCoefficient 33 48 1 1) v2687_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2687_pg : Scalar.QComplex := ((-93086395154726657079661 : Int)/10^30,(79868935099055917221 : Int)/10^30)
theorem v2687_pg_checked : Scalar.distance (sourceCoefficient 33 48 1 2) v2687_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2687_mb : Scalar.QComplex := ((-742556707346452356421885 : Int)/10^30,(-431476877611440672012872672 : Int)/10^30)
theorem v2687_mb_checked : Scalar.distance (sourceCoefficient 33 48 3 1) v2687_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2687_mg : Scalar.QComplex := ((-93086291571113655370352 : Int)/10^30,(160198271923123792981 : Int)/10^30)
theorem v2687_mg_checked : Scalar.distance (sourceCoefficient 33 48 3 2) v2687_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2687_upper : Scalar.QComplex := ((999996661684171734051019723152 : Int)/10^30,(-2583915732406792075179650620 : Int)/10^30)
theorem v2687_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 33 48 5) 1) 14) v2687_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2687 : Material (33 : Basis) (48 : Basis) where
  plus := ![v2687_pa,v2687_pb,v2687_pg]
  minus := ![(Primitive.Addresses.material2687 1).one,v2687_mb,v2687_mg]
  upper := v2687_upper
  lower := (Primitive.Addresses.material2687 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2687_pa_checked.trans (by decide +kernel)
    · exact v2687_pb_checked.trans (by decide +kernel)
    · exact v2687_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 33 48 Primitive.Addresses.material2687
    · exact v2687_mb_checked.trans (by decide +kernel)
    · exact v2687_mg_checked.trans (by decide +kernel)
  upper_error := v2687_upper_checked
  lower_error := reuse_lower_error 33 48 Primitive.Addresses.material2687

def v2688_pa : Scalar.QComplex := ((999999612758792172932838838182 : Int)/10^30,(-880046740632780983063128840 : Int)/10^30)
theorem v2688_pa_checked : Scalar.distance (sourceCoefficient 33 49 1 0) v2688_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2688_pb : Scalar.QComplex := ((-379720381388811268921282 : Int)/10^30,(-431477348660369428229041054 : Int)/10^30)
theorem v2688_pb_checked : Scalar.distance (sourceCoefficient 33 49 1 1) v2688_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2688_pg : Scalar.QComplex := ((-93086393283284870961823 : Int)/10^30,(81920408729174068605 : Int)/10^30)
theorem v2688_pg_checked : Scalar.distance (sourceCoefficient 33 49 1 2) v2688_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2688_mb : Scalar.QComplex := ((-752065758877061904632311 : Int)/10^30,(-431476860320045865555820134 : Int)/10^30)
theorem v2688_mb_checked : Scalar.distance (sourceCoefficient 33 49 3 1) v2688_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2688_mg : Scalar.QComplex := ((-93086287929343218226294 : Int)/10^30,(162249743174414580086 : Int)/10^30)
theorem v2688_mg_checked : Scalar.distance (sourceCoefficient 33 49 3 2) v2688_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2688_upper : Scalar.QComplex := ((999996604496000059394089192536 : Int)/10^30,(-2605954042272004114815213763 : Int)/10^30)
theorem v2688_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 33 49 5) 1) 14) v2688_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2688 : Material (33 : Basis) (49 : Basis) where
  plus := ![v2688_pa,v2688_pb,v2688_pg]
  minus := ![(Primitive.Addresses.material2688 1).one,v2688_mb,v2688_mg]
  upper := v2688_upper
  lower := (Primitive.Addresses.material2688 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2688_pa_checked.trans (by decide +kernel)
    · exact v2688_pb_checked.trans (by decide +kernel)
    · exact v2688_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 33 49 Primitive.Addresses.material2688
    · exact v2688_mb_checked.trans (by decide +kernel)
    · exact v2688_mg_checked.trans (by decide +kernel)
  upper_error := v2688_upper_checked
  lower_error := reuse_lower_error 33 49 Primitive.Addresses.material2688

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
