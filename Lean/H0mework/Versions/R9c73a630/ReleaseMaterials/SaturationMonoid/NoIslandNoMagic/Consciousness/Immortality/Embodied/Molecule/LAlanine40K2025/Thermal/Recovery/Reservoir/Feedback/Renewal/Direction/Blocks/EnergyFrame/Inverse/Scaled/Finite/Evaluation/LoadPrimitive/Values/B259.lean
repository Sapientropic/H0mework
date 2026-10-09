import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B172
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B173

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v4145_pa : Scalar.QComplex := ((999998116105233179566471091465 : Int)/10^30,(-1941078562186851468705916897 : Int)/10^30)
theorem v4145_pa_checked : Scalar.distance (sourceCoefficient 62 85 1 0) v4145_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4145_pb : Scalar.QComplex := ((-837531727647406868354340 : Int)/10^30,(-431476688342893590928599096 : Int)/10^30)
theorem v4145_pb_checked : Scalar.distance (sourceCoefficient 62 85 1 1) v4145_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4145_pg : Scalar.QComplex := ((-93086252396176374704973 : Int)/10^30,(180688069357840684811 : Int)/10^30)
theorem v4145_pg_checked : Scalar.distance (sourceCoefficient 62 85 1 2) v4145_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4145_mb : Scalar.QComplex := ((-1209876364847328227384204 : Int)/10^30,(-431475804932243131081719185 : Int)/10^30)
theorem v4145_mb_checked : Scalar.distance (sourceCoefficient 62 85 3 1) v4145_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4145_mg : Scalar.QComplex := ((-93086061810244388444439 : Int)/10^30,(261017245448137926704 : Int)/10^30)
theorem v4145_mg_checked : Scalar.distance (sourceCoefficient 62 85 3 2) v4145_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4145_upper : Scalar.QComplex := ((999993276600002208309254626620 : Int)/10^30,(-3666981700455546476443026463 : Int)/10^30)
theorem v4145_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 62 85 5) 1) 14) v4145_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4145 : Material (62 : Basis) (85 : Basis) where
  plus := ![v4145_pa,v4145_pb,v4145_pg]
  minus := ![(Primitive.Addresses.material4145 1).one,v4145_mb,v4145_mg]
  upper := v4145_upper
  lower := (Primitive.Addresses.material4145 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4145_pa_checked.trans (by decide +kernel)
    · exact v4145_pb_checked.trans (by decide +kernel)
    · exact v4145_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 62 85 Primitive.Addresses.material4145
    · exact v4145_mb_checked.trans (by decide +kernel)
    · exact v4145_mg_checked.trans (by decide +kernel)
  upper_error := v4145_upper_checked
  lower_error := reuse_lower_error 62 85 Primitive.Addresses.material4145

def v4146_pa : Scalar.QComplex := ((999998087688937458361463348214 : Int)/10^30,(-1955663178604556422703047979 : Int)/10^30)
theorem v4146_pa_checked : Scalar.distance (sourceCoefficient 62 86 1 0) v4146_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4146_pb : Scalar.QComplex := ((-843824659312840464954975 : Int)/10^30,(-431476674965937115212008599 : Int)/10^30)
theorem v4146_pb_checked : Scalar.distance (sourceCoefficient 62 86 1 1) v4146_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4146_pg : Scalar.QComplex := ((-93086249630626543068630 : Int)/10^30,(182045698965012340346 : Int)/10^30)
theorem v4146_pg_checked : Scalar.distance (sourceCoefficient 62 86 1 2) v4146_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4146_mb : Scalar.QComplex := ((-1216169282625904800970312 : Int)/10^30,(-431475786124775032069238168 : Int)/10^30)
theorem v4146_mb_checked : Scalar.distance (sourceCoefficient 62 86 3 1) v4146_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4146_mg : Scalar.QComplex := ((-93086057873122380927236 : Int)/10^30,(262374872163257083790 : Int)/10^30)
theorem v4146_mg_checked : Scalar.distance (sourceCoefficient 62 86 3 2) v4146_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4146_upper : Scalar.QComplex := ((999993223012023978945837245634 : Int)/10^30,(-3681566246107229997071339198 : Int)/10^30)
theorem v4146_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 62 86 5) 1) 14) v4146_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4146 : Material (62 : Basis) (86 : Basis) where
  plus := ![v4146_pa,v4146_pb,v4146_pg]
  minus := ![(Primitive.Addresses.material4146 1).one,v4146_mb,v4146_mg]
  upper := v4146_upper
  lower := (Primitive.Addresses.material4146 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4146_pa_checked.trans (by decide +kernel)
    · exact v4146_pb_checked.trans (by decide +kernel)
    · exact v4146_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 62 86 Primitive.Addresses.material4146
    · exact v4146_mb_checked.trans (by decide +kernel)
    · exact v4146_mg_checked.trans (by decide +kernel)
  upper_error := v4146_upper_checked
  lower_error := reuse_lower_error 62 86 Primitive.Addresses.material4146

def v4147_pa : Scalar.QComplex := ((999998085799776806481223640642 : Int)/10^30,(-1956628933197233255765904473 : Int)/10^30)
theorem v4147_pa_checked : Scalar.distance (sourceCoefficient 62 87 1 0) v4147_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4147_pb : Scalar.QComplex := ((-844241360543483581528465 : Int)/10^30,(-431476674075830632101368728 : Int)/10^30)
theorem v4147_pb_checked : Scalar.distance (sourceCoefficient 62 87 1 1) v4147_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4147_pg : Scalar.QComplex := ((-93086249446683693614023 : Int)/10^30,(182135597594197826168 : Int)/10^30)
theorem v4147_pg_checked : Scalar.distance (sourceCoefficient 62 87 1 2) v4147_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4147_mb : Scalar.QComplex := ((-1216585982933269199171674 : Int)/10^30,(-431475784875074485867657057 : Int)/10^30)
theorem v4147_mb_checked : Scalar.distance (sourceCoefficient 62 87 3 1) v4147_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4147_mg : Scalar.QComplex := ((-93086057611601131859841 : Int)/10^30,(262464770600234806795 : Int)/10^30)
theorem v4147_mg_checked : Scalar.distance (sourceCoefficient 62 87 3 2) v4147_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4147_upper : Scalar.QComplex := ((999993219456061326360514034399 : Int)/10^30,(-3682531996001008908015892493 : Int)/10^30)
theorem v4147_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 62 87 5) 1) 14) v4147_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4147 : Material (62 : Basis) (87 : Basis) where
  plus := ![v4147_pa,v4147_pb,v4147_pg]
  minus := ![(Primitive.Addresses.material4147 1).one,v4147_mb,v4147_mg]
  upper := v4147_upper
  lower := (Primitive.Addresses.material4147 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4147_pa_checked.trans (by decide +kernel)
    · exact v4147_pb_checked.trans (by decide +kernel)
    · exact v4147_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 62 87 Primitive.Addresses.material4147
    · exact v4147_mb_checked.trans (by decide +kernel)
    · exact v4147_mg_checked.trans (by decide +kernel)
  upper_error := v4147_upper_checked
  lower_error := reuse_lower_error 62 87 Primitive.Addresses.material4147

def v4148_pa : Scalar.QComplex := ((999998062721471925853826733962 : Int)/10^30,(-1968388504106899372896938348 : Int)/10^30)
theorem v4148_pa_checked : Scalar.distance (sourceCoefficient 62 88 1 0) v4148_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4148_pb : Scalar.QComplex := ((-849315348982548234606926 : Int)/10^30,(-431476663194347990462030221 : Int)/10^30)
theorem v4148_pb_checked : Scalar.distance (sourceCoefficient 62 88 1 1) v4148_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4148_pg : Scalar.QComplex := ((-93086247198766345456983 : Int)/10^30,(183230253844541205435 : Int)/10^30)
theorem v4148_pg_checked : Scalar.distance (sourceCoefficient 62 88 1 2) v4148_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4148_mb : Scalar.QComplex := ((-1221659960092826627709631 : Int)/10^30,(-431475769614972396944906215 : Int)/10^30)
theorem v4148_mb_checked : Scalar.distance (sourceCoefficient 62 88 3 1) v4148_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4148_mg : Scalar.QComplex := ((-93086054419045578146186 : Int)/10^30,(263559424503136206777 : Int)/10^30)
theorem v4148_mg_checked : Scalar.distance (sourceCoefficient 62 88 3 2) v4148_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4148_upper : Scalar.QComplex := ((999993176081838248012935402601 : Int)/10^30,(-3694291509565114954935889299 : Int)/10^30)
theorem v4148_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 62 88 5) 1) 14) v4148_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4148 : Material (62 : Basis) (88 : Basis) where
  plus := ![v4148_pa,v4148_pb,v4148_pg]
  minus := ![(Primitive.Addresses.material4148 1).one,v4148_mb,v4148_mg]
  upper := v4148_upper
  lower := (Primitive.Addresses.material4148 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4148_pa_checked.trans (by decide +kernel)
    · exact v4148_pb_checked.trans (by decide +kernel)
    · exact v4148_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 62 88 Primitive.Addresses.material4148
    · exact v4148_mb_checked.trans (by decide +kernel)
    · exact v4148_mg_checked.trans (by decide +kernel)
  upper_error := v4148_upper_checked
  lower_error := reuse_lower_error 62 88 Primitive.Addresses.material4148

def v4149_pa : Scalar.QComplex := ((999998030921680041073322395791 : Int)/10^30,(-1984477957209004431359252492 : Int)/10^30)
theorem v4149_pa_checked : Scalar.distance (sourceCoefficient 62 89 1 0) v4149_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4149_pb : Scalar.QComplex := ((-856257583396729928416317 : Int)/10^30,(-431476648177405595639823684 : Int)/10^30)
theorem v4149_pb_checked : Scalar.distance (sourceCoefficient 62 89 1 1) v4149_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4149_pg : Scalar.QComplex := ((-93086244098833451510003 : Int)/10^30,(184727963277339331029 : Int)/10^30)
theorem v4149_pg_checked : Scalar.distance (sourceCoefficient 62 89 1 2) v4149_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4149_mb : Scalar.QComplex := ((-1228602178963152224579761 : Int)/10^30,(-431475748607199960809143496 : Int)/10^30)
theorem v4149_mb_checked : Scalar.distance (sourceCoefficient 62 89 3 1) v4149_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4149_mg : Scalar.QComplex := ((-93086050026658052269945 : Int)/10^30,(265057130703166190155 : Int)/10^30)
theorem v4149_mg_checked : Scalar.distance (sourceCoefficient 62 89 3 2) v4149_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4149_upper : Scalar.QComplex := ((999993116513157294837114277495 : Int)/10^30,(-3710380883820313679192735238 : Int)/10^30)
theorem v4149_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 62 89 5) 1) 14) v4149_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4149 : Material (62 : Basis) (89 : Basis) where
  plus := ![v4149_pa,v4149_pb,v4149_pg]
  minus := ![(Primitive.Addresses.material4149 1).one,v4149_mb,v4149_mg]
  upper := v4149_upper
  lower := (Primitive.Addresses.material4149 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4149_pa_checked.trans (by decide +kernel)
    · exact v4149_pb_checked.trans (by decide +kernel)
    · exact v4149_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 62 89 Primitive.Addresses.material4149
    · exact v4149_mb_checked.trans (by decide +kernel)
    · exact v4149_mg_checked.trans (by decide +kernel)
  upper_error := v4149_upper_checked
  lower_error := reuse_lower_error 62 89 Primitive.Addresses.material4149

def v4150_pa : Scalar.QComplex := ((999997978579223465718066482449 : Int)/10^30,(-2010680846610572371813136195 : Int)/10^30)
theorem v4150_pa_checked : Scalar.distance (sourceCoefficient 62 90 1 0) v4150_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4150_pb : Scalar.QComplex := ((-867563536146383997601577 : Int)/10^30,(-431476623402409117303408969 : Int)/10^30)
theorem v4150_pb_checked : Scalar.distance (sourceCoefficient 62 90 1 1) v4150_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4150_pg : Scalar.QComplex := ((-93086238990183603525652 : Int)/10^30,(187167096164033308923 : Int)/10^30)
theorem v4150_pg_checked : Scalar.distance (sourceCoefficient 62 90 1 2) v4150_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4150_mb : Scalar.QComplex := ((-1239908106123377241117989 : Int)/10^30,(-431475714075684685594136243 : Int)/10^30)
theorem v4150_mb_checked : Scalar.distance (sourceCoefficient 62 90 3 1) v4150_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4150_mg : Scalar.QComplex := ((-93086042813148279719733 : Int)/10^30,(267496258273124786690 : Int)/10^30)
theorem v4150_mg_checked : Scalar.distance (sourceCoefficient 62 90 3 2) v4150_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4150_upper : Scalar.QComplex := ((999993018946968677873650306794 : Int)/10^30,(-3736583643857424285122849412 : Int)/10^30)
theorem v4150_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 62 90 5) 1) 14) v4150_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4150 : Material (62 : Basis) (90 : Basis) where
  plus := ![v4150_pa,v4150_pb,v4150_pg]
  minus := ![(Primitive.Addresses.material4150 1).one,v4150_mb,v4150_mg]
  upper := v4150_upper
  lower := (Primitive.Addresses.material4150 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4150_pa_checked.trans (by decide +kernel)
    · exact v4150_pb_checked.trans (by decide +kernel)
    · exact v4150_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 62 90 Primitive.Addresses.material4150
    · exact v4150_mb_checked.trans (by decide +kernel)
    · exact v4150_mg_checked.trans (by decide +kernel)
  upper_error := v4150_upper_checked
  lower_error := reuse_lower_error 62 90 Primitive.Addresses.material4150

def v4151_pa : Scalar.QComplex := ((999997948790476367889872915812 : Int)/10^30,(-2025441887540521468392062413 : Int)/10^30)
theorem v4151_pa_checked : Scalar.distance (sourceCoefficient 62 91 1 0) v4151_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4151_pb : Scalar.QComplex := ((-873932590531945791587440 : Int)/10^30,(-431476609271816994648005571 : Int)/10^30)
theorem v4151_pb_checked : Scalar.distance (sourceCoefficient 62 91 1 1) v4151_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4151_pg : Scalar.QComplex := ((-93086236079461258142247 : Int)/10^30,(188541148446225891082 : Int)/10^30)
theorem v4151_pg_checked : Scalar.distance (sourceCoefficient 62 91 1 2) v4151_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4151_mb : Scalar.QComplex := ((-1246277145943384423586759 : Int)/10^30,(-431475694448890741225247084 : Int)/10^30)
theorem v4151_mb_checked : Scalar.distance (sourceCoefficient 62 91 3 1) v4151_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4151_mg : Scalar.QComplex := ((-93086038716681783616596 : Int)/10^30,(268870307531872616900 : Int)/10^30)
theorem v4151_mg_checked : Scalar.distance (sourceCoefficient 62 91 3 2) v4151_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4151_upper : Scalar.QComplex := ((999992963682048412965488778777 : Int)/10^30,(-3751344611389861793388983141 : Int)/10^30)
theorem v4151_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 62 91 5) 1) 14) v4151_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4151 : Material (62 : Basis) (91 : Basis) where
  plus := ![v4151_pa,v4151_pb,v4151_pg]
  minus := ![(Primitive.Addresses.material4151 1).one,v4151_mb,v4151_mg]
  upper := v4151_upper
  lower := (Primitive.Addresses.material4151 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4151_pa_checked.trans (by decide +kernel)
    · exact v4151_pb_checked.trans (by decide +kernel)
    · exact v4151_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 62 91 Primitive.Addresses.material4151
    · exact v4151_mb_checked.trans (by decide +kernel)
    · exact v4151_mg_checked.trans (by decide +kernel)
  upper_error := v4151_upper_checked
  lower_error := reuse_lower_error 62 91 Primitive.Addresses.material4151

def v4152_pa : Scalar.QComplex := ((999997883554648216389474442295 : Int)/10^30,(-2057397925591034993708176137 : Int)/10^30)
theorem v4152_pa_checked : Scalar.distance (sourceCoefficient 62 92 1 0) v4152_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4152_pb : Scalar.QComplex := ((-887720895847893163559365 : Int)/10^30,(-431476578251196451649632777 : Int)/10^30)
theorem v4152_pb_checked : Scalar.distance (sourceCoefficient 62 92 1 1) v4152_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4152_pg : Scalar.QComplex := ((-93086229697000816300117 : Int)/10^30,(191515821212469675515 : Int)/10^30)
theorem v4152_pg_checked : Scalar.distance (sourceCoefficient 62 92 1 2) v4152_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4152_mb : Scalar.QComplex := ((-1260065419355917158026411 : Int)/10^30,(-431475651529595263177777141 : Int)/10^30)
theorem v4152_mb_checked : Scalar.distance (sourceCoefficient 62 92 3 1) v4152_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4152_mg : Scalar.QComplex := ((-93086029767215095275828 : Int)/10^30,(271844973682733875237 : Int)/10^30)
theorem v4152_mg_checked : Scalar.distance (sourceCoefficient 62 92 3 2) v4152_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4152_upper : Scalar.QComplex := ((999992843293094776507608418176 : Int)/10^30,(-3783300489254489220996261967 : Int)/10^30)
theorem v4152_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 62 92 5) 1) 14) v4152_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4152 : Material (62 : Basis) (92 : Basis) where
  plus := ![v4152_pa,v4152_pb,v4152_pg]
  minus := ![(Primitive.Addresses.material4152 1).one,v4152_mb,v4152_mg]
  upper := v4152_upper
  lower := (Primitive.Addresses.material4152 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4152_pa_checked.trans (by decide +kernel)
    · exact v4152_pb_checked.trans (by decide +kernel)
    · exact v4152_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 62 92 Primitive.Addresses.material4152
    · exact v4152_mb_checked.trans (by decide +kernel)
    · exact v4152_mg_checked.trans (by decide +kernel)
  upper_error := v4152_upper_checked
  lower_error := reuse_lower_error 62 92 Primitive.Addresses.material4152

def v4153_pa : Scalar.QComplex := ((999997804807398907528876770993 : Int)/10^30,(-2095323455534821801544460857 : Int)/10^30)
theorem v4153_pa_checked : Scalar.distance (sourceCoefficient 62 93 1 0) v4153_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4153_pb : Scalar.QComplex := ((-904084900826604830404391 : Int)/10^30,(-431476540673457366330005009 : Int)/10^30)
theorem v4153_pb_checked : Scalar.distance (sourceCoefficient 62 93 1 1) v4153_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4153_pg : Scalar.QComplex := ((-93086221978363048089144 : Int)/10^30,(195046172462299798751 : Int)/10^30)
theorem v4153_pg_checked : Scalar.distance (sourceCoefficient 62 93 1 2) v4153_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4153_mb : Scalar.QComplex := ((-1276429385813665507235223 : Int)/10^30,(-431475599830470880564869394 : Int)/10^30)
theorem v4153_mb_checked : Scalar.distance (sourceCoefficient 62 93 3 1) v4153_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4153_mg : Scalar.QComplex := ((-93086019002046073580952 : Int)/10^30,(275375316957216123712 : Int)/10^30)
theorem v4153_mg_checked : Scalar.distance (sourceCoefficient 62 93 3 2) v4153_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4153_upper : Scalar.QComplex := ((999992699089938646648710447470 : Int)/10^30,(-3821225826802045810818050803 : Int)/10^30)
theorem v4153_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 62 93 5) 1) 14) v4153_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4153 : Material (62 : Basis) (93 : Basis) where
  plus := ![v4153_pa,v4153_pb,v4153_pg]
  minus := ![(Primitive.Addresses.material4153 1).one,v4153_mb,v4153_mg]
  upper := v4153_upper
  lower := (Primitive.Addresses.material4153 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4153_pa_checked.trans (by decide +kernel)
    · exact v4153_pb_checked.trans (by decide +kernel)
    · exact v4153_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 62 93 Primitive.Addresses.material4153
    · exact v4153_mb_checked.trans (by decide +kernel)
    · exact v4153_mg_checked.trans (by decide +kernel)
  upper_error := v4153_upper_checked
  lower_error := reuse_lower_error 62 93 Primitive.Addresses.material4153

def v4154_pa : Scalar.QComplex := ((999997709936477467744470773204 : Int)/10^30,(-2140121912572639826623869493 : Int)/10^30)
theorem v4154_pa_checked : Scalar.distance (sourceCoefficient 62 94 1 0) v4154_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4154_pb : Scalar.QComplex := ((-923414416857615786663310 : Int)/10^30,(-431476495219802662918651891 : Int)/10^30)
theorem v4154_pb_checked : Scalar.distance (sourceCoefficient 62 94 1 1) v4154_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4154_pg : Scalar.QComplex := ((-93086212659707564526779 : Int)/10^30,(199216299689417843624 : Int)/10^30)
theorem v4154_pg_checked : Scalar.distance (sourceCoefficient 62 94 1 2) v4154_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4154_mb : Scalar.QComplex := ((-1295758855422957390194994 : Int)/10^30,(-431475537696331335949034970 : Int)/10^30)
theorem v4154_mb_checked : Scalar.distance (sourceCoefficient 62 94 3 1) v4154_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4154_mg : Scalar.QComplex := ((-93086006084762078335303 : Int)/10^30,(279545434590025232049 : Int)/10^30)
theorem v4154_mg_checked : Scalar.distance (sourceCoefficient 62 94 3 2) v4154_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4154_upper : Scalar.QComplex := ((999992526901085742959143151584 : Int)/10^30,(-3866024053379220692188245212 : Int)/10^30)
theorem v4154_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 62 94 5) 1) 14) v4154_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4154 : Material (62 : Basis) (94 : Basis) where
  plus := ![v4154_pa,v4154_pb,v4154_pg]
  minus := ![(Primitive.Addresses.material4154 1).one,v4154_mb,v4154_mg]
  upper := v4154_upper
  lower := (Primitive.Addresses.material4154 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4154_pa_checked.trans (by decide +kernel)
    · exact v4154_pb_checked.trans (by decide +kernel)
    · exact v4154_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 62 94 Primitive.Addresses.material4154
    · exact v4154_mb_checked.trans (by decide +kernel)
    · exact v4154_mg_checked.trans (by decide +kernel)
  upper_error := v4154_upper_checked
  lower_error := reuse_lower_error 62 94 Primitive.Addresses.material4154

def v4155_pa : Scalar.QComplex := ((999997614204140055549700670965 : Int)/10^30,(-2184396032743837243434817837 : Int)/10^30)
theorem v4155_pa_checked : Scalar.distance (sourceCoefficient 62 95 1 0) v4155_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4155_pb : Scalar.QComplex := ((-942517692430527137127436 : Int)/10^30,(-431476449163761509445011842 : Int)/10^30)
theorem v4155_pb_checked : Scalar.distance (sourceCoefficient 62 95 1 1) v4155_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4155_pg : Scalar.QComplex := ((-93086203235979954859408 : Int)/10^30,(203337618173908768120 : Int)/10^30)
theorem v4155_pg_checked : Scalar.distance (sourceCoefficient 62 95 1 2) v4155_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4155_mb : Scalar.QComplex := ((-1314862084138556953685008 : Int)/10^30,(-431475475155040891414898110 : Int)/10^30)
theorem v4155_mb_checked : Scalar.distance (sourceCoefficient 62 95 3 1) v4155_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4155_mg : Scalar.QComplex := ((-93085993104525742730842 : Int)/10^30,(283666743407708433003 : Int)/10^30)
theorem v4155_mg_checked : Scalar.distance (sourceCoefficient 62 95 3 2) v4155_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4155_upper : Scalar.QComplex := ((999992354755776014155320354016 : Int)/10^30,(-3910297942383987313852631783 : Int)/10^30)
theorem v4155_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 62 95 5) 1) 14) v4155_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4155 : Material (62 : Basis) (95 : Basis) where
  plus := ![v4155_pa,v4155_pb,v4155_pg]
  minus := ![(Primitive.Addresses.material4155 1).one,v4155_mb,v4155_mg]
  upper := v4155_upper
  lower := (Primitive.Addresses.material4155 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4155_pa_checked.trans (by decide +kernel)
    · exact v4155_pb_checked.trans (by decide +kernel)
    · exact v4155_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 62 95 Primitive.Addresses.material4155
    · exact v4155_mb_checked.trans (by decide +kernel)
    · exact v4155_mg_checked.trans (by decide +kernel)
  upper_error := v4155_upper_checked
  lower_error := reuse_lower_error 62 95 Primitive.Addresses.material4155

def v4156_pa : Scalar.QComplex := ((999997567528851335511536980797 : Int)/10^30,(-2205660078165510942542225769 : Int)/10^30)
theorem v4156_pa_checked : Scalar.distance (sourceCoefficient 62 96 1 0) v4156_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4156_pb : Scalar.QComplex := ((-951692643880910414380848 : Int)/10^30,(-431476426643016797523184560 : Int)/10^30)
theorem v4156_pb_checked : Scalar.distance (sourceCoefficient 62 96 1 1) v4156_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4156_pg : Scalar.QComplex := ((-93086198634263068463909 : Int)/10^30,(205317011583485964376 : Int)/10^30)
theorem v4156_pg_checked : Scalar.distance (sourceCoefficient 62 96 1 2) v4156_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4156_mb : Scalar.QComplex := ((-1324037012738298100265638 : Int)/10^30,(-431475444716734687788519440 : Int)/10^30)
theorem v4156_mb_checked : Scalar.distance (sourceCoefficient 62 96 3 1) v4156_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4156_mg : Scalar.QComplex := ((-93085986794683205869545 : Int)/10^30,(285646132109192580801 : Int)/10^30)
theorem v4156_mg_checked : Scalar.distance (sourceCoefficient 62 96 3 2) v4156_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4156_upper : Scalar.QComplex := ((999992271380743472799707200932 : Int)/10^30,(-3931561875578049225946595181 : Int)/10^30)
theorem v4156_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 62 96 5) 1) 14) v4156_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4156 : Material (62 : Basis) (96 : Basis) where
  plus := ![v4156_pa,v4156_pb,v4156_pg]
  minus := ![(Primitive.Addresses.material4156 1).one,v4156_mb,v4156_mg]
  upper := v4156_upper
  lower := (Primitive.Addresses.material4156 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4156_pa_checked.trans (by decide +kernel)
    · exact v4156_pb_checked.trans (by decide +kernel)
    · exact v4156_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 62 96 Primitive.Addresses.material4156
    · exact v4156_mb_checked.trans (by decide +kernel)
    · exact v4156_mg_checked.trans (by decide +kernel)
  upper_error := v4156_upper_checked
  lower_error := reuse_lower_error 62 96 Primitive.Addresses.material4156

def v4157_pa : Scalar.QComplex := ((999997403481507363142098547361 : Int)/10^30,(-2278822117534721751701923135 : Int)/10^30)
theorem v4157_pa_checked : Scalar.distance (sourceCoefficient 62 97 1 0) v4157_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4157_pb : Scalar.QComplex := ((-983260396177649569568740 : Int)/10^30,(-431476347169895415176773563 : Int)/10^30)
theorem v4157_pb_checked : Scalar.distance (sourceCoefficient 62 97 1 1) v4157_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4157_pg : Scalar.QComplex := ((-93086182426255514539008 : Int)/10^30,(212127402142545452686 : Int)/10^30)
theorem v4157_pg_checked : Scalar.distance (sourceCoefficient 62 97 1 2) v4157_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4157_mb : Scalar.QComplex := ((-1355604684699195941376780 : Int)/10^30,(-431475338002094423616687403 : Int)/10^30)
theorem v4157_mb_checked : Scalar.distance (sourceCoefficient 62 97 3 1) v4157_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4157_mg : Scalar.QComplex := ((-93085964709621363062740 : Int)/10^30,(292456506145651876273 : Int)/10^30)
theorem v4157_mg_checked : Scalar.distance (sourceCoefficient 62 97 3 2) v4157_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4157_upper : Scalar.QComplex := ((999991981062601086785452652713 : Int)/10^30,(-4004723522850163174003603357 : Int)/10^30)
theorem v4157_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 62 97 5) 1) 14) v4157_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4157 : Material (62 : Basis) (97 : Basis) where
  plus := ![v4157_pa,v4157_pb,v4157_pg]
  minus := ![(Primitive.Addresses.material4157 1).one,v4157_mb,v4157_mg]
  upper := v4157_upper
  lower := (Primitive.Addresses.material4157 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4157_pa_checked.trans (by decide +kernel)
    · exact v4157_pb_checked.trans (by decide +kernel)
    · exact v4157_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 62 97 Primitive.Addresses.material4157
    · exact v4157_mb_checked.trans (by decide +kernel)
    · exact v4157_mg_checked.trans (by decide +kernel)
  upper_error := v4157_upper_checked
  lower_error := reuse_lower_error 62 97 Primitive.Addresses.material4157

def v4158_pa : Scalar.QComplex := ((999998872911996332118433228804 : Int)/10^30,(-1501390934103571547702263337 : Int)/10^30)
theorem v4158_pa_checked : Scalar.distance (sourceCoefficient 63 64 1 0) v4158_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4158_pb : Scalar.QComplex := ((-647816438164275323475198 : Int)/10^30,(-431477034597206742819764875 : Int)/10^30)
theorem v4158_pb_checked : Scalar.distance (sourceCoefficient 63 64 1 1) v4158_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4158_pg : Scalar.QComplex := ((-93086324970636123634305 : Int)/10^30,(139759121920761707032 : Int)/10^30)
theorem v4158_pg_checked : Scalar.distance (sourceCoefficient 63 64 1 2) v4158_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4158_mb : Scalar.QComplex := ((-1020161444805746908852370 : Int)/10^30,(-431476314902177721156941959 : Int)/10^30)
theorem v4158_mb_checked : Scalar.distance (sourceCoefficient 63 64 3 1) v4158_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4158_mg : Scalar.QComplex := ((-93086169704515381421343 : Int)/10^30,(220088375879266756051 : Int)/10^30)
theorem v4158_mg_checked : Scalar.distance (sourceCoefficient 63 64 3 2) v4158_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4158_upper : Scalar.QComplex := ((999994792266596107798825402731 : Int)/10^30,(-3227296033415155476592446950 : Int)/10^30)
theorem v4158_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 63 64 5) 1) 14) v4158_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4158 : Material (63 : Basis) (64 : Basis) where
  plus := ![v4158_pa,v4158_pb,v4158_pg]
  minus := ![(Primitive.Addresses.material4158 1).one,v4158_mb,v4158_mg]
  upper := v4158_upper
  lower := (Primitive.Addresses.material4158 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4158_pa_checked.trans (by decide +kernel)
    · exact v4158_pb_checked.trans (by decide +kernel)
    · exact v4158_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 63 64 Primitive.Addresses.material4158
    · exact v4158_mb_checked.trans (by decide +kernel)
    · exact v4158_mg_checked.trans (by decide +kernel)
  upper_error := v4158_upper_checked
  lower_error := reuse_lower_error 63 64 Primitive.Addresses.material4158

def v4159_pa : Scalar.QComplex := ((999998818265242726811442951487 : Int)/10^30,(-1537357511462229974222792951 : Int)/10^30)
theorem v4159_pa_checked : Scalar.distance (sourceCoefficient 63 65 1 0) v4159_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4159_pb : Scalar.QComplex := ((-663335207373784648968109 : Int)/10^30,(-431477010742020412710299424 : Int)/10^30)
theorem v4159_pb_checked : Scalar.distance (sourceCoefficient 63 65 1 1) v4159_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4159_pg : Scalar.QComplex := ((-93086319853956239671626 : Int)/10^30,(143107122156515601046 : Int)/10^30)
theorem v4159_pg_checked : Scalar.distance (sourceCoefficient 63 65 1 2) v4159_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4159_mb : Scalar.QComplex := ((-1035680187650957809679101 : Int)/10^30,(-431476277655001385036380640 : Int)/10^30)
theorem v4159_mb_checked : Scalar.distance (sourceCoefficient 63 65 3 1) v4159_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4159_mg : Scalar.QComplex := ((-93086161698663987509910 : Int)/10^30,(223436370452942857971 : Int)/10^30)
theorem v4159_mg_checked : Scalar.distance (sourceCoefficient 63 65 3 2) v4159_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4159_upper : Scalar.QComplex := ((999994675544874233777522540250 : Int)/10^30,(-3263262462890482650354239375 : Int)/10^30)
theorem v4159_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 63 65 5) 1) 14) v4159_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4159 : Material (63 : Basis) (65 : Basis) where
  plus := ![v4159_pa,v4159_pb,v4159_pg]
  minus := ![(Primitive.Addresses.material4159 1).one,v4159_mb,v4159_mg]
  upper := v4159_upper
  lower := (Primitive.Addresses.material4159 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4159_pa_checked.trans (by decide +kernel)
    · exact v4159_pb_checked.trans (by decide +kernel)
    · exact v4159_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 63 65 Primitive.Addresses.material4159
    · exact v4159_mb_checked.trans (by decide +kernel)
    · exact v4159_mg_checked.trans (by decide +kernel)
  upper_error := v4159_upper_checked
  lower_error := reuse_lower_error 63 65 Primitive.Addresses.material4159

def v4160_pa : Scalar.QComplex := ((999998791072204165208645681599 : Int)/10^30,(-1554945056959623627289425239 : Int)/10^30)
theorem v4160_pa_checked : Scalar.distance (sourceCoefficient 63 66 1 0) v4160_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4160_pb : Scalar.QComplex := ((-670923837583595809972961 : Int)/10^30,(-431476998805972051227763295 : Int)/10^30)
theorem v4160_pb_checked : Scalar.distance (sourceCoefficient 63 66 1 1) v4160_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4160_pg : Scalar.QComplex := ((-93086317300770601680297 : Int)/10^30,(144744283942796488182 : Int)/10^30)
theorem v4160_pg_checked : Scalar.distance (sourceCoefficient 63 66 1 2) v4160_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4160_mb : Scalar.QComplex := ((-1043268804734902969740413 : Int)/10^30,(-431476259170311376040330875 : Int)/10^30)
theorem v4160_mb_checked : Scalar.distance (sourceCoefficient 63 66 3 1) v4160_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4160_mg : Scalar.QComplex := ((-93086157732682413655556 : Int)/10^30,(225073529426349375711 : Int)/10^30)
theorem v4160_mg_checked : Scalar.distance (sourceCoefficient 63 66 3 2) v4160_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4160_upper : Scalar.QComplex := ((999994617997368174173828686186 : Int)/10^30,(-3280849935260575639135459868 : Int)/10^30)
theorem v4160_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 63 66 5) 1) 14) v4160_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4160 : Material (63 : Basis) (66 : Basis) where
  plus := ![v4160_pa,v4160_pb,v4160_pg]
  minus := ![(Primitive.Addresses.material4160 1).one,v4160_mb,v4160_mg]
  upper := v4160_upper
  lower := (Primitive.Addresses.material4160 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4160_pa_checked.trans (by decide +kernel)
    · exact v4160_pb_checked.trans (by decide +kernel)
    · exact v4160_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 63 66 Primitive.Addresses.material4160
    · exact v4160_mb_checked.trans (by decide +kernel)
    · exact v4160_mg_checked.trans (by decide +kernel)
  upper_error := v4160_upper_checked
  lower_error := reuse_lower_error 63 66 Primitive.Addresses.material4160

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
