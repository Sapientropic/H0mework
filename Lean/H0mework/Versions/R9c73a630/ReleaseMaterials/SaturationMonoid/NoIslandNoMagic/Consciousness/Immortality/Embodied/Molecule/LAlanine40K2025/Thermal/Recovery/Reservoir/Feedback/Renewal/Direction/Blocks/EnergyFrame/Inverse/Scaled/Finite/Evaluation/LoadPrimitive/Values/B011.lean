import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B007
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B008

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v177_pa : Scalar.QComplex := ((999977344916414915208553057550 : Int)/10^30,(6731244603886961387527766489 : Int)/10^30)
theorem v177_pa_checked : Scalar.distance (sourceCoefficient 1 82 1 0) v177_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v177_pb : Scalar.QComplex := ((2904342033472888310728716 : Int)/10^30,(-431461996446286350512427471 : Int)/10^30)
theorem v177_pb_checked : Scalar.distance (sourceCoefficient 1 82 1 1) v177_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v177_pg : Scalar.QComplex := ((-93083700831594337536911 : Int)/10^30,(-626583354230760765554 : Int)/10^30)
theorem v177_pg_checked : Scalar.distance (sourceCoefficient 1 82 1 2) v177_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v177_mb : Scalar.QComplex := ((2532008681447427196252137 : Int)/10^30,(-431464342109634463882858307 : Int)/10^30)
theorem v177_mb_checked : Scalar.distance (sourceCoefficient 1 82 3 1) v177_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v177_mg : Scalar.QComplex := ((-93084206885492817105317 : Int)/10^30,(-546256079441734490225 : Int)/10^30)
theorem v177_mg_checked : Scalar.distance (sourceCoefficient 1 82 3 2) v177_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v177_upper : Scalar.QComplex := ((999987473085157821246067944093 : Int)/10^30,(5005364398399185947699799282 : Int)/10^30)
theorem v177_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 1 82 5) 1) 14) v177_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material177 : Material (1 : Basis) (82 : Basis) where
  plus := ![v177_pa,v177_pb,v177_pg]
  minus := ![(Primitive.Addresses.material177 1).one,v177_mb,v177_mg]
  upper := v177_upper
  lower := (Primitive.Addresses.material177 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v177_pa_checked.trans (by decide +kernel)
    · exact v177_pb_checked.trans (by decide +kernel)
    · exact v177_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 1 82 Primitive.Addresses.material177
    · exact v177_mb_checked.trans (by decide +kernel)
    · exact v177_mg_checked.trans (by decide +kernel)
  upper_error := v177_upper_checked
  lower_error := reuse_lower_error 1 82 Primitive.Addresses.material177

def v178_pa : Scalar.QComplex := ((999977436158068930807945969887 : Int)/10^30,(6717676289847233613258178244 : Int)/10^30)
theorem v178_pa_checked : Scalar.distance (sourceCoefficient 1 83 1 0) v178_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v178_pb : Scalar.QComplex := ((2898487571669318842144247 : Int)/10^30,(-431462018352156325860675572 : Int)/10^30)
theorem v178_pb_checked : Scalar.distance (sourceCoefficient 1 83 1 1) v178_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v178_pg : Scalar.QComplex := ((-93083707441241970494326 : Int)/10^30,(-625320324078056473919 : Int)/10^30)
theorem v178_pg_checked : Scalar.distance (sourceCoefficient 1 83 1 2) v178_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v178_mb : Scalar.QComplex := ((2526154202919962234292540 : Int)/10^30,(-431464358963359421365665790 : Int)/10^30)
theorem v178_mb_checked : Scalar.distance (sourceCoefficient 1 83 3 1) v178_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v178_mg : Scalar.QComplex := ((-93084212405199851971455 : Int)/10^30,(-544993044055485828008 : Int)/10^30)
theorem v178_mg_checked : Scalar.distance (sourceCoefficient 1 83 3 2) v178_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v178_upper : Scalar.QComplex := ((999987540908996818384023585957 : Int)/10^30,(4991795947093050636744453365 : Int)/10^30)
theorem v178_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 1 83 5) 1) 14) v178_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material178 : Material (1 : Basis) (83 : Basis) where
  plus := ![v178_pa,v178_pb,v178_pg]
  minus := ![(Primitive.Addresses.material178 1).one,v178_mb,v178_mg]
  upper := v178_upper
  lower := (Primitive.Addresses.material178 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v178_pa_checked.trans (by decide +kernel)
    · exact v178_pb_checked.trans (by decide +kernel)
    · exact v178_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 1 83 Primitive.Addresses.material178
    · exact v178_mb_checked.trans (by decide +kernel)
    · exact v178_mg_checked.trans (by decide +kernel)
  upper_error := v178_upper_checked
  lower_error := reuse_lower_error 1 83 Primitive.Addresses.material178

def v179_pa : Scalar.QComplex := ((999977671593517452001312171406 : Int)/10^30,(6682538021392766268333641153 : Int)/10^30)
theorem v179_pa_checked : Scalar.distance (sourceCoefficient 1 84 1 0) v179_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v179_pb : Scalar.QComplex := ((2883326098314554258017582 : Int)/10^30,(-431462074590109631421406452 : Int)/10^30)
theorem v179_pb_checked : Scalar.distance (sourceCoefficient 1 84 1 1) v179_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v179_pg : Scalar.QComplex := ((-93083724465505027862337 : Int)/10^30,(-622049417285826788818 : Int)/10^30)
theorem v179_pg_checked : Scalar.distance (sourceCoefficient 1 84 1 2) v179_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v179_mb : Scalar.QComplex := ((2510992686679686254401329 : Int)/10^30,(-431464402117623129215754641 : Int)/10^30)
theorem v179_mb_checked : Scalar.distance (sourceCoefficient 1 84 3 1) v179_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v179_mg : Scalar.QComplex := ((-93084226606811324907353 : Int)/10^30,(-541722123789991955315 : Int)/10^30)
theorem v179_mg_checked : Scalar.distance (sourceCoefficient 1 84 3 2) v179_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v179_upper : Scalar.QComplex := ((999987715698631052535467096466 : Int)/10^30,(4956657324632680913252461288 : Int)/10^30)
theorem v179_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 1 84 5) 1) 14) v179_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material179 : Material (1 : Basis) (84 : Basis) where
  plus := ![v179_pa,v179_pb,v179_pg]
  minus := ![(Primitive.Addresses.material179 1).one,v179_mb,v179_mg]
  upper := v179_upper
  lower := (Primitive.Addresses.material179 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v179_pa_checked.trans (by decide +kernel)
    · exact v179_pb_checked.trans (by decide +kernel)
    · exact v179_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 1 84 Primitive.Addresses.material179
    · exact v179_mb_checked.trans (by decide +kernel)
    · exact v179_mg_checked.trans (by decide +kernel)
  upper_error := v179_upper_checked
  lower_error := reuse_lower_error 1 84 Primitive.Addresses.material179

def v180_pa : Scalar.QComplex := ((999978196768784918378198060123 : Int)/10^30,(6603482948359284231329282077 : Int)/10^30)
theorem v180_pa_checked : Scalar.distance (sourceCoefficient 1 85 1 0) v180_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v180_pb : Scalar.QComplex := ((2849215392883271138350300 : Int)/10^30,(-431462198518917258272226513 : Int)/10^30)
theorem v180_pb_checked : Scalar.distance (sourceCoefficient 1 85 1 1) v180_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v180_pg : Scalar.QComplex := ((-93083762276944684643247 : Int)/10^30,(-614690439202705043210 : Int)/10^30)
theorem v180_pg_checked : Scalar.distance (sourceCoefficient 1 85 1 2) v180_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v180_mb : Scalar.QComplex := ((2476881887004398267378494 : Int)/10^30,(-431464496610382113653227947 : Int)/10^30)
theorem v180_mb_checked : Scalar.distance (sourceCoefficient 1 85 3 1) v180_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v180_mg : Scalar.QComplex := ((-93084258067770253096522 : Int)/10^30,(-534363115817384612191 : Int)/10^30)
theorem v180_mg_checked : Scalar.distance (sourceCoefficient 1 85 3 2) v180_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v180_upper : Scalar.QComplex := ((999988104431232096455298981230 : Int)/10^30,(4877601462937575579529989883 : Int)/10^30)
theorem v180_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 1 85 5) 1) 14) v180_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material180 : Material (1 : Basis) (85 : Basis) where
  plus := ![v180_pa,v180_pb,v180_pg]
  minus := ![(Primitive.Addresses.material180 1).one,v180_mb,v180_mg]
  upper := v180_upper
  lower := (Primitive.Addresses.material180 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v180_pa_checked.trans (by decide +kernel)
    · exact v180_pb_checked.trans (by decide +kernel)
    · exact v180_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 1 85 Primitive.Addresses.material180
    · exact v180_mb_checked.trans (by decide +kernel)
    · exact v180_mg_checked.trans (by decide +kernel)
  upper_error := v180_upper_checked
  lower_error := reuse_lower_error 1 85 Primitive.Addresses.material180

def v181_pa : Scalar.QComplex := ((999978292971879938311369378584 : Int)/10^30,(6588898621549247369506087858 : Int)/10^30)
theorem v181_pa_checked : Scalar.distance (sourceCoefficient 1 86 1 0) v181_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v181_pb : Scalar.QComplex := ((2842922544523516955025999 : Int)/10^30,(-431462220988833201201576847 : Int)/10^30)
theorem v181_pb_checked : Scalar.distance (sourceCoefficient 1 86 1 1) v181_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v181_pg : Scalar.QComplex := ((-93083769178356413854656 : Int)/10^30,(-613332832060913396979 : Int)/10^30)
theorem v181_pg_checked : Scalar.distance (sourceCoefficient 1 86 1 2) v181_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v181_mb : Scalar.QComplex := ((2470589021597233674466872 : Int)/10^30,(-431464513649844974907188432 : Int)/10^30)
theorem v181_mb_checked : Scalar.distance (sourceCoefficient 1 86 3 1) v181_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v181_mg : Scalar.QComplex := ((-93084263797625593586625 : Int)/10^30,(-533005503225484656296 : Int)/10^30)
theorem v181_mg_checked : Scalar.distance (sourceCoefficient 1 86 3 2) v181_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v181_upper : Scalar.QComplex := ((999988175462958838848498370573 : Int)/10^30,(4863016991811365778084432073 : Int)/10^30)
theorem v181_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 1 86 5) 1) 14) v181_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material181 : Material (1 : Basis) (86 : Basis) where
  plus := ![v181_pa,v181_pb,v181_pg]
  minus := ![(Primitive.Addresses.material181 1).one,v181_mb,v181_mg]
  upper := v181_upper
  lower := (Primitive.Addresses.material181 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v181_pa_checked.trans (by decide +kernel)
    · exact v181_pb_checked.trans (by decide +kernel)
    · exact v181_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 1 86 Primitive.Addresses.material181
    · exact v181_mb_checked.trans (by decide +kernel)
    · exact v181_mg_checked.trans (by decide +kernel)
  upper_error := v181_upper_checked
  lower_error := reuse_lower_error 1 86 Primitive.Addresses.material181

def v182_pa : Scalar.QComplex := ((999978299334684884689620570672 : Int)/10^30,(6587932886069461326490257734 : Int)/10^30)
theorem v182_pa_checked : Scalar.distance (sourceCoefficient 1 87 1 0) v182_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v182_pb : Scalar.QComplex := ((2842505848790698987358259 : Int)/10^30,(-431462222472411535785680854 : Int)/10^30)
theorem v182_pb_checked : Scalar.distance (sourceCoefficient 1 87 1 1) v182_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v182_pg : Scalar.QComplex := ((-93083769634534121944109 : Int)/10^30,(-613242934914348700681 : Int)/10^30)
theorem v182_pg_checked : Scalar.distance (sourceCoefficient 1 87 1 2) v182_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v182_mb : Scalar.QComplex := ((2470172324739309287204752 : Int)/10^30,(-431464514773833106944501469 : Int)/10^30)
theorem v182_mb_checked : Scalar.distance (sourceCoefficient 1 87 3 1) v182_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v182_mg : Scalar.QComplex := ((-93084264176225943152118 : Int)/10^30,(-532915605718731959567 : Int)/10^30)
theorem v182_mg_checked : Scalar.distance (sourceCoefficient 1 87 3 2) v182_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v182_upper : Scalar.QComplex := ((999988180158982481303847138087 : Int)/10^30,(4862051246788305180658310251 : Int)/10^30)
theorem v182_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 1 87 5) 1) 14) v182_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material182 : Material (1 : Basis) (87 : Basis) where
  plus := ![v182_pa,v182_pb,v182_pg]
  minus := ![(Primitive.Addresses.material182 1).one,v182_mb,v182_mg]
  upper := v182_upper
  lower := (Primitive.Addresses.material182 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v182_pa_checked.trans (by decide +kernel)
    · exact v182_pb_checked.trans (by decide +kernel)
    · exact v182_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 1 87 Primitive.Addresses.material182
    · exact v182_mb_checked.trans (by decide +kernel)
    · exact v182_mg_checked.trans (by decide +kernel)
  upper_error := v182_upper_checked
  lower_error := reuse_lower_error 1 87 Primitive.Addresses.material182

def v183_pa : Scalar.QComplex := ((999978376736955473794608888095 : Int)/10^30,(6576173547249777228123714442 : Int)/10^30)
theorem v183_pa_checked : Scalar.distance (sourceCoefficient 1 88 1 0) v183_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v183_pb : Scalar.QComplex := ((2837431927112342224627993 : Int)/10^30,(-431462240494250431781382028 : Int)/10^30)
theorem v183_pb_checked : Scalar.distance (sourceCoefficient 1 88 1 1) v183_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v183_pg : Scalar.QComplex := ((-93083775181084769277399 : Int)/10^30,(-612148296667636104795 : Int)/10^30)
theorem v183_pg_checked : Scalar.distance (sourceCoefficient 1 88 1 2) v183_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v183_mb : Scalar.QComplex := ((2465098389398170161251842 : Int)/10^30,(-431464528417099405113353501 : Int)/10^30)
theorem v183_mb_checked : Scalar.distance (sourceCoefficient 1 88 3 1) v183_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v183_mg : Scalar.QComplex := ((-93084268778151019014647 : Int)/10^30,(-531820963093179809090 : Int)/10^30)
theorem v183_mg_checked : Scalar.distance (sourceCoefficient 1 88 3 2) v183_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v183_upper : Scalar.QComplex := ((999988237265585784928694785409 : Int)/10^30,(4850291791893477747579722630 : Int)/10^30)
theorem v183_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 1 88 5) 1) 14) v183_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material183 : Material (1 : Basis) (88 : Basis) where
  plus := ![v183_pa,v183_pb,v183_pg]
  minus := ![(Primitive.Addresses.material183 1).one,v183_mb,v183_mg]
  upper := v183_upper
  lower := (Primitive.Addresses.material183 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v183_pa_checked.trans (by decide +kernel)
    · exact v183_pb_checked.trans (by decide +kernel)
    · exact v183_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 1 88 Primitive.Addresses.material183
    · exact v183_mb_checked.trans (by decide +kernel)
    · exact v183_mg_checked.trans (by decide +kernel)
  upper_error := v183_upper_checked
  lower_error := reuse_lower_error 1 88 Primitive.Addresses.material183

def v184_pa : Scalar.QComplex := ((999978482414765049796979499544 : Int)/10^30,(6560084409779043589621156019 : Int)/10^30)
theorem v184_pa_checked : Scalar.distance (sourceCoefficient 1 89 1 0) v184_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v184_pb : Scalar.QComplex := ((2830489783489554636153561 : Int)/10^30,(-431462265022854499704396699 : Int)/10^30)
theorem v184_pb_checked : Scalar.distance (sourceCoefficient 1 89 1 1) v184_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v184_pg : Scalar.QComplex := ((-93083782745548959371168 : Int)/10^30,(-610650611718921703142 : Int)/10^30)
theorem v184_pg_checked : Scalar.distance (sourceCoefficient 1 89 1 2) v184_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v184_mb : Scalar.QComplex := ((2458156227193179331878579 : Int)/10^30,(-431464546954937055992563460 : Int)/10^30)
theorem v184_mb_checked : Scalar.distance (sourceCoefficient 1 89 3 1) v184_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v184_mg : Scalar.QComplex := ((-93084275050177734998265 : Int)/10^30,(-530323272174330056196 : Int)/10^30)
theorem v184_mg_checked : Scalar.distance (sourceCoefficient 1 89 3 2) v184_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v184_upper : Scalar.QComplex := ((999988315174846286910842775314 : Int)/10^30,(4834202495995312096699941376 : Int)/10^30)
theorem v184_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 1 89 5) 1) 14) v184_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material184 : Material (1 : Basis) (89 : Basis) where
  plus := ![v184_pa,v184_pb,v184_pg]
  minus := ![(Primitive.Addresses.material184 1).one,v184_mb,v184_mg]
  upper := v184_upper
  lower := (Primitive.Addresses.material184 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v184_pa_checked.trans (by decide +kernel)
    · exact v184_pb_checked.trans (by decide +kernel)
    · exact v184_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 1 89 Primitive.Addresses.material184
    · exact v184_mb_checked.trans (by decide +kernel)
    · exact v184_mg_checked.trans (by decide +kernel)
  upper_error := v184_upper_checked
  lower_error := reuse_lower_error 1 89 Primitive.Addresses.material184

def v185_pa : Scalar.QComplex := ((999978653964984555691037243525 : Int)/10^30,(6533882029672538964625761712 : Int)/10^30)
theorem v185_pa_checked : Scalar.distance (sourceCoefficient 1 90 1 0) v185_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v185_pb : Scalar.QComplex := ((2819183977238665980579731 : Int)/10^30,(-431462304650771290015146758 : Int)/10^30)
theorem v185_pb_checked : Scalar.distance (sourceCoefficient 1 90 1 1) v185_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v185_pg : Scalar.QComplex := ((-93083795004676459991406 : Int)/10^30,(-608211518339145235956 : Int)/10^30)
theorem v185_pg_checked : Scalar.distance (sourceCoefficient 1 90 1 2) v185_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v185_mb : Scalar.QComplex := ((2446850390954851629461894 : Int)/10^30,(-431464576826437491113245007 : Int)/10^30)
theorem v185_mb_checked : Scalar.distance (sourceCoefficient 1 90 3 1) v185_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v185_mg : Scalar.QComplex := ((-93084285204472936925875 : Int)/10^30,(-527884169123664623947 : Int)/10^30)
theorem v185_mg_checked : Scalar.distance (sourceCoefficient 1 90 3 2) v185_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v185_upper : Scalar.QComplex := ((999988441501879286432345922101 : Int)/10^30,(4807999858834058739731452769 : Int)/10^30)
theorem v185_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 1 90 5) 1) 14) v185_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material185 : Material (1 : Basis) (90 : Basis) where
  plus := ![v185_pa,v185_pb,v185_pg]
  minus := ![(Primitive.Addresses.material185 1).one,v185_mb,v185_mg]
  upper := v185_upper
  lower := (Primitive.Addresses.material185 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v185_pa_checked.trans (by decide +kernel)
    · exact v185_pb_checked.trans (by decide +kernel)
    · exact v185_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 1 90 Primitive.Addresses.material185
    · exact v185_mb_checked.trans (by decide +kernel)
    · exact v185_mg_checked.trans (by decide +kernel)
  upper_error := v185_upper_checked
  lower_error := reuse_lower_error 1 90 Primitive.Addresses.material185

def v186_pa : Scalar.QComplex := ((999978750303138735759168043393 : Int)/10^30,(6519121273063708395410661626 : Int)/10^30)
theorem v186_pa_checked : Scalar.distance (sourceCoefficient 1 91 1 0) v186_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v186_pb : Scalar.QComplex := ((2812815004638092049193679 : Int)/10^30,(-431462326800685811025780114 : Int)/10^30)
theorem v186_pb_checked : Scalar.distance (sourceCoefficient 1 91 1 1) v186_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v186_pg : Scalar.QComplex := ((-93083801877855719712392 : Int)/10^30,(-606837488112243225869 : Int)/10^30)
theorem v186_pg_checked : Scalar.distance (sourceCoefficient 1 91 1 2) v186_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v186_mb : Scalar.QComplex := ((2440481401611358637182208 : Int)/10^30,(-431464593480207258280734407 : Int)/10^30)
theorem v186_mb_checked : Scalar.distance (sourceCoefficient 1 91 3 1) v186_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v186_mg : Scalar.QComplex := ((-93084290891923435655845 : Int)/10^30,(-526510133477132718983 : Int)/10^30)
theorem v186_mg_checked : Scalar.distance (sourceCoefficient 1 91 3 2) v186_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v186_upper : Scalar.QComplex := ((999988512364163160674129763014 : Int)/10^30,(4793238957938726833375561448 : Int)/10^30)
theorem v186_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 1 91 5) 1) 14) v186_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material186 : Material (1 : Basis) (91 : Basis) where
  plus := ![v186_pa,v186_pb,v186_pg]
  minus := ![(Primitive.Addresses.material186 1).one,v186_mb,v186_mg]
  upper := v186_upper
  lower := (Primitive.Addresses.material186 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v186_pa_checked.trans (by decide +kernel)
    · exact v186_pb_checked.trans (by decide +kernel)
    · exact v186_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 1 91 Primitive.Addresses.material186
    · exact v186_mb_checked.trans (by decide +kernel)
    · exact v186_mg_checked.trans (by decide +kernel)
  upper_error := v186_upper_checked
  lower_error := reuse_lower_error 1 91 Primitive.Addresses.material186

def v187_pa : Scalar.QComplex := ((999978958118274793581901317789 : Int)/10^30,(6487165844159242598015581260 : Int)/10^30)
theorem v187_pa_checked : Scalar.distance (sourceCoefficient 1 92 1 0) v187_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v187_pb : Scalar.QComplex := ((2799026874543033068822541 : Int)/10^30,(-431462374323397376474448126 : Int)/10^30)
theorem v187_pb_checked : Scalar.distance (sourceCoefficient 1 92 1 1) v187_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v187_pg : Scalar.QComplex := ((-93083816676473250446637 : Int)/10^30,(-603862862598530820338 : Int)/10^30)
theorem v187_pg_checked : Scalar.distance (sourceCoefficient 1 92 1 2) v187_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v187_mb : Scalar.QComplex := ((2426693235640290902370271 : Int)/10^30,(-431464629104365851143179777 : Int)/10^30)
theorem v187_mb_checked : Scalar.distance (sourceCoefficient 1 92 3 1) v187_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v187_mg : Scalar.QComplex := ((-93084303123567610014505 : Int)/10^30,(-523535496300468915276 : Int)/10^30)
theorem v187_mg_checked : Scalar.distance (sourceCoefficient 1 92 3 2) v187_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v187_upper : Scalar.QComplex := ((999988665026818387020091372116 : Int)/10^30,(4761283217958046646887536213 : Int)/10^30)
theorem v187_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 1 92 5) 1) 14) v187_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material187 : Material (1 : Basis) (92 : Basis) where
  plus := ![v187_pa,v187_pb,v187_pg]
  minus := ![(Primitive.Addresses.material187 1).one,v187_mb,v187_mg]
  upper := v187_upper
  lower := (Primitive.Addresses.material187 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v187_pa_checked.trans (by decide +kernel)
    · exact v187_pb_checked.trans (by decide +kernel)
    · exact v187_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 1 92 Primitive.Addresses.material187
    · exact v187_mb_checked.trans (by decide +kernel)
    · exact v187_mg_checked.trans (by decide +kernel)
  upper_error := v187_upper_checked
  lower_error := reuse_lower_error 1 92 Primitive.Addresses.material187

def v188_pa : Scalar.QComplex := ((999979203428846695145224169961 : Int)/10^30,(6449241025829161479071491639 : Int)/10^30)
theorem v188_pa_checked : Scalar.distance (sourceCoefficient 1 93 1 0) v188_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v188_pb : Scalar.QComplex := ((2782663074260016584641627 : Int)/10^30,(-431462429961151131824136828 : Int)/10^30)
theorem v188_pb_checked : Scalar.distance (sourceCoefficient 1 93 1 1) v188_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v188_pg : Scalar.QComplex := ((-93083834095610978085627 : Int)/10^30,(-600332566549825521435 : Int)/10^30)
theorem v188_pg_checked : Scalar.distance (sourceCoefficient 1 93 1 2) v188_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v188_mb : Scalar.QComplex := ((2410329393437389466716017 : Int)/10^30,(-431464670620876243977236200 : Int)/10^30)
theorem v188_mb_checked : Scalar.distance (sourceCoefficient 1 93 3 1) v188_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v188_mg : Scalar.QComplex := ((-93084317496212360311479 : Int)/10^30,(-520005186534322847694 : Int)/10^30)
theorem v188_mg_checked : Scalar.distance (sourceCoefficient 1 93 3 2) v188_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v188_upper : Scalar.QComplex := ((999988844882229002225854644165 : Int)/10^30,(4723358032728734767636974728 : Int)/10^30)
theorem v188_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 1 93 5) 1) 14) v188_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material188 : Material (1 : Basis) (93 : Basis) where
  plus := ![v188_pa,v188_pb,v188_pg]
  minus := ![(Primitive.Addresses.material188 1).one,v188_mb,v188_mg]
  upper := v188_upper
  lower := (Primitive.Addresses.material188 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v188_pa_checked.trans (by decide +kernel)
    · exact v188_pb_checked.trans (by decide +kernel)
    · exact v188_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 1 93 Primitive.Addresses.material188
    · exact v188_mb_checked.trans (by decide +kernel)
    · exact v188_mg_checked.trans (by decide +kernel)
  upper_error := v188_upper_checked
  lower_error := reuse_lower_error 1 93 Primitive.Addresses.material188

def v189_pa : Scalar.QComplex := ((999979491342106996717149439651 : Int)/10^30,(6404443393532180596165065931 : Int)/10^30)
theorem v189_pa_checked : Scalar.distance (sourceCoefficient 1 94 1 0) v189_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v189_pb : Scalar.QComplex := ((2763333795465694493689274 : Int)/10^30,(-431462494615669584675684255 : Int)/10^30)
theorem v189_pb_checked : Scalar.distance (sourceCoefficient 1 94 1 1) v189_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v189_pg : Scalar.QComplex := ((-93083854470244647220344 : Int)/10^30,(-596162503299298068894 : Int)/10^30)
theorem v189_pg_checked : Scalar.distance (sourceCoefficient 1 94 1 2) v189_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v189_mb : Scalar.QComplex := ((2391000066046303769175369 : Int)/10^30,(-431464718595073581896991064 : Int)/10^30)
theorem v189_mb_checked : Scalar.distance (sourceCoefficient 1 94 3 1) v189_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v189_mg : Scalar.QComplex := ((-93084334272261670510591 : Int)/10^30,(-515835107254109307603 : Int)/10^30)
theorem v189_mg_checked : Scalar.distance (sourceCoefficient 1 94 3 2) v189_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v189_upper : Scalar.QComplex := ((999989055478411155683906577064 : Int)/10^30,(4678559970240396897966332222 : Int)/10^30)
theorem v189_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 1 94 5) 1) 14) v189_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material189 : Material (1 : Basis) (94 : Basis) where
  plus := ![v189_pa,v189_pb,v189_pg]
  minus := ![(Primitive.Addresses.material189 1).one,v189_mb,v189_mg]
  upper := v189_upper
  lower := (Primitive.Addresses.material189 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v189_pa_checked.trans (by decide +kernel)
    · exact v189_pb_checked.trans (by decide +kernel)
    · exact v189_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 1 94 Primitive.Addresses.material189
    · exact v189_mb_checked.trans (by decide +kernel)
    · exact v189_mg_checked.trans (by decide +kernel)
  upper_error := v189_upper_checked
  lower_error := reuse_lower_error 1 94 Primitive.Addresses.material189

def v190_pa : Scalar.QComplex := ((999979773913782876513621845878 : Int)/10^30,(6360170071600547242998734863 : Int)/10^30)
theorem v190_pa_checked : Scalar.distance (sourceCoefficient 1 95 1 0) v190_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v190_pb : Scalar.QComplex := ((2744230749506351494736489 : Int)/10^30,(-431462557379072740926814964 : Int)/10^30)
theorem v190_pb_checked : Scalar.distance (sourceCoefficient 1 95 1 1) v190_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v190_pg : Scalar.QComplex := ((-93083874392270311056729 : Int)/10^30,(-592041246735642778648 : Int)/10^30)
theorem v190_pg_checked : Scalar.distance (sourceCoefficient 1 95 1 2) v190_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v190_mb : Scalar.QComplex := ((2371896973037907668115199 : Int)/10^30,(-431464764873385074803290289 : Int)/10^30)
theorem v190_mb_checked : Scalar.distance (sourceCoefficient 1 95 3 1) v190_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v190_mg : Scalar.QComplex := ((-93084350637821116537118 : Int)/10^30,(-511713835033175293573 : Int)/10^30)
theorem v190_mg_checked : Scalar.distance (sourceCoefficient 1 95 3 2) v190_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v190_upper : Scalar.QComplex := ((999989261637928968554085196851 : Int)/10^30,(4634286226555597985903658083 : Int)/10^30)
theorem v190_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 1 95 5) 1) 14) v190_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material190 : Material (1 : Basis) (95 : Basis) where
  plus := ![v190_pa,v190_pb,v190_pg]
  minus := ![(Primitive.Addresses.material190 1).one,v190_mb,v190_mg]
  upper := v190_upper
  lower := (Primitive.Addresses.material190 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v190_pa_checked.trans (by decide +kernel)
    · exact v190_pb_checked.trans (by decide +kernel)
    · exact v190_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 1 95 Primitive.Addresses.material190
    · exact v190_mb_checked.trans (by decide +kernel)
    · exact v190_mg_checked.trans (by decide +kernel)
  upper_error := v190_upper_checked
  lower_error := reuse_lower_error 1 95 Primitive.Addresses.material190

def v191_pa : Scalar.QComplex := ((999979908930977641998076005284 : Int)/10^30,(6338906403604768693356622209 : Int)/10^30)
theorem v191_pa_checked : Scalar.distance (sourceCoefficient 1 96 1 0) v191_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v191_pb : Scalar.QComplex := ((2735055906622496352129814 : Int)/10^30,(-431462587122310808249238133 : Int)/10^30)
theorem v191_pb_checked : Scalar.distance (sourceCoefficient 1 96 1 1) v191_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v191_pg : Scalar.QComplex := ((-93083883884780551938432 : Int)/10^30,(-590061882603649026179 : Int)/10^30)
theorem v191_pg_checked : Scalar.distance (sourceCoefficient 1 96 1 2) v191_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v191_mb : Scalar.QComplex := ((2362722107903190975817513 : Int)/10^30,(-431464786699135878175916631 : Int)/10^30)
theorem v191_mb_checked : Scalar.distance (sourceCoefficient 1 96 3 1) v191_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v191_mg : Scalar.QComplex := ((-93084358422225724264024 : Int)/10^30,(-509734463446580457765 : Int)/10^30)
theorem v191_mg_checked : Scalar.distance (sourceCoefficient 1 96 3 2) v191_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v191_upper : Scalar.QComplex := ((999989359955760705965254824356 : Int)/10^30,(4613022357202125609071258890 : Int)/10^30)
theorem v191_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 1 96 5) 1) 14) v191_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material191 : Material (1 : Basis) (96 : Basis) where
  plus := ![v191_pa,v191_pb,v191_pg]
  minus := ![(Primitive.Addresses.material191 1).one,v191_mb,v191_mg]
  upper := v191_upper
  lower := (Primitive.Addresses.material191 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v191_pa_checked.trans (by decide +kernel)
    · exact v191_pb_checked.trans (by decide +kernel)
    · exact v191_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 1 96 Primitive.Addresses.material191
    · exact v191_mb_checked.trans (by decide +kernel)
    · exact v191_mg_checked.trans (by decide +kernel)
  upper_error := v191_upper_checked
  lower_error := reuse_lower_error 1 96 Primitive.Addresses.material191

def v192_pa : Scalar.QComplex := ((999980370023161335869767751009 : Int)/10^30,(6265745633309540437196500636 : Int)/10^30)
theorem v192_pa_checked : Scalar.distance (sourceCoefficient 1 97 1 0) v192_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v192_pb : Scalar.QComplex := ((2703488519374732487275960 : Int)/10^30,(-431462687471047297457497771 : Int)/10^30)
theorem v192_pb_checked : Scalar.distance (sourceCoefficient 1 97 1 1) v192_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v192_pg : Scalar.QComplex := ((-93083916170018654684965 : Int)/10^30,(-583251590488858117529 : Int)/10^30)
theorem v192_pg_checked : Scalar.distance (sourceCoefficient 1 97 1 2) v192_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v192_mb : Scalar.QComplex := ((2331154645812968033305798 : Int)/10^30,(-431464859806601550487284791 : Int)/10^30)
theorem v192_mb_checked : Scalar.distance (sourceCoefficient 1 97 3 1) v192_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v192_mg : Scalar.QComplex := ((-93084384830476434847062 : Int)/10^30,(-502924146006866139653 : Int)/10^30)
theorem v192_mg_checked : Scalar.distance (sourceCoefficient 1 97 3 2) v192_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v192_upper : Scalar.QComplex := ((999989694778405220864113091589 : Int)/10^30,(4539860900067991540398895181 : Int)/10^30)
theorem v192_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 1 97 5) 1) 14) v192_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material192 : Material (1 : Basis) (97 : Basis) where
  plus := ![v192_pa,v192_pb,v192_pg]
  minus := ![(Primitive.Addresses.material192 1).one,v192_mb,v192_mg]
  upper := v192_upper
  lower := (Primitive.Addresses.material192 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v192_pa_checked.trans (by decide +kernel)
    · exact v192_pb_checked.trans (by decide +kernel)
    · exact v192_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 1 97 Primitive.Addresses.material192
    · exact v192_mb_checked.trans (by decide +kernel)
    · exact v192_mg_checked.trans (by decide +kernel)
  upper_error := v192_upper_checked
  lower_error := reuse_lower_error 1 97 Primitive.Addresses.material192

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
