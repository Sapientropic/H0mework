import H0mework.Versions.C62.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalSourcePropagationNativeFourierDictionary
import H0mework.Versions.C62.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalSourcePropagationNativeGaugeLiteral

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 8192
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
noncomputable section
namespace LowEnergy.SourcePropagationNativeActionHessian
open PreparationVacuumOriginalGreenFeedback
open SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair
open scoped BigOperators

def nativeRecordCoefficientAtoms : List SourceCoefficient := [
  ⟨⟨1,0⟩,⟨0,0⟩⟩,⟨⟨-1,0⟩,⟨0,0⟩⟩,⟨⟨0,0⟩,⟨0,(-3/25:ℚ)⟩⟩,⟨⟨0,0⟩,⟨0,(3/25:ℚ)⟩⟩,⟨⟨0,1⟩,⟨0,0⟩⟩,
  ⟨⟨0,-1⟩,⟨0,0⟩⟩,⟨⟨(-3/5:ℚ),0⟩,⟨0,0⟩⟩,⟨⟨0,0⟩,⟨0,(1/5:ℚ)⟩⟩,⟨⟨0,0⟩,⟨0,(1/10:ℚ)⟩⟩,⟨⟨0,0⟩,⟨0,(-1/10:ℚ)⟩⟩,
  ⟨⟨(3/5:ℚ),0⟩,⟨0,0⟩⟩,⟨⟨0,0⟩,⟨0,(-1/5:ℚ)⟩⟩,⟨⟨0,0⟩,⟨0,(-1/3:ℚ)⟩⟩,⟨⟨(5/6:ℚ),0⟩,⟨0,0⟩⟩,⟨⟨(-5/6:ℚ),0⟩,⟨0,0⟩⟩,
  ⟨⟨(-5/3:ℚ),0⟩,⟨0,0⟩⟩,⟨⟨0,0⟩,⟨0,(18/125:ℚ)⟩⟩,⟨⟨0,0⟩,⟨0,(-9/125:ℚ)⟩⟩,⟨⟨(18/25:ℚ),0⟩,⟨0,0⟩⟩,⟨⟨(-18/25:ℚ),0⟩,⟨0,0⟩⟩,
  ⟨⟨(-9/25:ℚ),0⟩,⟨0,0⟩⟩,⟨⟨(9/25:ℚ),0⟩,⟨0,0⟩⟩,⟨⟨0,0⟩,⟨0,(9/125:ℚ)⟩⟩,⟨⟨0,0⟩,⟨0,(27/125:ℚ)⟩⟩,⟨⟨(5/3:ℚ),0⟩,⟨0,0⟩⟩,
  ⟨⟨0,(3/5:ℚ)⟩,⟨0,0⟩⟩,⟨⟨0,(-3/5:ℚ)⟩,⟨0,0⟩⟩,⟨⟨0,(-6/5:ℚ)⟩,⟨0,0⟩⟩,⟨⟨0,(6/5:ℚ)⟩,⟨0,0⟩⟩,⟨⟨0,0⟩,⟨0,(4/5:ℚ)⟩⟩,
  ⟨⟨0,0⟩,⟨0,(-4/5:ℚ)⟩⟩,⟨⟨0,0⟩,⟨0,(-2/5:ℚ)⟩⟩,⟨⟨0,0⟩,⟨0,(2/5:ℚ)⟩⟩,⟨⟨2,0⟩,⟨0,0⟩⟩,⟨⟨-2,0⟩,⟨0,0⟩⟩,
  ⟨⟨0,0⟩,⟨0,(3/50:ℚ)⟩⟩,⟨⟨0,0⟩,⟨0,(3/100:ℚ)⟩⟩,⟨⟨0,0⟩,⟨0,(-5/36:ℚ)⟩⟩,⟨⟨0,0⟩,⟨0,(-5/72:ℚ)⟩⟩,⟨⟨0,0⟩,⟨0,(-5/18:ℚ)⟩⟩,
  ⟨⟨0,0⟩,⟨0,(-5/9:ℚ)⟩⟩,⟨⟨0,0⟩,⟨0,(5/18:ℚ)⟩⟩,⟨⟨0,0⟩,⟨(-18/125:ℚ),0⟩⟩,⟨⟨0,0⟩,⟨0,(6/25:ℚ)⟩⟩,⟨⟨0,0⟩,⟨(18/125:ℚ),0⟩⟩,
  ⟨⟨0,0⟩,⟨0,(-219/1250:ℚ)⟩⟩,⟨⟨0,0⟩,⟨0,(-6/25:ℚ)⟩⟩,⟨⟨(-16/5:ℚ),0⟩,⟨0,0⟩⟩,⟨⟨0,4⟩,⟨0,0⟩⟩,⟨⟨0,2⟩,⟨0,0⟩⟩,
  ⟨⟨0,-2⟩,⟨0,0⟩⟩,⟨⟨(-6/5:ℚ),0⟩,⟨0,0⟩⟩,⟨⟨(6/5:ℚ),0⟩,⟨0,0⟩⟩,⟨⟨0,(-3/5:ℚ)⟩,⟨0,0⟩⟩,⟨⟨0,(3/5:ℚ)⟩,⟨0,0⟩⟩,
  ⟨⟨0,1⟩,⟨0,0⟩⟩,⟨⟨0,-1⟩,⟨0,0⟩⟩,⟨⟨(16/5:ℚ),0⟩,⟨0,0⟩⟩,⟨⟨0,-4⟩,⟨0,0⟩⟩,⟨⟨0,0⟩,⟨0,(-18/125:ℚ)⟩⟩,
  ⟨⟨0,0⟩,⟨0,(18/125:ℚ)⟩⟩,⟨⟨0,0⟩,⟨(18/125:ℚ),0⟩⟩,⟨⟨0,0⟩,⟨(-18/125:ℚ),0⟩⟩,⟨⟨(2/5:ℚ),0⟩,⟨0,0⟩⟩,⟨⟨(-2/5:ℚ),0⟩,⟨0,0⟩⟩,
  ⟨⟨0,(-1/5:ℚ)⟩,⟨0,0⟩⟩,⟨⟨0,(1/5:ℚ)⟩,⟨0,0⟩⟩,⟨⟨0,0⟩,⟨0,(48/125:ℚ)⟩⟩,⟨⟨0,0⟩,⟨(24/25:ℚ),0⟩⟩,⟨⟨0,0⟩,⟨(12/25:ℚ),0⟩⟩,
  ⟨⟨0,0⟩,⟨(-12/25:ℚ),0⟩⟩,⟨⟨0,0⟩,⟨0,(6/125:ℚ)⟩⟩,⟨⟨0,0⟩,⟨0,(-6/125:ℚ)⟩⟩,⟨⟨0,0⟩,⟨(6/125:ℚ),0⟩⟩,⟨⟨0,0⟩,⟨(-6/125:ℚ),0⟩⟩,
  ⟨⟨0,0⟩,⟨(6/25:ℚ),0⟩⟩,⟨⟨0,0⟩,⟨(-6/25:ℚ),0⟩⟩,⟨⟨0,0⟩,⟨0,(-48/125:ℚ)⟩⟩,⟨⟨0,0⟩,⟨(-24/25:ℚ),0⟩⟩,⟨⟨0,0⟩,⟨0,(24/125:ℚ)⟩⟩,
  ⟨⟨0,0⟩,⟨0,(-24/125:ℚ)⟩⟩,⟨⟨0,0⟩,⟨0,(-3/25:ℚ)⟩⟩,⟨⟨0,0⟩,⟨0,(3/25:ℚ)⟩⟩,⟨⟨0,(-1/2:ℚ)⟩,⟨0,0⟩⟩,⟨⟨0,(1/2:ℚ)⟩,⟨0,0⟩⟩,
  ⟨⟨(-1/2:ℚ),0⟩,⟨0,0⟩⟩,⟨⟨(1/2:ℚ),0⟩,⟨0,0⟩⟩,⟨⟨0,0⟩,⟨(-3/25:ℚ),0⟩⟩,⟨⟨0,0⟩,⟨(3/25:ℚ),0⟩⟩,⟨⟨0,0⟩,⟨0,(3/50:ℚ)⟩⟩,
  ⟨⟨0,0⟩,⟨0,(-3/50:ℚ)⟩⟩,⟨⟨0,0⟩,⟨(-36/125:ℚ),0⟩⟩,⟨⟨0,0⟩,⟨(36/125:ℚ),0⟩⟩,⟨⟨0,0⟩,⟨(-27/125:ℚ),0⟩⟩,⟨⟨0,0⟩,⟨(27/125:ℚ),0⟩⟩]

def nativeRecordRealAtoms : List ℝ := [
  1,-1,-lapse,lapse,spinScale,
  -spinScale,-3/5,(25*lapse/3)/5,(25*lapse/3)/10,-(25*lapse/3)/10,
  3/5,-(25*lapse/3)/5,-(25*lapse/3)/3,5/6,-5/6,
  -5/3,18*(25*lapse/3)/125,-9*(25*lapse/3)/125,18/25,-18/25,
  -9/25,9/25,9*(25*lapse/3)/125,27*(25*lapse/3)/125,5/3,
  3*spinScale/5,-3*spinScale/5,-6*spinScale/5,6*spinScale/5,4*(25*lapse/3)/5,
  -4*(25*lapse/3)/5,-2*(25*lapse/3)/5,2*(25*lapse/3)/5,2,-2,
  3*(25*lapse/3)/50,3*(25*lapse/3)/100,-5*(25*lapse/3)/36,-5*(25*lapse/3)/72,(-125/54:ℝ)*lapse,
  (-125/27:ℝ)*lapse,(125/54:ℝ)*lapse,-lapse*gaugeScale,2*lapse,lapse*gaugeScale,
  (-73/50:ℝ)*lapse,-2*lapse,(-16/5:ℝ),4*spinScale,2*spinScale,
  -2*spinScale,(-6/5:ℝ),(6/5:ℝ),(-3/5:ℝ)*spinScale,(3/5:ℝ)*spinScale,
  1*spinScale,-1*spinScale,(16/5:ℝ),-4*spinScale,(-18/125:ℝ)*((25/3:ℝ)*lapse),
  (18/125:ℝ)*((25/3:ℝ)*lapse),(18/125:ℝ)*((25/6:ℝ)*lapse*spinScale),(-18/125:ℝ)*((25/6:ℝ)*lapse*spinScale),(2/5:ℝ),(-2/5:ℝ),
  (-1/5:ℝ)*spinScale,(1/5:ℝ)*spinScale,(48/125:ℝ)*((25/3:ℝ)*lapse),(24/25:ℝ)*((25/6:ℝ)*lapse*spinScale),(12/25:ℝ)*((25/6:ℝ)*lapse*spinScale),
  (-12/25:ℝ)*((25/6:ℝ)*lapse*spinScale),(6/125:ℝ)*((25/3:ℝ)*lapse),(-6/125:ℝ)*((25/3:ℝ)*lapse),(6/125:ℝ)*((25/6:ℝ)*lapse*spinScale),(-6/125:ℝ)*((25/6:ℝ)*lapse*spinScale),
  (6/25:ℝ)*((25/6:ℝ)*lapse*spinScale),(-6/25:ℝ)*((25/6:ℝ)*lapse*spinScale),(-48/125:ℝ)*((25/3:ℝ)*lapse),(-24/25:ℝ)*((25/6:ℝ)*lapse*spinScale),(24/125:ℝ)*((25/3:ℝ)*lapse),
  (-24/125:ℝ)*((25/3:ℝ)*lapse),(-3/25:ℝ)*((25/3:ℝ)*lapse),(3/25:ℝ)*((25/3:ℝ)*lapse),(-1/2:ℝ)*spinScale,(1/2:ℝ)*spinScale,
  (-1/2:ℝ),(1/2:ℝ),(-3/25:ℝ)*((25/6:ℝ)*lapse*spinScale),(3/25:ℝ)*((25/6:ℝ)*lapse*spinScale),(3/50:ℝ)*((25/3:ℝ)*lapse),
  (-3/50:ℝ)*((25/3:ℝ)*lapse),(-36/125:ℝ)*((25/6:ℝ)*lapse*spinScale),(36/125:ℝ)*((25/6:ℝ)*lapse*spinScale),(-27/125:ℝ)*((25/6:ℝ)*lapse*spinScale),(27/125:ℝ)*((25/6:ℝ)*lapse*spinScale)]

def nativeRecordJet (code : ℕ) : NativeJetIndex :=
  (if code/289=0 then none else some ⟨(code/289-1)%4,Nat.mod_lt _ (by decide)⟩,
    ⟨code%289,Nat.mod_lt _ (by decide)⟩)

def decodeNativeRealRecords (codes : List ℕ) : List (NativeJetIndex × NativeJetIndex × ℝ) :=
  codes.map fun code => let pair := code/nativeRecordRealAtoms.length
    (nativeRecordJet (pair/1445),nativeRecordJet (pair%1445),
      nativeRecordRealAtoms[code%nativeRecordRealAtoms.length]?.getD 0)

def decodeNativeSourceRecords (codes : List ℕ) : List (NativeJetIndex × NativeJetIndex × SourceCoefficient) :=
  codes.map fun code => let pair := code/nativeRecordCoefficientAtoms.length
    (nativeRecordJet (pair/1445),nativeRecordJet (pair%1445),
      nativeRecordCoefficientAtoms[code%nativeRecordCoefficientAtoms.length]?.getD 0)

def nativeGravityRecordCodes : List ℕ := [
  7830565,7831040,7831515,7843865,7844530,7845195,7967746,7981615,7982091,8105401,8118321,8119270,8243056,8255500,8255976,8392016,
  8392490,8517417,8517892,8528910,8529575,8530243,8654598,8666091,8667613,8792253,8803936,8804983,8940545,8941496,9077441,9079913,
  9204267,9214620,9215950,9217283,9341448,9353131,9354653,9489551,9490025,9626636,9629583,9764481,9766953,9900995,9901660,9904323,
  16623385,16623861,16625099,16625575,16760091,16761040,16761805,16762754,16897270,16897746,16898984,16899460,17034925,17035401,17038634,17039110,
  17171631,17172580,17175340,17176289,17308810,17309286,17312519,17312995,17446657,17447322,17448370,17449035,17583838,17585074,17721683,17722444,
  17858768,17859433,17861905,17862570,17995947,17998609,18133792,18135979,18271924,18408247,18408630,18409960,18545428,18546664,18685459,18820358,
  18822165,18823495,18957537,18960199,19096144,19233514,19369555,19370220,19509679,19647049,19783090,19783755,57120460,95969286,57258305,96107131,
  57396150,96244976,57533995,96382821,57671840,96520666,57809685,96658511,57944205,135641856,58082050,135779701,58219895,135917546,58357740,136055391,
  58495585,136193236,58633430,136331081,58767950,175314426,58905795,175452271,59043640,175590116,59181485,175727961,59319330,175865806,59457175,176003651,
  138112425,176961251,138250270,177099096,138388115,177236941,138525960,177374786,138663805,177512631,138801650,177650476,176137695,98440046,176275540,98577891,
  176413385,98715736,176551230,98853581,176689075,98991426,176826920,99129271,97616490,136465316,97754335,136603161,97892180,136741006,98030025,136878851,
  98167870,137016696,98305715,137154541,19920645,19922356,20058015,20059726,20195385,20197096,20332185,20333896,20469555,20471266,20606925,20608636,
  20744865,20746576,20882235,20883946,21019605,21021316,21156405,21158116,21293775,21295486,21431145,21432856,21569085,21570796,21706455,21708166,
  21843825,21845536,21980625,21982336,22117995,22119706,22255365,22257076,22395015,22532385,22669755,22806555,22943925,23081295,23219235,23356605,
  23493975,23630775,23768145,23905515,24043455,24180825,24318195,24454995,24592365,24729735]
def nativeGravitySourceRecords := decodeNativeSourceRecords nativeGravityRecordCodes

theorem literalGravityTerms_decoded : literalGravityTerms = decodeNativeRealRecords nativeGravityRecordCodes := by rfl

def nativeGaugeRecordCodes : List ℕ := [
  7830571,7831046,7831521,7845392,7846437,7848148,7848244,7967755,7987704,7987798,7988272,8105410,8123838,8123934,8125646,8243065,
  8260546,8261777,8379582,8399533,8399629,8400105,8516956,8517432,8517907,8531778,8532824,8534535,8534631,8654332,8654618,8668958,
  8670193,8791702,8792273,8806806,8806900,8808608,8929062,8947494,8947588,8949309,9066442,9080783,9082018,9203806,9204282,9218154,
  9219198,9220910,9221006,9341182,9341468,9357046,9357140,9357613,9478542,9496034,9497260,9615922,9630456,9630550,9632258,9753292,
  9768871,9768965,9769438,9890656,9904529,9905574,9907286,9907380,1260105,1260201,1261912,1398521,1398615,1399093,1534561,1535605,
  1536651,1671740,1672975,1673830,1808921,1809966,1811390,1946100,1947336,1948571,2083186,2084420,2220460,2221696,2886034,2904653,
  3023215,3024926,3025022,3041832,3043541,3043635,3160777,3162012,3179390,3180625,3297956,3299382,3316571,3317995,3435516,3436371,
  3454131,3454986,3572697,3573741,3591310,3592356,3710827,3729440,3848101,3866716,4534951,4535047,4550812,4553566,4553660,4687993,
  4809407,4825551,4828020,4946586,4962730,4965201,5083767,5100290,5102380,5220946,5237471,5239561,5358032,5376645,5495306,5513921,
  6199725,6199821,6335860,6335956,6472946,6474181,6610316,6611360,6747305,6748541,6884675,6885720,7021761,7022806,7159035,7160080,
  42579318,80604494,42716688,80741864,42854058,80879234,42991428,81016604,43128798,81153974,43266168,81291344,43403538,43403600,81428714,81428776,
  43540780,43540908,81565956,81566084,43678278,81703454,43815648,81840824,43953018,81978194,44090355,82115531,44227758,120278109,44365128,120415479,
  44502498,120552849,44639868,120690219,44777238,120827589,44914608,120964959,45051978,45052040,121102329,121102391,45189220,45189348,121239571,121239699,
  45326718,121377069,45464088,121514439,45601458,121651809,45738795,121789146,45876198,159951724,46013568,160089094,46150938,160226464,46288308,160363834,
  46425678,160501204,46563048,160638574,46700418,46700480,160775944,160776006,46837660,46837788,160913186,160913314,46975158,161050684,47112528,161188054,
  47249898,161325424,47387235,161462761,125215448,163240624,125352818,163377994,125490188,163515364,125627558,163652734,125764928,163790104,125902298,163927474,
  126039668,126039730,164064844,164064906,126176910,126177038,164202086,164202214,126314408,164339584,126451778,164476954,126589148,164614324,126726485,164751661,
  161594463,85544114,161731833,85681484,161869203,85818854,162006573,85956224,162143943,86093594,162281313,86230964,162418683,162418745,86368334,86368396,
  162555925,162556053,86505576,86505704,162693423,86643074,162830793,86780444,162968163,86917814,163105500,87055151,83897953,121923129,84035323,122060499,
  84172693,122197869,84310063,122335239,84447433,122472609,84584803,122609979,84722173,84722235,122747349,122747411,84859415,84859543,122884591,122884719,
  84996913,123022089,85134283,123159459,85271653,123296829,85408990,123434166,29809325,29946695,30084065,30221435,30358805,30496175,30633545,30633640,
  30770915,30908285,31045655,31183025,31320396,31457765,31595135,31732505,31869875,32007245,32144615,32281985,32282080,32419355,32556725,32694095,
  32831465,32968836,33106205,33243575,33380945,33518315,33655685,33793055,33930425,33930520,34067795,34205165,34342535,34479905,34617276,34754647,
  34892017,35029387,35166757,35304127,35441497,35578867,35578962,35716237,35853607,35990977,36128347,36265718,36403087,36540457,36677827,36815197,
  36952567,37089937,37227307,37227402,37364677,37502047,37639417,37776787,37914158,38051527,38188897,38326267,38463637,38601007,38738377,38875747,
  38875842,39013117,39150487,39287857,39425227,39562598]
def nativeGaugeSourceRecords := decodeNativeSourceRecords nativeGaugeRecordCodes

theorem literalGaugeTerms_decoded : literalGaugeTerms = decodeNativeRealRecords nativeGaugeRecordCodes := by rfl

def nativeScalarRecordCodes : List ℕ := [
  1511109,1537520,1648479,1674890,1785849,1812260,1923219,1949630,2060589,2060685,2060971,2061064,2087000,2087286,2087379,2197959,
  2198246,2198339,2224275,2224561,2224654,2335329,2361645,2472699,2499015,2610069,2610166,2636101,2636385,2636481,2747439,2773374,
  2773661,2773755,3159513,3157652,3212278,3296883,3294834,3349648,3434253,3432012,3487018,3571623,3569194,3624388,3708993,3709128,
  3709372,3709468,3761758,3762002,3762098,3846363,3846647,3846743,3899033,3899277,3899373,3983733,4036403,4121103,4173773,4258473,
  4258567,4310817,4311143,4311197,4395843,4448093,4448377,4448513,4807953,4804859,4887033,4945323,4942229,5024403,5082693,5079217,
  5161773,5220063,5216587,5299143,5357433,5357568,5357812,5357908,5436513,5436757,5436853,5494803,5495087,5495183,5573788,5574032,
  5574128,5632173,5711158,5769543,5848528,5906913,5907007,5985572,5985898,5985952,6044283,6122848,6123132,6123268,6456393,6452062,
  6561788,6593763,6589244,6699158,6731133,6726804,6836528,6868503,6863982,6973898,7005873,7006008,7006252,7006348,7111268,7111512,
  7111608,7143243,7143527,7143623,7248543,7248787,7248883,7280613,7385913,7417983,7523283,7555353,7555447,7660327,7660653,7660707,
  7692723,7797603,7797887,7798023,45,55239,82597,109959,137415,192417,219967,247137,274785,329599,356959,384697,
  412155,466777,494329,521879,549526,549808,549906,686896,824266,961636,961728,1099006,39699969,39837339,39974709,40112079,
  40249449,40249736,40249829,40386819,40524189,40661559,40661656,40798929,79399863,79537233,79674603,79811973,79949343,79949627,79949723,80086713,
  80224083,80361453,80361547,80498823,119099793,119237163,119374533,119511903,119649273,119649557,119649653,119786643,119924013,120061383,120061477,120198753,
  158799723,158937093,159074463,159211833,159349203,159349487,159349583,159486573,159623943,159761313,159761407,159898683]
def nativeScalarSourceRecords := decodeNativeSourceRecords nativeScalarRecordCodes

theorem literalScalarTerms_decoded : literalScalarTerms = decodeNativeRealRecords nativeScalarRecordCodes := by rfl

def nativeDiracRecordCodes : List ℕ := [
  7830612,7831087,7831562,7826813,7827858,7829569,7829665,7837075,7837740,7838405,7831756,7831947,7832326,7832517,7834038,7834229,
  7834608,7834799,7887715,7888096,7888285,7888666,7914030,7914410,7914600,7914980,7942721,7942911,7943291,7943481,7967802,7962958,
  7973779,7968944,7969325,7969515,7969894,7971226,7971607,7971797,7972176,7997536,7997915,7998106,7998485,8105457,8100138,8111149,
  8107360,8107740,8107929,8108309,8109641,8110021,8110212,8110592,8133671,8134051,8134241,8134621,8243112,8237975,8238069,8248519,
  8243590,8243780,8244159,8244349,8245872,8246062,8246441,8246631,8272180,8272370,8272750,8272940,8380773,8381154,8381344,8381723,
  8383055,8383436,8383626,8384005,8436911,8437100,8437480,8437671,8517482,8517957,8514253,8515964,8516060,8524135,8524800,8518151,
  8518342,8518721,8518912,8520433,8520624,8521003,8521194,8546730,8546921,8547301,8547490,8600425,8600805,8600995,8601375,8629116,
  8629306,8629686,8629876,8654672,8650398,8660839,8656574,8656764,8657144,8657334,8658848,8659038,8659418,8659608,8710246,8710626,
  8710816,8711196,8792327,8788235,8788329,8798209,8792614,8792994,8793184,8793564,8794889,8795269,8795459,8795839,8848755,8848945,
  8849325,8849515,8931014,8931394,8931583,8931963,8933295,8933675,8933866,8934246,9013466,9013655,9014035,9014226,9063458,9073139,
  9068400,9068590,9068970,9069160,9070674,9070864,9071244,9071434,9150666,9151045,9151236,9151615,9204332,9199583,9202339,9202435,
  9209845,9211175,9204526,9204717,9205096,9205287,9206808,9206999,9207378,9207569,9233105,9233296,9233676,9233865,9260485,9260866,
  9261055,9261436,9315491,9315681,9316061,9316251,9341522,9338475,9338569,9347879,9342855,9343234,9343425,9343804,9345129,9345508,
  9345699,9346078,9425310,9425500,9425880,9426070,9479069,9479259,9479638,9479828,9481351,9481541,9481920,9482110,9590021,9590210,
  9590590,9590781,9613698,9622809,9616265,9616645,9616835,9617215,9618538,9618918,9619108,9619488,9727221,9727600,9727791,9728170,
  9750878,9760179,9754679,9755060,9755249,9755630,9756953,9757334,9757523,9757904,9863356,9863736,9863926,9864306,9885958,9887003,
  9896220,9896885,9890901,9891092,9891471,9891662,9893183,9893374,9893753,9893944,9919480,9919671,9920051,9920240,9946860,9947241,
  9947430,9947811,9973175,9973555,9973745,9974125,1243606,1243986,1244175,1244555,1245831,1246211,1246400,1246780,1379740,1380121,
  1380311,1380690,1381966,1382345,1382535,1382916,1518631,1519200,1520856,1521425,1654766,1655335,1656990,1657561,1792895,1793466,
  1795120,1795691,1929030,1929601,1931256,1931825,2066401,2066970,2068625,2069196,2203485,2204056,2205711,2206280,2752585,2752776,
  2753156,2753345,2754811,2755000,2755380,2755571,2891020,2891210,2891590,2891780,2893306,2893496,2893876,2894066,3027155,3027346,
  3027725,3027916,3029442,3029631,3030012,3030201,3165665,3166235,3167951,3168521,3301800,3302370,3304087,3304657,3440501,3441071,
  3442787,3443357,3576636,3577206,3578921,3579491,3713435,3714005,3715722,3716292,3851091,3851661,3853376,3853946,4399810,4400191,
  4400380,4400761,4402097,4402476,4402667,4403046,4537180,4537371,4537750,4537941,4539467,4539656,4540037,4540226,4675596,4675786,
  4676166,4676356,4677882,4678072,4678452,4678642,4811825,4812395,4814112,4814682,4950241,4950811,4952527,4953097,5086660,5087230,
  5088947,5089517,5225076,5225646,5227362,5227932,5361876,5362446,5364162,5364732,5499531,5500101,5501817,5502387,6048251,6048631,
  6048821,6049201,6050537,6050917,6051107,6051487,6185525,6185906,6186095,6186476,6187811,6188192,6188381,6188762,6321661,6322041,
  6322231,6322611,6323946,6324326,6324516,6324896,6460551,6461121,6462837,6463407,6596686,6597256,6598971,6599541,6734816,6735386,
  6737102,6737672,6870951,6871521,6873236,6873806,7008321,7008891,7010606,7011176,7145406,7145976,7147691,7148261,7694506,7694696,
  7695076,7695266,7696791,7696981,7697361,7697551,16618433,16618814,16619003,16619384,16620715,16621096,16621285,16621666,16754568,16754948,
  16755138,16755518,16756851,16757231,16757421,16757801,16893079,16893269,16893649,16893839,16895361,16895551,16895931,16896121,17029118,17029499,
  17029689,17030068,17031401,17031780,17031970,17032351,17167534,17167914,17168103,17168483,17169816,17170196,17170385,17170765,17303764,17303954,
  17304333,17304523,17306045,17306235,17306616,17306806,17442182,17442373,17442753,17442942,17444464,17444655,17445035,17445224,17578317,17578507,
  17578888,17579078,17580599,17580789,17581170,17581360,17716638,17717018,17717207,17717587,17718919,17719299,17719490,17719870,17852867,17853058,
  17853437,17853628,17855150,17855339,17855720,17855909,17991283,17991473,17991853,17992043,17993564,17993754,17994134,17994324,18127323,18127703,
  18127893,18128273,18129605,18129985,18130175,18130555,18264693,18264883,18265262,18265452,18266975,18267165,18267544,18267734,18403107,18403298,
  18403678,18403867,18405389,18405580,18405960,18406149,18539148,18539527,18539717,18540098,18541430,18541809,18541999,18542380,18677657,18677847,
  18678227,18678417,18679940,18680130,18680510,18680700,18813792,18813983,18814362,18814553,18816075,18816264,18816645,18816834,18952112,18952493,
  18952682,18953063,18954395,18954774,18954965,18955344,19089387,19089767,19089958,19090338,19091670,19092050,19092239,19092619,19225522,19225903,
  19226093,19226472,19227804,19228185,19228375,19228754,19364032,19364223,19364603,19364792,19366314,19366505,19366885,19367074,19500072,19500452,
  19500642,19501022,19502354,19502734,19502924,19503304,19638488,19638867,19639058,19639437,19640769,19641150,19641339,19641720,19774717,19774908,
  19775287,19775478,19777000,19777189,19777570,19777759,10030951,11679392,10168292,10168482,11816731,11816921,10305693,11954134,10442842,10443032,
  12091281,12091471,10580431,12228872,10717803,12366244,10854031,12502472,10991372,10991562,12639811,12640001,11128773,12777214,11265922,11266112,
  12914361,12914551,11403511,13051952,11540883,13189324,13351776,13379596,13405912,13434221,14997936,15025756,15054351,15080381,13489146,13516966,
  13543282,13571591,15135306,15163126,15191721,15217751,13626516,13654336,13680652,13708961,15272676,15300496,15329091,15355121,13763886,13791136,
  13817451,13846332,15410046,15437296,15465892,15492492,13901256,13928506,13954821,13983702,15547416,15574666,15603262,15629862,14038626,14065876,
  14092191,14121072,15684786,15712036,15740632,15767232,14174855,14202676,14228992,14257301,15821015,15848836,15877431,15903461,14312225,14340046,
  14366362,14394671,15958385,15986206,16014801,16040831,14449595,14477416,14503732,14532041,16095755,16123576,16152171,16178201,14586965,14614216,
  14640531,14669412,16233125,16260376,16288972,16315572,14724335,14751586,14777901,14806782,16370495,16397746,16426342,16452942,14861705,14888956,
  14915271,14944152,16507865,16535116,16563712,16590312]
def nativeDiracSourceRecords := decodeNativeSourceRecords nativeDiracRecordCodes

def literalDiracTerms := decodeNativeRealRecords nativeDiracRecordCodes

def literalDiracQuadratic (jet : NativeFirstJet) : ℝ :=
  (literalDiracTerms.map fun term => term.2.2 * nativeJetCoefficient jet term.1 * nativeJetCoefficient jet term.2.1).sum

def literalDiracHessian := nativeLiteralHessian literalDiracTerms

theorem literalDiracTerms_decoded : literalDiracTerms = decodeNativeRealRecords nativeDiracRecordCodes := by rfl

theorem nativeRecordAtom_count : nativeRecordCoefficientAtoms.length = 95 ∧ nativeRecordRealAtoms.length = 95 := by decide

private theorem source_rootTwo : Real.sqrt 2 = spinScale := rfl

private theorem source_rootFifteen : Real.sqrt 15 = (25/6:ℝ)*lapse*spinScale := by
  have square : ((25/6:ℝ)*lapse*spinScale)^2 = 15 := by
    rw [mul_pow, mul_pow, lapse_sq, spinScale_sq]
    norm_num
  have positive : 0 < (25/6:ℝ)*lapse*spinScale :=
    mul_pos (mul_pos (by norm_num) lapse_pos) spinScale_pos
  have rootSquare : (Real.sqrt 15)^2 = 15 := Real.sq_sqrt (by norm_num)
  nlinarith [Real.sqrt_nonneg (15:ℝ)]

attribute [local irreducible] spinScale lapse gaugeScale

private theorem nativeAtomCalc0 : (coefficientValue (⟨⟨1,0⟩,⟨0,0⟩⟩:SourceCoefficient)).re = (1:ℝ) := by
  norm_num [coefficientValue, rootTwo, rootFifteen, source_rootFifteen, source_rootTwo, gaugeScale]
  <;> ring_nf! <;> norm_num [spinScale_sq] <;> ring

private theorem nativeAtomCalc1 : (coefficientValue (⟨⟨-1,0⟩,⟨0,0⟩⟩:SourceCoefficient)).re = (-1:ℝ) := by
  norm_num [coefficientValue, rootTwo, rootFifteen, source_rootFifteen, source_rootTwo, gaugeScale]
  <;> ring_nf! <;> norm_num [spinScale_sq] <;> ring

private theorem nativeAtomCalc2 : (coefficientValue (⟨⟨0,0⟩,⟨0,(-3/25:ℚ)⟩⟩:SourceCoefficient)).re = (-lapse:ℝ) := by
  norm_num [coefficientValue, rootTwo, rootFifteen, source_rootFifteen, source_rootTwo, gaugeScale]
  <;> ring_nf! <;> norm_num [spinScale_sq] <;> ring

private theorem nativeAtomCalc3 : (coefficientValue (⟨⟨0,0⟩,⟨0,(3/25:ℚ)⟩⟩:SourceCoefficient)).re = (lapse:ℝ) := by
  norm_num [coefficientValue, rootTwo, rootFifteen, source_rootFifteen, source_rootTwo, gaugeScale]
  <;> ring_nf! <;> norm_num [spinScale_sq] <;> ring

private theorem nativeAtomCalc4 : (coefficientValue (⟨⟨0,1⟩,⟨0,0⟩⟩:SourceCoefficient)).re = (spinScale:ℝ) := by
  norm_num [coefficientValue, rootTwo, rootFifteen, source_rootFifteen, source_rootTwo, gaugeScale]
  <;> ring_nf! <;> norm_num [spinScale_sq] <;> ring

private theorem nativeAtomCalc5 : (coefficientValue (⟨⟨0,-1⟩,⟨0,0⟩⟩:SourceCoefficient)).re = (-spinScale:ℝ) := by
  norm_num [coefficientValue, rootTwo, rootFifteen, source_rootFifteen, source_rootTwo, gaugeScale]
  <;> ring_nf! <;> norm_num [spinScale_sq] <;> ring

private theorem nativeAtomCalc6 : (coefficientValue (⟨⟨(-3/5:ℚ),0⟩,⟨0,0⟩⟩:SourceCoefficient)).re = (-3/5:ℝ) := by
  norm_num [coefficientValue, rootTwo, rootFifteen, source_rootFifteen, source_rootTwo, gaugeScale]
  <;> ring_nf! <;> norm_num [spinScale_sq] <;> ring

private theorem nativeAtomCalc7 : (coefficientValue (⟨⟨0,0⟩,⟨0,(1/5:ℚ)⟩⟩:SourceCoefficient)).re = ((25*lapse/3)/5:ℝ) := by
  norm_num [coefficientValue, rootTwo, rootFifteen, source_rootFifteen, source_rootTwo, gaugeScale]
  <;> ring_nf! <;> norm_num [spinScale_sq] <;> ring

private theorem nativeAtomCalc8 : (coefficientValue (⟨⟨0,0⟩,⟨0,(1/10:ℚ)⟩⟩:SourceCoefficient)).re = ((25*lapse/3)/10:ℝ) := by
  norm_num [coefficientValue, rootTwo, rootFifteen, source_rootFifteen, source_rootTwo, gaugeScale]
  <;> ring_nf! <;> norm_num [spinScale_sq] <;> ring

private theorem nativeAtomCalc9 : (coefficientValue (⟨⟨0,0⟩,⟨0,(-1/10:ℚ)⟩⟩:SourceCoefficient)).re = (-(25*lapse/3)/10:ℝ) := by
  norm_num [coefficientValue, rootTwo, rootFifteen, source_rootFifteen, source_rootTwo, gaugeScale]
  <;> ring_nf! <;> norm_num [spinScale_sq] <;> ring

private theorem nativeAtomCalc10 : (coefficientValue (⟨⟨(3/5:ℚ),0⟩,⟨0,0⟩⟩:SourceCoefficient)).re = (3/5:ℝ) := by
  norm_num [coefficientValue, rootTwo, rootFifteen, source_rootFifteen, source_rootTwo, gaugeScale]
  <;> ring_nf! <;> norm_num [spinScale_sq] <;> ring

private theorem nativeAtomCalc11 : (coefficientValue (⟨⟨0,0⟩,⟨0,(-1/5:ℚ)⟩⟩:SourceCoefficient)).re = (-(25*lapse/3)/5:ℝ) := by
  norm_num [coefficientValue, rootTwo, rootFifteen, source_rootFifteen, source_rootTwo, gaugeScale]
  <;> ring_nf! <;> norm_num [spinScale_sq] <;> ring

private theorem nativeAtomCalc12 : (coefficientValue (⟨⟨0,0⟩,⟨0,(-1/3:ℚ)⟩⟩:SourceCoefficient)).re = (-(25*lapse/3)/3:ℝ) := by
  norm_num [coefficientValue, rootTwo, rootFifteen, source_rootFifteen, source_rootTwo, gaugeScale]
  <;> ring_nf! <;> norm_num [spinScale_sq] <;> ring

private theorem nativeAtomCalc13 : (coefficientValue (⟨⟨(5/6:ℚ),0⟩,⟨0,0⟩⟩:SourceCoefficient)).re = (5/6:ℝ) := by
  norm_num [coefficientValue, rootTwo, rootFifteen, source_rootFifteen, source_rootTwo, gaugeScale]
  <;> ring_nf! <;> norm_num [spinScale_sq] <;> ring

private theorem nativeAtomCalc14 : (coefficientValue (⟨⟨(-5/6:ℚ),0⟩,⟨0,0⟩⟩:SourceCoefficient)).re = (-5/6:ℝ) := by
  norm_num [coefficientValue, rootTwo, rootFifteen, source_rootFifteen, source_rootTwo, gaugeScale]
  <;> ring_nf! <;> norm_num [spinScale_sq] <;> ring

private theorem nativeAtomCalc15 : (coefficientValue (⟨⟨(-5/3:ℚ),0⟩,⟨0,0⟩⟩:SourceCoefficient)).re = (-5/3:ℝ) := by
  norm_num [coefficientValue, rootTwo, rootFifteen, source_rootFifteen, source_rootTwo, gaugeScale]
  <;> ring_nf! <;> norm_num [spinScale_sq] <;> ring

private theorem nativeAtomCalc16 : (coefficientValue (⟨⟨0,0⟩,⟨0,(18/125:ℚ)⟩⟩:SourceCoefficient)).re = (18*(25*lapse/3)/125:ℝ) := by
  norm_num [coefficientValue, rootTwo, rootFifteen, source_rootFifteen, source_rootTwo, gaugeScale]
  <;> ring_nf! <;> norm_num [spinScale_sq] <;> ring

private theorem nativeAtomCalc17 : (coefficientValue (⟨⟨0,0⟩,⟨0,(-9/125:ℚ)⟩⟩:SourceCoefficient)).re = (-9*(25*lapse/3)/125:ℝ) := by
  norm_num [coefficientValue, rootTwo, rootFifteen, source_rootFifteen, source_rootTwo, gaugeScale]
  <;> ring_nf! <;> norm_num [spinScale_sq] <;> ring

private theorem nativeAtomCalc18 : (coefficientValue (⟨⟨(18/25:ℚ),0⟩,⟨0,0⟩⟩:SourceCoefficient)).re = (18/25:ℝ) := by
  norm_num [coefficientValue, rootTwo, rootFifteen, source_rootFifteen, source_rootTwo, gaugeScale]
  <;> ring_nf! <;> norm_num [spinScale_sq] <;> ring

private theorem nativeAtomCalc19 : (coefficientValue (⟨⟨(-18/25:ℚ),0⟩,⟨0,0⟩⟩:SourceCoefficient)).re = (-18/25:ℝ) := by
  norm_num [coefficientValue, rootTwo, rootFifteen, source_rootFifteen, source_rootTwo, gaugeScale]
  <;> ring_nf! <;> norm_num [spinScale_sq] <;> ring

private theorem nativeAtomCalc20 : (coefficientValue (⟨⟨(-9/25:ℚ),0⟩,⟨0,0⟩⟩:SourceCoefficient)).re = (-9/25:ℝ) := by
  norm_num [coefficientValue, rootTwo, rootFifteen, source_rootFifteen, source_rootTwo, gaugeScale]
  <;> ring_nf! <;> norm_num [spinScale_sq] <;> ring

private theorem nativeAtomCalc21 : (coefficientValue (⟨⟨(9/25:ℚ),0⟩,⟨0,0⟩⟩:SourceCoefficient)).re = (9/25:ℝ) := by
  norm_num [coefficientValue, rootTwo, rootFifteen, source_rootFifteen, source_rootTwo, gaugeScale]
  <;> ring_nf! <;> norm_num [spinScale_sq] <;> ring

private theorem nativeAtomCalc22 : (coefficientValue (⟨⟨0,0⟩,⟨0,(9/125:ℚ)⟩⟩:SourceCoefficient)).re = (9*(25*lapse/3)/125:ℝ) := by
  norm_num [coefficientValue, rootTwo, rootFifteen, source_rootFifteen, source_rootTwo, gaugeScale]
  <;> ring_nf! <;> norm_num [spinScale_sq] <;> ring

private theorem nativeAtomCalc23 : (coefficientValue (⟨⟨0,0⟩,⟨0,(27/125:ℚ)⟩⟩:SourceCoefficient)).re = (27*(25*lapse/3)/125:ℝ) := by
  norm_num [coefficientValue, rootTwo, rootFifteen, source_rootFifteen, source_rootTwo, gaugeScale]
  <;> ring_nf! <;> norm_num [spinScale_sq] <;> ring

private theorem nativeAtomCalc24 : (coefficientValue (⟨⟨(5/3:ℚ),0⟩,⟨0,0⟩⟩:SourceCoefficient)).re = (5/3:ℝ) := by
  norm_num [coefficientValue, rootTwo, rootFifteen, source_rootFifteen, source_rootTwo, gaugeScale]
  <;> ring_nf! <;> norm_num [spinScale_sq] <;> ring

private theorem nativeAtomCalc25 : (coefficientValue (⟨⟨0,(3/5:ℚ)⟩,⟨0,0⟩⟩:SourceCoefficient)).re = (3*spinScale/5:ℝ) := by
  norm_num [coefficientValue, rootTwo, rootFifteen, source_rootFifteen, source_rootTwo, gaugeScale]
  <;> ring_nf! <;> norm_num [spinScale_sq] <;> ring

private theorem nativeAtomCalc26 : (coefficientValue (⟨⟨0,(-3/5:ℚ)⟩,⟨0,0⟩⟩:SourceCoefficient)).re = (-3*spinScale/5:ℝ) := by
  norm_num [coefficientValue, rootTwo, rootFifteen, source_rootFifteen, source_rootTwo, gaugeScale]
  <;> ring_nf! <;> norm_num [spinScale_sq] <;> ring

private theorem nativeAtomCalc27 : (coefficientValue (⟨⟨0,(-6/5:ℚ)⟩,⟨0,0⟩⟩:SourceCoefficient)).re = (-6*spinScale/5:ℝ) := by
  norm_num [coefficientValue, rootTwo, rootFifteen, source_rootFifteen, source_rootTwo, gaugeScale]
  <;> ring_nf! <;> norm_num [spinScale_sq] <;> ring

private theorem nativeAtomCalc28 : (coefficientValue (⟨⟨0,(6/5:ℚ)⟩,⟨0,0⟩⟩:SourceCoefficient)).re = (6*spinScale/5:ℝ) := by
  norm_num [coefficientValue, rootTwo, rootFifteen, source_rootFifteen, source_rootTwo, gaugeScale]
  <;> ring_nf! <;> norm_num [spinScale_sq] <;> ring

private theorem nativeAtomCalc29 : (coefficientValue (⟨⟨0,0⟩,⟨0,(4/5:ℚ)⟩⟩:SourceCoefficient)).re = (4*(25*lapse/3)/5:ℝ) := by
  norm_num [coefficientValue, rootTwo, rootFifteen, source_rootFifteen, source_rootTwo, gaugeScale]
  <;> ring_nf! <;> norm_num [spinScale_sq] <;> ring

private theorem nativeAtomCalc30 : (coefficientValue (⟨⟨0,0⟩,⟨0,(-4/5:ℚ)⟩⟩:SourceCoefficient)).re = (-4*(25*lapse/3)/5:ℝ) := by
  norm_num [coefficientValue, rootTwo, rootFifteen, source_rootFifteen, source_rootTwo, gaugeScale]
  <;> ring_nf! <;> norm_num [spinScale_sq] <;> ring

private theorem nativeAtomCalc31 : (coefficientValue (⟨⟨0,0⟩,⟨0,(-2/5:ℚ)⟩⟩:SourceCoefficient)).re = (-2*(25*lapse/3)/5:ℝ) := by
  norm_num [coefficientValue, rootTwo, rootFifteen, source_rootFifteen, source_rootTwo, gaugeScale]
  <;> ring_nf! <;> norm_num [spinScale_sq] <;> ring

private theorem nativeAtomCalc32 : (coefficientValue (⟨⟨0,0⟩,⟨0,(2/5:ℚ)⟩⟩:SourceCoefficient)).re = (2*(25*lapse/3)/5:ℝ) := by
  norm_num [coefficientValue, rootTwo, rootFifteen, source_rootFifteen, source_rootTwo, gaugeScale]
  <;> ring_nf! <;> norm_num [spinScale_sq] <;> ring

private theorem nativeAtomCalc33 : (coefficientValue (⟨⟨2,0⟩,⟨0,0⟩⟩:SourceCoefficient)).re = (2:ℝ) := by
  norm_num [coefficientValue, rootTwo, rootFifteen, source_rootFifteen, source_rootTwo, gaugeScale]
  <;> ring_nf! <;> norm_num [spinScale_sq] <;> ring

private theorem nativeAtomCalc34 : (coefficientValue (⟨⟨-2,0⟩,⟨0,0⟩⟩:SourceCoefficient)).re = (-2:ℝ) := by
  norm_num [coefficientValue, rootTwo, rootFifteen, source_rootFifteen, source_rootTwo, gaugeScale]
  <;> ring_nf! <;> norm_num [spinScale_sq] <;> ring

private theorem nativeAtomCalc35 : (coefficientValue (⟨⟨0,0⟩,⟨0,(3/50:ℚ)⟩⟩:SourceCoefficient)).re = (3*(25*lapse/3)/50:ℝ) := by
  norm_num [coefficientValue, rootTwo, rootFifteen, source_rootFifteen, source_rootTwo, gaugeScale]
  <;> ring_nf! <;> norm_num [spinScale_sq] <;> ring

private theorem nativeAtomCalc36 : (coefficientValue (⟨⟨0,0⟩,⟨0,(3/100:ℚ)⟩⟩:SourceCoefficient)).re = (3*(25*lapse/3)/100:ℝ) := by
  norm_num [coefficientValue, rootTwo, rootFifteen, source_rootFifteen, source_rootTwo, gaugeScale]
  <;> ring_nf! <;> norm_num [spinScale_sq] <;> ring

private theorem nativeAtomCalc37 : (coefficientValue (⟨⟨0,0⟩,⟨0,(-5/36:ℚ)⟩⟩:SourceCoefficient)).re = (-5*(25*lapse/3)/36:ℝ) := by
  norm_num [coefficientValue, rootTwo, rootFifteen, source_rootFifteen, source_rootTwo, gaugeScale]
  <;> ring_nf! <;> norm_num [spinScale_sq] <;> ring

private theorem nativeAtomCalc38 : (coefficientValue (⟨⟨0,0⟩,⟨0,(-5/72:ℚ)⟩⟩:SourceCoefficient)).re = (-5*(25*lapse/3)/72:ℝ) := by
  norm_num [coefficientValue, rootTwo, rootFifteen, source_rootFifteen, source_rootTwo, gaugeScale]
  <;> ring_nf! <;> norm_num [spinScale_sq] <;> ring

private theorem nativeAtomCalc39 : (coefficientValue (⟨⟨0,0⟩,⟨0,(-5/18:ℚ)⟩⟩:SourceCoefficient)).re = ((-125/54:ℝ)*lapse:ℝ) := by
  norm_num [coefficientValue, rootTwo, rootFifteen, source_rootFifteen, source_rootTwo, gaugeScale]
  <;> ring_nf! <;> norm_num [spinScale_sq] <;> ring

private theorem nativeAtomCalc40 : (coefficientValue (⟨⟨0,0⟩,⟨0,(-5/9:ℚ)⟩⟩:SourceCoefficient)).re = ((-125/27:ℝ)*lapse:ℝ) := by
  norm_num [coefficientValue, rootTwo, rootFifteen, source_rootFifteen, source_rootTwo, gaugeScale]
  <;> ring_nf! <;> norm_num [spinScale_sq] <;> ring

private theorem nativeAtomCalc41 : (coefficientValue (⟨⟨0,0⟩,⟨0,(5/18:ℚ)⟩⟩:SourceCoefficient)).re = ((125/54:ℝ)*lapse:ℝ) := by
  norm_num [coefficientValue, rootTwo, rootFifteen, source_rootFifteen, source_rootTwo, gaugeScale]
  <;> ring_nf! <;> norm_num [spinScale_sq] <;> ring

private theorem nativeAtomCalc42 : (coefficientValue (⟨⟨0,0⟩,⟨(-18/125:ℚ),0⟩⟩:SourceCoefficient)).re = (-lapse*gaugeScale:ℝ) := by
  norm_num [coefficientValue, rootTwo, rootFifteen, source_rootFifteen, source_rootTwo, gaugeScale]
  <;> ring_nf! <;> norm_num [spinScale_sq] <;> ring

private theorem nativeAtomCalc43 : (coefficientValue (⟨⟨0,0⟩,⟨0,(6/25:ℚ)⟩⟩:SourceCoefficient)).re = (2*lapse:ℝ) := by
  norm_num [coefficientValue, rootTwo, rootFifteen, source_rootFifteen, source_rootTwo, gaugeScale]
  <;> ring_nf! <;> norm_num [spinScale_sq] <;> ring

private theorem nativeAtomCalc44 : (coefficientValue (⟨⟨0,0⟩,⟨(18/125:ℚ),0⟩⟩:SourceCoefficient)).re = (lapse*gaugeScale:ℝ) := by
  norm_num [coefficientValue, rootTwo, rootFifteen, source_rootFifteen, source_rootTwo, gaugeScale]
  <;> ring_nf! <;> norm_num [spinScale_sq] <;> ring

private theorem nativeAtomCalc45 : (coefficientValue (⟨⟨0,0⟩,⟨0,(-219/1250:ℚ)⟩⟩:SourceCoefficient)).re = ((-73/50:ℝ)*lapse:ℝ) := by
  norm_num [coefficientValue, rootTwo, rootFifteen, source_rootFifteen, source_rootTwo, gaugeScale]
  <;> ring_nf! <;> norm_num [spinScale_sq] <;> ring

private theorem nativeAtomCalc46 : (coefficientValue (⟨⟨0,0⟩,⟨0,(-6/25:ℚ)⟩⟩:SourceCoefficient)).re = (-2*lapse:ℝ) := by
  norm_num [coefficientValue, rootTwo, rootFifteen, source_rootFifteen, source_rootTwo, gaugeScale]
  <;> ring_nf! <;> norm_num [spinScale_sq] <;> ring

private theorem nativeAtomCalc47 : (coefficientValue (⟨⟨(-16/5:ℚ),0⟩,⟨0,0⟩⟩:SourceCoefficient)).re = ((-16/5:ℝ):ℝ) := by
  norm_num [coefficientValue, rootTwo, rootFifteen, source_rootFifteen, source_rootTwo, gaugeScale]
  <;> ring_nf! <;> norm_num [spinScale_sq] <;> ring

private theorem nativeAtomCalc48 : (coefficientValue (⟨⟨0,4⟩,⟨0,0⟩⟩:SourceCoefficient)).re = (4*spinScale:ℝ) := by
  norm_num [coefficientValue, rootTwo, rootFifteen, source_rootFifteen, source_rootTwo, gaugeScale]
  <;> ring_nf! <;> norm_num [spinScale_sq] <;> ring

private theorem nativeAtomCalc49 : (coefficientValue (⟨⟨0,2⟩,⟨0,0⟩⟩:SourceCoefficient)).re = (2*spinScale:ℝ) := by
  norm_num [coefficientValue, rootTwo, rootFifteen, source_rootFifteen, source_rootTwo, gaugeScale]
  <;> ring_nf! <;> norm_num [spinScale_sq] <;> ring

private theorem nativeAtomCalc50 : (coefficientValue (⟨⟨0,-2⟩,⟨0,0⟩⟩:SourceCoefficient)).re = (-2*spinScale:ℝ) := by
  norm_num [coefficientValue, rootTwo, rootFifteen, source_rootFifteen, source_rootTwo, gaugeScale]
  <;> ring_nf! <;> norm_num [spinScale_sq] <;> ring

private theorem nativeAtomCalc51 : (coefficientValue (⟨⟨(-6/5:ℚ),0⟩,⟨0,0⟩⟩:SourceCoefficient)).re = ((-6/5:ℝ):ℝ) := by
  norm_num [coefficientValue, rootTwo, rootFifteen, source_rootFifteen, source_rootTwo, gaugeScale]
  <;> ring_nf! <;> norm_num [spinScale_sq] <;> ring

private theorem nativeAtomCalc52 : (coefficientValue (⟨⟨(6/5:ℚ),0⟩,⟨0,0⟩⟩:SourceCoefficient)).re = ((6/5:ℝ):ℝ) := by
  norm_num [coefficientValue, rootTwo, rootFifteen, source_rootFifteen, source_rootTwo, gaugeScale]
  <;> ring_nf! <;> norm_num [spinScale_sq] <;> ring

private theorem nativeAtomCalc53 : (coefficientValue (⟨⟨0,(-3/5:ℚ)⟩,⟨0,0⟩⟩:SourceCoefficient)).re = ((-3/5:ℝ)*spinScale:ℝ) := by
  norm_num [coefficientValue, rootTwo, rootFifteen, source_rootFifteen, source_rootTwo, gaugeScale]
  <;> ring_nf! <;> norm_num [spinScale_sq] <;> ring

private theorem nativeAtomCalc54 : (coefficientValue (⟨⟨0,(3/5:ℚ)⟩,⟨0,0⟩⟩:SourceCoefficient)).re = ((3/5:ℝ)*spinScale:ℝ) := by
  norm_num [coefficientValue, rootTwo, rootFifteen, source_rootFifteen, source_rootTwo, gaugeScale]
  <;> ring_nf! <;> norm_num [spinScale_sq] <;> ring

private theorem nativeAtomCalc55 : (coefficientValue (⟨⟨0,1⟩,⟨0,0⟩⟩:SourceCoefficient)).re = (1*spinScale:ℝ) := by
  norm_num [coefficientValue, rootTwo, rootFifteen, source_rootFifteen, source_rootTwo, gaugeScale]
  <;> ring_nf! <;> norm_num [spinScale_sq] <;> ring

private theorem nativeAtomCalc56 : (coefficientValue (⟨⟨0,-1⟩,⟨0,0⟩⟩:SourceCoefficient)).re = (-1*spinScale:ℝ) := by
  norm_num [coefficientValue, rootTwo, rootFifteen, source_rootFifteen, source_rootTwo, gaugeScale]
  <;> ring_nf! <;> norm_num [spinScale_sq] <;> ring

private theorem nativeAtomCalc57 : (coefficientValue (⟨⟨(16/5:ℚ),0⟩,⟨0,0⟩⟩:SourceCoefficient)).re = ((16/5:ℝ):ℝ) := by
  norm_num [coefficientValue, rootTwo, rootFifteen, source_rootFifteen, source_rootTwo, gaugeScale]
  <;> ring_nf! <;> norm_num [spinScale_sq] <;> ring

private theorem nativeAtomCalc58 : (coefficientValue (⟨⟨0,-4⟩,⟨0,0⟩⟩:SourceCoefficient)).re = (-4*spinScale:ℝ) := by
  norm_num [coefficientValue, rootTwo, rootFifteen, source_rootFifteen, source_rootTwo, gaugeScale]
  <;> ring_nf! <;> norm_num [spinScale_sq] <;> ring

private theorem nativeAtomCalc59 : (coefficientValue (⟨⟨0,0⟩,⟨0,(-18/125:ℚ)⟩⟩:SourceCoefficient)).re = ((-18/125:ℝ)*((25/3:ℝ)*lapse):ℝ) := by
  norm_num [coefficientValue, rootTwo, rootFifteen, source_rootFifteen, source_rootTwo, gaugeScale]
  <;> ring_nf! <;> norm_num [spinScale_sq] <;> ring

private theorem nativeAtomCalc60 : (coefficientValue (⟨⟨0,0⟩,⟨0,(18/125:ℚ)⟩⟩:SourceCoefficient)).re = ((18/125:ℝ)*((25/3:ℝ)*lapse):ℝ) := by
  norm_num [coefficientValue, rootTwo, rootFifteen, source_rootFifteen, source_rootTwo, gaugeScale]
  <;> ring_nf! <;> norm_num [spinScale_sq] <;> ring

private theorem nativeAtomCalc61 : (coefficientValue (⟨⟨0,0⟩,⟨(18/125:ℚ),0⟩⟩:SourceCoefficient)).re = ((18/125:ℝ)*((25/6:ℝ)*lapse*spinScale):ℝ) := by
  norm_num [coefficientValue, rootTwo, rootFifteen, source_rootFifteen, source_rootTwo, gaugeScale]
  <;> ring_nf! <;> norm_num [spinScale_sq] <;> ring

private theorem nativeAtomCalc62 : (coefficientValue (⟨⟨0,0⟩,⟨(-18/125:ℚ),0⟩⟩:SourceCoefficient)).re = ((-18/125:ℝ)*((25/6:ℝ)*lapse*spinScale):ℝ) := by
  norm_num [coefficientValue, rootTwo, rootFifteen, source_rootFifteen, source_rootTwo, gaugeScale]
  <;> ring_nf! <;> norm_num [spinScale_sq] <;> ring

private theorem nativeAtomCalc63 : (coefficientValue (⟨⟨(2/5:ℚ),0⟩,⟨0,0⟩⟩:SourceCoefficient)).re = ((2/5:ℝ):ℝ) := by
  norm_num [coefficientValue, rootTwo, rootFifteen, source_rootFifteen, source_rootTwo, gaugeScale]
  <;> ring_nf! <;> norm_num [spinScale_sq] <;> ring

private theorem nativeAtomCalc64 : (coefficientValue (⟨⟨(-2/5:ℚ),0⟩,⟨0,0⟩⟩:SourceCoefficient)).re = ((-2/5:ℝ):ℝ) := by
  norm_num [coefficientValue, rootTwo, rootFifteen, source_rootFifteen, source_rootTwo, gaugeScale]
  <;> ring_nf! <;> norm_num [spinScale_sq] <;> ring

private theorem nativeAtomCalc65 : (coefficientValue (⟨⟨0,(-1/5:ℚ)⟩,⟨0,0⟩⟩:SourceCoefficient)).re = ((-1/5:ℝ)*spinScale:ℝ) := by
  norm_num [coefficientValue, rootTwo, rootFifteen, source_rootFifteen, source_rootTwo, gaugeScale]
  <;> ring_nf! <;> norm_num [spinScale_sq] <;> ring

private theorem nativeAtomCalc66 : (coefficientValue (⟨⟨0,(1/5:ℚ)⟩,⟨0,0⟩⟩:SourceCoefficient)).re = ((1/5:ℝ)*spinScale:ℝ) := by
  norm_num [coefficientValue, rootTwo, rootFifteen, source_rootFifteen, source_rootTwo, gaugeScale]
  <;> ring_nf! <;> norm_num [spinScale_sq] <;> ring

private theorem nativeAtomCalc67 : (coefficientValue (⟨⟨0,0⟩,⟨0,(48/125:ℚ)⟩⟩:SourceCoefficient)).re = ((48/125:ℝ)*((25/3:ℝ)*lapse):ℝ) := by
  norm_num [coefficientValue, rootTwo, rootFifteen, source_rootFifteen, source_rootTwo, gaugeScale]
  <;> ring_nf! <;> norm_num [spinScale_sq] <;> ring

private theorem nativeAtomCalc68 : (coefficientValue (⟨⟨0,0⟩,⟨(24/25:ℚ),0⟩⟩:SourceCoefficient)).re = ((24/25:ℝ)*((25/6:ℝ)*lapse*spinScale):ℝ) := by
  norm_num [coefficientValue, rootTwo, rootFifteen, source_rootFifteen, source_rootTwo, gaugeScale]
  <;> ring_nf! <;> norm_num [spinScale_sq] <;> ring

private theorem nativeAtomCalc69 : (coefficientValue (⟨⟨0,0⟩,⟨(12/25:ℚ),0⟩⟩:SourceCoefficient)).re = ((12/25:ℝ)*((25/6:ℝ)*lapse*spinScale):ℝ) := by
  norm_num [coefficientValue, rootTwo, rootFifteen, source_rootFifteen, source_rootTwo, gaugeScale]
  <;> ring_nf! <;> norm_num [spinScale_sq] <;> ring

private theorem nativeAtomCalc70 : (coefficientValue (⟨⟨0,0⟩,⟨(-12/25:ℚ),0⟩⟩:SourceCoefficient)).re = ((-12/25:ℝ)*((25/6:ℝ)*lapse*spinScale):ℝ) := by
  norm_num [coefficientValue, rootTwo, rootFifteen, source_rootFifteen, source_rootTwo, gaugeScale]
  <;> ring_nf! <;> norm_num [spinScale_sq] <;> ring

private theorem nativeAtomCalc71 : (coefficientValue (⟨⟨0,0⟩,⟨0,(6/125:ℚ)⟩⟩:SourceCoefficient)).re = ((6/125:ℝ)*((25/3:ℝ)*lapse):ℝ) := by
  norm_num [coefficientValue, rootTwo, rootFifteen, source_rootFifteen, source_rootTwo, gaugeScale]
  <;> ring_nf! <;> norm_num [spinScale_sq] <;> ring

private theorem nativeAtomCalc72 : (coefficientValue (⟨⟨0,0⟩,⟨0,(-6/125:ℚ)⟩⟩:SourceCoefficient)).re = ((-6/125:ℝ)*((25/3:ℝ)*lapse):ℝ) := by
  norm_num [coefficientValue, rootTwo, rootFifteen, source_rootFifteen, source_rootTwo, gaugeScale]
  <;> ring_nf! <;> norm_num [spinScale_sq] <;> ring

private theorem nativeAtomCalc73 : (coefficientValue (⟨⟨0,0⟩,⟨(6/125:ℚ),0⟩⟩:SourceCoefficient)).re = ((6/125:ℝ)*((25/6:ℝ)*lapse*spinScale):ℝ) := by
  norm_num [coefficientValue, rootTwo, rootFifteen, source_rootFifteen, source_rootTwo, gaugeScale]
  <;> ring_nf! <;> norm_num [spinScale_sq] <;> ring

private theorem nativeAtomCalc74 : (coefficientValue (⟨⟨0,0⟩,⟨(-6/125:ℚ),0⟩⟩:SourceCoefficient)).re = ((-6/125:ℝ)*((25/6:ℝ)*lapse*spinScale):ℝ) := by
  norm_num [coefficientValue, rootTwo, rootFifteen, source_rootFifteen, source_rootTwo, gaugeScale]
  <;> ring_nf! <;> norm_num [spinScale_sq] <;> ring

private theorem nativeAtomCalc75 : (coefficientValue (⟨⟨0,0⟩,⟨(6/25:ℚ),0⟩⟩:SourceCoefficient)).re = ((6/25:ℝ)*((25/6:ℝ)*lapse*spinScale):ℝ) := by
  norm_num [coefficientValue, rootTwo, rootFifteen, source_rootFifteen, source_rootTwo, gaugeScale]
  <;> ring_nf! <;> norm_num [spinScale_sq] <;> ring

private theorem nativeAtomCalc76 : (coefficientValue (⟨⟨0,0⟩,⟨(-6/25:ℚ),0⟩⟩:SourceCoefficient)).re = ((-6/25:ℝ)*((25/6:ℝ)*lapse*spinScale):ℝ) := by
  norm_num [coefficientValue, rootTwo, rootFifteen, source_rootFifteen, source_rootTwo, gaugeScale]
  <;> ring_nf! <;> norm_num [spinScale_sq] <;> ring

private theorem nativeAtomCalc77 : (coefficientValue (⟨⟨0,0⟩,⟨0,(-48/125:ℚ)⟩⟩:SourceCoefficient)).re = ((-48/125:ℝ)*((25/3:ℝ)*lapse):ℝ) := by
  norm_num [coefficientValue, rootTwo, rootFifteen, source_rootFifteen, source_rootTwo, gaugeScale]
  <;> ring_nf! <;> norm_num [spinScale_sq] <;> ring

private theorem nativeAtomCalc78 : (coefficientValue (⟨⟨0,0⟩,⟨(-24/25:ℚ),0⟩⟩:SourceCoefficient)).re = ((-24/25:ℝ)*((25/6:ℝ)*lapse*spinScale):ℝ) := by
  norm_num [coefficientValue, rootTwo, rootFifteen, source_rootFifteen, source_rootTwo, gaugeScale]
  <;> ring_nf! <;> norm_num [spinScale_sq] <;> ring

private theorem nativeAtomCalc79 : (coefficientValue (⟨⟨0,0⟩,⟨0,(24/125:ℚ)⟩⟩:SourceCoefficient)).re = ((24/125:ℝ)*((25/3:ℝ)*lapse):ℝ) := by
  norm_num [coefficientValue, rootTwo, rootFifteen, source_rootFifteen, source_rootTwo, gaugeScale]
  <;> ring_nf! <;> norm_num [spinScale_sq] <;> ring

private theorem nativeAtomCalc80 : (coefficientValue (⟨⟨0,0⟩,⟨0,(-24/125:ℚ)⟩⟩:SourceCoefficient)).re = ((-24/125:ℝ)*((25/3:ℝ)*lapse):ℝ) := by
  norm_num [coefficientValue, rootTwo, rootFifteen, source_rootFifteen, source_rootTwo, gaugeScale]
  <;> ring_nf! <;> norm_num [spinScale_sq] <;> ring

private theorem nativeAtomCalc81 : (coefficientValue (⟨⟨0,0⟩,⟨0,(-3/25:ℚ)⟩⟩:SourceCoefficient)).re = ((-3/25:ℝ)*((25/3:ℝ)*lapse):ℝ) := by
  norm_num [coefficientValue, rootTwo, rootFifteen, source_rootFifteen, source_rootTwo, gaugeScale]
  <;> ring_nf! <;> norm_num [spinScale_sq] <;> ring

private theorem nativeAtomCalc82 : (coefficientValue (⟨⟨0,0⟩,⟨0,(3/25:ℚ)⟩⟩:SourceCoefficient)).re = ((3/25:ℝ)*((25/3:ℝ)*lapse):ℝ) := by
  norm_num [coefficientValue, rootTwo, rootFifteen, source_rootFifteen, source_rootTwo, gaugeScale]
  <;> ring_nf! <;> norm_num [spinScale_sq] <;> ring

private theorem nativeAtomCalc83 : (coefficientValue (⟨⟨0,(-1/2:ℚ)⟩,⟨0,0⟩⟩:SourceCoefficient)).re = ((-1/2:ℝ)*spinScale:ℝ) := by
  norm_num [coefficientValue, rootTwo, rootFifteen, source_rootFifteen, source_rootTwo, gaugeScale]
  <;> ring_nf! <;> norm_num [spinScale_sq] <;> ring

private theorem nativeAtomCalc84 : (coefficientValue (⟨⟨0,(1/2:ℚ)⟩,⟨0,0⟩⟩:SourceCoefficient)).re = ((1/2:ℝ)*spinScale:ℝ) := by
  norm_num [coefficientValue, rootTwo, rootFifteen, source_rootFifteen, source_rootTwo, gaugeScale]
  <;> ring_nf! <;> norm_num [spinScale_sq] <;> ring

private theorem nativeAtomCalc85 : (coefficientValue (⟨⟨(-1/2:ℚ),0⟩,⟨0,0⟩⟩:SourceCoefficient)).re = ((-1/2:ℝ):ℝ) := by
  norm_num [coefficientValue, rootTwo, rootFifteen, source_rootFifteen, source_rootTwo, gaugeScale]
  <;> ring_nf! <;> norm_num [spinScale_sq] <;> ring

private theorem nativeAtomCalc86 : (coefficientValue (⟨⟨(1/2:ℚ),0⟩,⟨0,0⟩⟩:SourceCoefficient)).re = ((1/2:ℝ):ℝ) := by
  norm_num [coefficientValue, rootTwo, rootFifteen, source_rootFifteen, source_rootTwo, gaugeScale]
  <;> ring_nf! <;> norm_num [spinScale_sq] <;> ring

private theorem nativeAtomCalc87 : (coefficientValue (⟨⟨0,0⟩,⟨(-3/25:ℚ),0⟩⟩:SourceCoefficient)).re = ((-3/25:ℝ)*((25/6:ℝ)*lapse*spinScale):ℝ) := by
  norm_num [coefficientValue, rootTwo, rootFifteen, source_rootFifteen, source_rootTwo, gaugeScale]
  <;> ring_nf! <;> norm_num [spinScale_sq] <;> ring

private theorem nativeAtomCalc88 : (coefficientValue (⟨⟨0,0⟩,⟨(3/25:ℚ),0⟩⟩:SourceCoefficient)).re = ((3/25:ℝ)*((25/6:ℝ)*lapse*spinScale):ℝ) := by
  norm_num [coefficientValue, rootTwo, rootFifteen, source_rootFifteen, source_rootTwo, gaugeScale]
  <;> ring_nf! <;> norm_num [spinScale_sq] <;> ring

private theorem nativeAtomCalc89 : (coefficientValue (⟨⟨0,0⟩,⟨0,(3/50:ℚ)⟩⟩:SourceCoefficient)).re = ((3/50:ℝ)*((25/3:ℝ)*lapse):ℝ) := by
  norm_num [coefficientValue, rootTwo, rootFifteen, source_rootFifteen, source_rootTwo, gaugeScale]
  <;> ring_nf! <;> norm_num [spinScale_sq] <;> ring

private theorem nativeAtomCalc90 : (coefficientValue (⟨⟨0,0⟩,⟨0,(-3/50:ℚ)⟩⟩:SourceCoefficient)).re = ((-3/50:ℝ)*((25/3:ℝ)*lapse):ℝ) := by
  norm_num [coefficientValue, rootTwo, rootFifteen, source_rootFifteen, source_rootTwo, gaugeScale]
  <;> ring_nf! <;> norm_num [spinScale_sq] <;> ring

private theorem nativeAtomCalc91 : (coefficientValue (⟨⟨0,0⟩,⟨(-36/125:ℚ),0⟩⟩:SourceCoefficient)).re = ((-36/125:ℝ)*((25/6:ℝ)*lapse*spinScale):ℝ) := by
  norm_num [coefficientValue, rootTwo, rootFifteen, source_rootFifteen, source_rootTwo, gaugeScale]
  <;> ring_nf! <;> norm_num [spinScale_sq] <;> ring

private theorem nativeAtomCalc92 : (coefficientValue (⟨⟨0,0⟩,⟨(36/125:ℚ),0⟩⟩:SourceCoefficient)).re = ((36/125:ℝ)*((25/6:ℝ)*lapse*spinScale):ℝ) := by
  norm_num [coefficientValue, rootTwo, rootFifteen, source_rootFifteen, source_rootTwo, gaugeScale]
  <;> ring_nf! <;> norm_num [spinScale_sq] <;> ring

private theorem nativeAtomCalc93 : (coefficientValue (⟨⟨0,0⟩,⟨(-27/125:ℚ),0⟩⟩:SourceCoefficient)).re = ((-27/125:ℝ)*((25/6:ℝ)*lapse*spinScale):ℝ) := by
  norm_num [coefficientValue, rootTwo, rootFifteen, source_rootFifteen, source_rootTwo, gaugeScale]
  <;> ring_nf! <;> norm_num [spinScale_sq] <;> ring

private theorem nativeAtomCalc94 : (coefficientValue (⟨⟨0,0⟩,⟨(27/125:ℚ),0⟩⟩:SourceCoefficient)).re = ((27/125:ℝ)*((25/6:ℝ)*lapse*spinScale):ℝ) := by
  norm_num [coefficientValue, rootTwo, rootFifteen, source_rootFifteen, source_rootTwo, gaugeScale]
  <;> ring_nf! <;> norm_num [spinScale_sq] <;> ring

theorem nativeRecordAtom_value (i : Fin 95) :
    (coefficientValue (nativeRecordCoefficientAtoms[i.val]?.getD 0)).re =
      nativeRecordRealAtoms[i.val]?.getD 0 := by
  fin_cases i
  · exact nativeAtomCalc0
  · exact nativeAtomCalc1
  · exact nativeAtomCalc2
  · exact nativeAtomCalc3
  · exact nativeAtomCalc4
  · exact nativeAtomCalc5
  · exact nativeAtomCalc6
  · exact nativeAtomCalc7
  · exact nativeAtomCalc8
  · exact nativeAtomCalc9
  · exact nativeAtomCalc10
  · exact nativeAtomCalc11
  · exact nativeAtomCalc12
  · exact nativeAtomCalc13
  · exact nativeAtomCalc14
  · exact nativeAtomCalc15
  · exact nativeAtomCalc16
  · exact nativeAtomCalc17
  · exact nativeAtomCalc18
  · exact nativeAtomCalc19
  · exact nativeAtomCalc20
  · exact nativeAtomCalc21
  · exact nativeAtomCalc22
  · exact nativeAtomCalc23
  · exact nativeAtomCalc24
  · exact nativeAtomCalc25
  · exact nativeAtomCalc26
  · exact nativeAtomCalc27
  · exact nativeAtomCalc28
  · exact nativeAtomCalc29
  · exact nativeAtomCalc30
  · exact nativeAtomCalc31
  · exact nativeAtomCalc32
  · exact nativeAtomCalc33
  · exact nativeAtomCalc34
  · exact nativeAtomCalc35
  · exact nativeAtomCalc36
  · exact nativeAtomCalc37
  · exact nativeAtomCalc38
  · exact nativeAtomCalc39
  · exact nativeAtomCalc40
  · exact nativeAtomCalc41
  · exact nativeAtomCalc42
  · exact nativeAtomCalc43
  · exact nativeAtomCalc44
  · exact nativeAtomCalc45
  · exact nativeAtomCalc46
  · exact nativeAtomCalc47
  · exact nativeAtomCalc48
  · exact nativeAtomCalc49
  · exact nativeAtomCalc50
  · exact nativeAtomCalc51
  · exact nativeAtomCalc52
  · exact nativeAtomCalc53
  · exact nativeAtomCalc54
  · exact nativeAtomCalc55
  · exact nativeAtomCalc56
  · exact nativeAtomCalc57
  · exact nativeAtomCalc58
  · exact nativeAtomCalc59
  · exact nativeAtomCalc60
  · exact nativeAtomCalc61
  · exact nativeAtomCalc62
  · exact nativeAtomCalc63
  · exact nativeAtomCalc64
  · exact nativeAtomCalc65
  · exact nativeAtomCalc66
  · exact nativeAtomCalc67
  · exact nativeAtomCalc68
  · exact nativeAtomCalc69
  · exact nativeAtomCalc70
  · exact nativeAtomCalc71
  · exact nativeAtomCalc72
  · exact nativeAtomCalc73
  · exact nativeAtomCalc74
  · exact nativeAtomCalc75
  · exact nativeAtomCalc76
  · exact nativeAtomCalc77
  · exact nativeAtomCalc78
  · exact nativeAtomCalc79
  · exact nativeAtomCalc80
  · exact nativeAtomCalc81
  · exact nativeAtomCalc82
  · exact nativeAtomCalc83
  · exact nativeAtomCalc84
  · exact nativeAtomCalc85
  · exact nativeAtomCalc86
  · exact nativeAtomCalc87
  · exact nativeAtomCalc88
  · exact nativeAtomCalc89
  · exact nativeAtomCalc90
  · exact nativeAtomCalc91
  · exact nativeAtomCalc92
  · exact nativeAtomCalc93
  · exact nativeAtomCalc94

theorem nativeDecodedRecords_source (codes : List ℕ) :
    decodeNativeRealRecords codes = nativeSourceRealTerms (decodeNativeSourceRecords codes) := by
  unfold decodeNativeRealRecords decodeNativeSourceRecords nativeSourceRealTerms
  simp only [List.map_map]
  apply List.map_congr_left
  intro code _
  dsimp only [Function.comp_apply]
  have counts := nativeRecordAtom_count
  rw [counts.1, counts.2]
  have atom := nativeRecordAtom_value ⟨code % 95, Nat.mod_lt _ (by decide)⟩
  exact congrArg (fun r : ℝ => (nativeRecordJet (code / 95 / 1445),
    nativeRecordJet (code / 95 % 1445), r)) atom.symm

theorem literalGravityTerms_source : literalGravityTerms = nativeSourceRealTerms nativeGravitySourceRecords := by
  rw [literalGravityTerms_decoded, nativeDecodedRecords_source]
  rfl

theorem literalGaugeTerms_source : literalGaugeTerms = nativeSourceRealTerms nativeGaugeSourceRecords := by
  rw [literalGaugeTerms_decoded, nativeDecodedRecords_source]
  rfl

theorem literalScalarTerms_source : literalScalarTerms = nativeSourceRealTerms nativeScalarSourceRecords := by
  rw [literalScalarTerms_decoded, nativeDecodedRecords_source]
  rfl

theorem literalDiracTerms_source : literalDiracTerms = nativeSourceRealTerms nativeDiracSourceRecords := by
  rw [literalDiracTerms_decoded, nativeDecodedRecords_source]
  rfl

end LowEnergy.SourcePropagationNativeActionHessian
