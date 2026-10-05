module

public import BecknerOnofri.EntropyScalarCertificate.Bessel0090
public import BecknerOnofri.EntropyScalarCertificate.Bessel0091
public import BecknerOnofri.EntropyScalarCertificate.Bessel0533
public import BecknerOnofri.EntropyScalarCertificate.Bessel0534
public import BecknerOnofri.EntropyScalarCertificate.Brackets0036
public import BecknerOnofri.EntropyScalarCertificate.Logs0072
public import BecknerOnofri.ScalarElementaryComposition
public import BecknerOnofri.ScalarGammaEnclosure
public import BecknerOnofri.ScalarLogBesselEndpoints

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0576
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0090.rows BesselBatch0090.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0090.rows BesselBatch0090.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0090.rows BesselBatch0090.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0090.rows BesselBatch0090.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0090.rows BesselBatch0090.accepted ⟨4,by decide⟩
]
theorem leftAccepted : besselPointCheck (217868634329401773931465339522536938389/1250000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (217868634329401773931465339522536938389/1250000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0090.rows BesselBatch0090.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0090.rows BesselBatch0090.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0090.rows BesselBatch0090.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0090.rows BesselBatch0090.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0090.rows BesselBatch0090.accepted ⟨19,by decide⟩
]
theorem rightAccepted : besselPointCheck (872520699140490562521955607427134222569/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (872520699140490562521955607427134222569/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0533.rows BesselBatch0533.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0533.rows BesselBatch0533.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0533.rows BesselBatch0533.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0533.rows BesselBatch0533.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0533.rows BesselBatch0533.accepted ⟨62,by decide⟩
]
theorem midAccepted : besselPointCheck (13951961891664781265982535724138255809/80000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (13951961891664781265982535724138255809/80000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0072.rows ScalarLogs0072.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0072.rows ScalarLogs0072.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0072.rows ScalarLogs0072.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0072.rows ScalarLogs0072.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0072.rows ScalarLogs0072.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0072.rows ScalarLogs0072.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0072.rows ScalarLogs0072.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0072.rows ScalarLogs0072.accepted ⟨7,by decide⟩
noncomputable def wholeH := identityFunctionEnclosure leftPoint.argument rightPoint.argument
noncomputable def wholeT := (firstMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeSecond := (secondMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeThird := (thirdMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeOne : FunctionEnclosure leftPoint.argument rightPoint.argument (fun _ => (1 : ℝ)) :=
  (FunctionEnclosure.const leftPoint.argument rightPoint.argument 1).congr (fun _ => Rat.cast_one)
noncomputable def wholeZ := logBesselEndpoints leftPoint rightPoint whole_zl whole_zu (by decide +kernel)
noncomputable def wholePlus := logCompose (wholeOne.radd wholeT) whole_pl whole_pu (by decide +kernel)
noncomputable def wholeMinus := logCompose (wholeOne.rsub wholeT) whole_ml whole_mu (by decide +kernel)
noncomputable def wholeW1lower := checkedWeightOfLog 1 wholeT.value.lower whole_wl (by decide +kernel)
noncomputable def wholeW1upper := checkedWeightOfLog 1 wholeT.value.upper whole_wu (by decide +kernel)
noncomputable def wholeW1 := (weightCompose wholeT 1 (by omega)
  wholeW1lower wholeW1upper (by decide +kernel)).round
noncomputable def wholeW2lower := checkedWeightOfLog 2 wholeT.value.lower whole_wl (by decide +kernel)
noncomputable def wholeW2upper := checkedWeightOfLog 2 wholeT.value.upper whole_wu (by decide +kernel)
noncomputable def wholeW2 := (weightCompose wholeT 2 (by omega)
  wholeW2lower wholeW2upper (by decide +kernel)).round
noncomputable def wholeBase := gammaBaseFunctionEnclosure wholeH wholeT wholeZ wholePlus wholeMinus
  (by decide +kernel) (by decide +kernel)
noncomputable def wholeData : GammaEnclosureData leftPoint.argument rightPoint.argument :=
  ⟨wholeBase,wholeT,wholeSecond,wholeThird,wholeW1,wholeW2⟩
theorem wholeDataAccepted : wholeData.check=true := by decide +kernel
noncomputable def wholeGamma := wholeData.enclosure wholeDataAccepted
def point_wl := checkedLogOfRows ScalarLogs0072.rows ScalarLogs0072.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0072.rows ScalarLogs0072.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0072.rows ScalarLogs0072.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0072.rows ScalarLogs0072.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0072.rows ScalarLogs0072.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0072.rows ScalarLogs0072.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0072.rows ScalarLogs0072.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0072.rows ScalarLogs0072.accepted ⟨15,by decide⟩
noncomputable def pointH := identityFunctionEnclosure midPoint.argument midPoint.argument
noncomputable def pointT := (firstMomentEnclosure midPoint midPoint).round
noncomputable def pointSecond := (secondMomentEnclosure midPoint midPoint).round
noncomputable def pointThird := (thirdMomentEnclosure midPoint midPoint).round
noncomputable def pointOne : FunctionEnclosure midPoint.argument midPoint.argument (fun _ => (1 : ℝ)) :=
  (FunctionEnclosure.const midPoint.argument midPoint.argument 1).congr (fun _ => Rat.cast_one)
noncomputable def pointZ := logBesselEndpoints midPoint midPoint point_zl point_zu (by decide +kernel)
noncomputable def pointPlus := logCompose (pointOne.radd pointT) point_pl point_pu (by decide +kernel)
noncomputable def pointMinus := logCompose (pointOne.rsub pointT) point_ml point_mu (by decide +kernel)
noncomputable def pointW1lower := checkedWeightOfLog 1 pointT.value.lower point_wl (by decide +kernel)
noncomputable def pointW1upper := checkedWeightOfLog 1 pointT.value.upper point_wu (by decide +kernel)
noncomputable def pointW1 := (weightCompose pointT 1 (by omega)
  pointW1lower pointW1upper (by decide +kernel)).round
noncomputable def pointW2lower := checkedWeightOfLog 2 pointT.value.lower point_wl (by decide +kernel)
noncomputable def pointW2upper := checkedWeightOfLog 2 pointT.value.upper point_wu (by decide +kernel)
noncomputable def pointW2 := (weightCompose pointT 2 (by omega)
  pointW2lower pointW2upper (by decide +kernel)).round
noncomputable def pointBase := gammaBaseFunctionEnclosure pointH pointT pointZ pointPlus pointMinus
  (by decide +kernel) (by decide +kernel)
noncomputable def pointData : GammaEnclosureData midPoint.argument midPoint.argument :=
  ⟨pointBase,pointT,pointSecond,pointThird,pointW1,pointW2⟩
theorem pointDataAccepted : pointData.check=true := by decide +kernel
noncomputable def pointGamma := pointData.enclosure pointDataAccepted
theorem panelAccepted : gammaPanelCheck BracketBatch0036.bracket0576 BracketBatch0036.bracket0577 (13951961891664781265982535724138255809/80000000000000000000000000000000000000) (684807622401378767167228284419142663/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0036.bracket0576 BracketBatch0036.bracket0577
  (13951961891664781265982535724138255809/80000000000000000000000000000000000000) (684807622401378767167228284419142663/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0576
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0577
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0090.rows BesselBatch0090.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0090.rows BesselBatch0090.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0090.rows BesselBatch0090.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0090.rows BesselBatch0090.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0090.rows BesselBatch0090.accepted ⟨14,by decide⟩
]
theorem leftAccepted : besselPointCheck (349008279656196225008782242970853689027/2000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (349008279656196225008782242970853689027/2000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0090.rows BesselBatch0090.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0090.rows BesselBatch0090.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0090.rows BesselBatch0090.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0090.rows BesselBatch0090.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0090.rows BesselBatch0090.accepted ⟨29,by decide⟩
]
theorem rightAccepted : besselPointCheck (1747133946190060737088072990583733558969/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1747133946190060737088072990583733558969/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0533.rows BesselBatch0533.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0534.rows BesselBatch0534.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0534.rows BesselBatch0534.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0534.rows BesselBatch0534.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0534.rows BesselBatch0534.accepted ⟨3,by decide⟩
]
theorem midAccepted : besselPointCheck (436521918058880232766498025679750250513/2500000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (436521918058880232766498025679750250513/2500000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0072.rows ScalarLogs0072.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0072.rows ScalarLogs0072.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0072.rows ScalarLogs0072.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0072.rows ScalarLogs0072.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0072.rows ScalarLogs0072.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0072.rows ScalarLogs0072.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0072.rows ScalarLogs0072.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0072.rows ScalarLogs0072.accepted ⟨23,by decide⟩
noncomputable def wholeH := identityFunctionEnclosure leftPoint.argument rightPoint.argument
noncomputable def wholeT := (firstMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeSecond := (secondMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeThird := (thirdMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeOne : FunctionEnclosure leftPoint.argument rightPoint.argument (fun _ => (1 : ℝ)) :=
  (FunctionEnclosure.const leftPoint.argument rightPoint.argument 1).congr (fun _ => Rat.cast_one)
noncomputable def wholeZ := logBesselEndpoints leftPoint rightPoint whole_zl whole_zu (by decide +kernel)
noncomputable def wholePlus := logCompose (wholeOne.radd wholeT) whole_pl whole_pu (by decide +kernel)
noncomputable def wholeMinus := logCompose (wholeOne.rsub wholeT) whole_ml whole_mu (by decide +kernel)
noncomputable def wholeW1lower := checkedWeightOfLog 1 wholeT.value.lower whole_wl (by decide +kernel)
noncomputable def wholeW1upper := checkedWeightOfLog 1 wholeT.value.upper whole_wu (by decide +kernel)
noncomputable def wholeW1 := (weightCompose wholeT 1 (by omega)
  wholeW1lower wholeW1upper (by decide +kernel)).round
noncomputable def wholeW2lower := checkedWeightOfLog 2 wholeT.value.lower whole_wl (by decide +kernel)
noncomputable def wholeW2upper := checkedWeightOfLog 2 wholeT.value.upper whole_wu (by decide +kernel)
noncomputable def wholeW2 := (weightCompose wholeT 2 (by omega)
  wholeW2lower wholeW2upper (by decide +kernel)).round
noncomputable def wholeBase := gammaBaseFunctionEnclosure wholeH wholeT wholeZ wholePlus wholeMinus
  (by decide +kernel) (by decide +kernel)
noncomputable def wholeData : GammaEnclosureData leftPoint.argument rightPoint.argument :=
  ⟨wholeBase,wholeT,wholeSecond,wholeThird,wholeW1,wholeW2⟩
theorem wholeDataAccepted : wholeData.check=true := by decide +kernel
noncomputable def wholeGamma := wholeData.enclosure wholeDataAccepted
def point_wl := checkedLogOfRows ScalarLogs0072.rows ScalarLogs0072.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0072.rows ScalarLogs0072.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0072.rows ScalarLogs0072.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0072.rows ScalarLogs0072.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0072.rows ScalarLogs0072.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0072.rows ScalarLogs0072.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0072.rows ScalarLogs0072.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0072.rows ScalarLogs0072.accepted ⟨31,by decide⟩
noncomputable def pointH := identityFunctionEnclosure midPoint.argument midPoint.argument
noncomputable def pointT := (firstMomentEnclosure midPoint midPoint).round
noncomputable def pointSecond := (secondMomentEnclosure midPoint midPoint).round
noncomputable def pointThird := (thirdMomentEnclosure midPoint midPoint).round
noncomputable def pointOne : FunctionEnclosure midPoint.argument midPoint.argument (fun _ => (1 : ℝ)) :=
  (FunctionEnclosure.const midPoint.argument midPoint.argument 1).congr (fun _ => Rat.cast_one)
noncomputable def pointZ := logBesselEndpoints midPoint midPoint point_zl point_zu (by decide +kernel)
noncomputable def pointPlus := logCompose (pointOne.radd pointT) point_pl point_pu (by decide +kernel)
noncomputable def pointMinus := logCompose (pointOne.rsub pointT) point_ml point_mu (by decide +kernel)
noncomputable def pointW1lower := checkedWeightOfLog 1 pointT.value.lower point_wl (by decide +kernel)
noncomputable def pointW1upper := checkedWeightOfLog 1 pointT.value.upper point_wu (by decide +kernel)
noncomputable def pointW1 := (weightCompose pointT 1 (by omega)
  pointW1lower pointW1upper (by decide +kernel)).round
noncomputable def pointW2lower := checkedWeightOfLog 2 pointT.value.lower point_wl (by decide +kernel)
noncomputable def pointW2upper := checkedWeightOfLog 2 pointT.value.upper point_wu (by decide +kernel)
noncomputable def pointW2 := (weightCompose pointT 2 (by omega)
  pointW2lower pointW2upper (by decide +kernel)).round
noncomputable def pointBase := gammaBaseFunctionEnclosure pointH pointT pointZ pointPlus pointMinus
  (by decide +kernel) (by decide +kernel)
noncomputable def pointData : GammaEnclosureData midPoint.argument midPoint.argument :=
  ⟨pointBase,pointT,pointSecond,pointThird,pointW1,pointW2⟩
theorem pointDataAccepted : pointData.check=true := by decide +kernel
noncomputable def pointGamma := pointData.enclosure pointDataAccepted
theorem panelAccepted : gammaPanelCheck BracketBatch0036.bracket0577 BracketBatch0036.bracket0578 (436521918058880232766498025679750250513/2500000000000000000000000000000000000000) (172006307440397938608613677884865977/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0036.bracket0577 BracketBatch0036.bracket0578
  (436521918058880232766498025679750250513/2500000000000000000000000000000000000000) (172006307440397938608613677884865977/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0577
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0578
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0090.rows BesselBatch0090.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0090.rows BesselBatch0090.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0090.rows BesselBatch0090.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0090.rows BesselBatch0090.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0090.rows BesselBatch0090.accepted ⟨24,by decide⟩
]
theorem leftAccepted : besselPointCheck (873566973095030368544036495291866779483/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (873566973095030368544036495291866779483/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0090.rows BesselBatch0090.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0090.rows BesselBatch0090.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0090.rows BesselBatch0090.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0090.rows BesselBatch0090.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0090.rows BesselBatch0090.accepted ⟨39,by decide⟩
]
theorem rightAccepted : besselPointCheck (1749226718667882162937493137697304224901/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1749226718667882162937493137697304224901/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0534.rows BesselBatch0534.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0534.rows BesselBatch0534.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0534.rows BesselBatch0534.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0534.rows BesselBatch0534.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0534.rows BesselBatch0534.accepted ⟨8,by decide⟩
]
theorem midAccepted : besselPointCheck (3496360664857942900025566128281037783867/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (3496360664857942900025566128281037783867/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0072.rows ScalarLogs0072.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0072.rows ScalarLogs0072.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0072.rows ScalarLogs0072.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0072.rows ScalarLogs0072.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0072.rows ScalarLogs0072.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0072.rows ScalarLogs0072.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0072.rows ScalarLogs0072.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0072.rows ScalarLogs0072.accepted ⟨39,by decide⟩
noncomputable def wholeH := identityFunctionEnclosure leftPoint.argument rightPoint.argument
noncomputable def wholeT := (firstMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeSecond := (secondMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeThird := (thirdMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeOne : FunctionEnclosure leftPoint.argument rightPoint.argument (fun _ => (1 : ℝ)) :=
  (FunctionEnclosure.const leftPoint.argument rightPoint.argument 1).congr (fun _ => Rat.cast_one)
noncomputable def wholeZ := logBesselEndpoints leftPoint rightPoint whole_zl whole_zu (by decide +kernel)
noncomputable def wholePlus := logCompose (wholeOne.radd wholeT) whole_pl whole_pu (by decide +kernel)
noncomputable def wholeMinus := logCompose (wholeOne.rsub wholeT) whole_ml whole_mu (by decide +kernel)
noncomputable def wholeW1lower := checkedWeightOfLog 1 wholeT.value.lower whole_wl (by decide +kernel)
noncomputable def wholeW1upper := checkedWeightOfLog 1 wholeT.value.upper whole_wu (by decide +kernel)
noncomputable def wholeW1 := (weightCompose wholeT 1 (by omega)
  wholeW1lower wholeW1upper (by decide +kernel)).round
noncomputable def wholeW2lower := checkedWeightOfLog 2 wholeT.value.lower whole_wl (by decide +kernel)
noncomputable def wholeW2upper := checkedWeightOfLog 2 wholeT.value.upper whole_wu (by decide +kernel)
noncomputable def wholeW2 := (weightCompose wholeT 2 (by omega)
  wholeW2lower wholeW2upper (by decide +kernel)).round
noncomputable def wholeBase := gammaBaseFunctionEnclosure wholeH wholeT wholeZ wholePlus wholeMinus
  (by decide +kernel) (by decide +kernel)
noncomputable def wholeData : GammaEnclosureData leftPoint.argument rightPoint.argument :=
  ⟨wholeBase,wholeT,wholeSecond,wholeThird,wholeW1,wholeW2⟩
theorem wholeDataAccepted : wholeData.check=true := by decide +kernel
noncomputable def wholeGamma := wholeData.enclosure wholeDataAccepted
def point_wl := checkedLogOfRows ScalarLogs0072.rows ScalarLogs0072.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0072.rows ScalarLogs0072.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0072.rows ScalarLogs0072.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0072.rows ScalarLogs0072.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0072.rows ScalarLogs0072.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0072.rows ScalarLogs0072.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0072.rows ScalarLogs0072.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0072.rows ScalarLogs0072.accepted ⟨47,by decide⟩
noncomputable def pointH := identityFunctionEnclosure midPoint.argument midPoint.argument
noncomputable def pointT := (firstMomentEnclosure midPoint midPoint).round
noncomputable def pointSecond := (secondMomentEnclosure midPoint midPoint).round
noncomputable def pointThird := (thirdMomentEnclosure midPoint midPoint).round
noncomputable def pointOne : FunctionEnclosure midPoint.argument midPoint.argument (fun _ => (1 : ℝ)) :=
  (FunctionEnclosure.const midPoint.argument midPoint.argument 1).congr (fun _ => Rat.cast_one)
noncomputable def pointZ := logBesselEndpoints midPoint midPoint point_zl point_zu (by decide +kernel)
noncomputable def pointPlus := logCompose (pointOne.radd pointT) point_pl point_pu (by decide +kernel)
noncomputable def pointMinus := logCompose (pointOne.rsub pointT) point_ml point_mu (by decide +kernel)
noncomputable def pointW1lower := checkedWeightOfLog 1 pointT.value.lower point_wl (by decide +kernel)
noncomputable def pointW1upper := checkedWeightOfLog 1 pointT.value.upper point_wu (by decide +kernel)
noncomputable def pointW1 := (weightCompose pointT 1 (by omega)
  pointW1lower pointW1upper (by decide +kernel)).round
noncomputable def pointW2lower := checkedWeightOfLog 2 pointT.value.lower point_wl (by decide +kernel)
noncomputable def pointW2upper := checkedWeightOfLog 2 pointT.value.upper point_wu (by decide +kernel)
noncomputable def pointW2 := (weightCompose pointT 2 (by omega)
  pointW2lower pointW2upper (by decide +kernel)).round
noncomputable def pointBase := gammaBaseFunctionEnclosure pointH pointT pointZ pointPlus pointMinus
  (by decide +kernel) (by decide +kernel)
noncomputable def pointData : GammaEnclosureData midPoint.argument midPoint.argument :=
  ⟨pointBase,pointT,pointSecond,pointThird,pointW1,pointW2⟩
theorem pointDataAccepted : pointData.check=true := by decide +kernel
noncomputable def pointGamma := pointData.enclosure pointDataAccepted
theorem panelAccepted : gammaPanelCheck BracketBatch0036.bracket0578 BracketBatch0036.bracket0579 (3496360664857942900025566128281037783867/20000000000000000000000000000000000000000) (691254224708029205422018213072080283/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0036.bracket0578 BracketBatch0036.bracket0579
  (3496360664857942900025566128281037783867/20000000000000000000000000000000000000000) (691254224708029205422018213072080283/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0578
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0579
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0090.rows BesselBatch0090.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0090.rows BesselBatch0090.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0090.rows BesselBatch0090.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0090.rows BesselBatch0090.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0090.rows BesselBatch0090.accepted ⟨34,by decide⟩
]
theorem leftAccepted : besselPointCheck (874613359333941081468746568848652112449/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (874613359333941081468746568848652112449/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0090.rows BesselBatch0090.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0090.rows BesselBatch0090.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0090.rows BesselBatch0090.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0090.rows BesselBatch0090.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0090.rows BesselBatch0090.accepted ⟨49,by decide⟩
]
theorem rightAccepted : besselPointCheck (350263943204008497195487421202838099969/2000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (350263943204008497195487421202838099969/2000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0534.rows BesselBatch0534.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0534.rows BesselBatch0534.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0534.rows BesselBatch0534.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0534.rows BesselBatch0534.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0534.rows BesselBatch0534.accepted ⟨13,by decide⟩
]
theorem midAccepted : besselPointCheck (3500546434687924648914930243711494724743/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (3500546434687924648914930243711494724743/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0072.rows ScalarLogs0072.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0072.rows ScalarLogs0072.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0072.rows ScalarLogs0072.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0072.rows ScalarLogs0072.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0072.rows ScalarLogs0072.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0072.rows ScalarLogs0072.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0072.rows ScalarLogs0072.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0072.rows ScalarLogs0072.accepted ⟨55,by decide⟩
noncomputable def wholeH := identityFunctionEnclosure leftPoint.argument rightPoint.argument
noncomputable def wholeT := (firstMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeSecond := (secondMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeThird := (thirdMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeOne : FunctionEnclosure leftPoint.argument rightPoint.argument (fun _ => (1 : ℝ)) :=
  (FunctionEnclosure.const leftPoint.argument rightPoint.argument 1).congr (fun _ => Rat.cast_one)
noncomputable def wholeZ := logBesselEndpoints leftPoint rightPoint whole_zl whole_zu (by decide +kernel)
noncomputable def wholePlus := logCompose (wholeOne.radd wholeT) whole_pl whole_pu (by decide +kernel)
noncomputable def wholeMinus := logCompose (wholeOne.rsub wholeT) whole_ml whole_mu (by decide +kernel)
noncomputable def wholeW1lower := checkedWeightOfLog 1 wholeT.value.lower whole_wl (by decide +kernel)
noncomputable def wholeW1upper := checkedWeightOfLog 1 wholeT.value.upper whole_wu (by decide +kernel)
noncomputable def wholeW1 := (weightCompose wholeT 1 (by omega)
  wholeW1lower wholeW1upper (by decide +kernel)).round
noncomputable def wholeW2lower := checkedWeightOfLog 2 wholeT.value.lower whole_wl (by decide +kernel)
noncomputable def wholeW2upper := checkedWeightOfLog 2 wholeT.value.upper whole_wu (by decide +kernel)
noncomputable def wholeW2 := (weightCompose wholeT 2 (by omega)
  wholeW2lower wholeW2upper (by decide +kernel)).round
noncomputable def wholeBase := gammaBaseFunctionEnclosure wholeH wholeT wholeZ wholePlus wholeMinus
  (by decide +kernel) (by decide +kernel)
noncomputable def wholeData : GammaEnclosureData leftPoint.argument rightPoint.argument :=
  ⟨wholeBase,wholeT,wholeSecond,wholeThird,wholeW1,wholeW2⟩
theorem wholeDataAccepted : wholeData.check=true := by decide +kernel
noncomputable def wholeGamma := wholeData.enclosure wholeDataAccepted
def point_wl := checkedLogOfRows ScalarLogs0072.rows ScalarLogs0072.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0072.rows ScalarLogs0072.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0072.rows ScalarLogs0072.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0072.rows ScalarLogs0072.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0072.rows ScalarLogs0072.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0072.rows ScalarLogs0072.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0072.rows ScalarLogs0072.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0072.rows ScalarLogs0072.accepted ⟨63,by decide⟩
noncomputable def pointH := identityFunctionEnclosure midPoint.argument midPoint.argument
noncomputable def pointT := (firstMomentEnclosure midPoint midPoint).round
noncomputable def pointSecond := (secondMomentEnclosure midPoint midPoint).round
noncomputable def pointThird := (thirdMomentEnclosure midPoint midPoint).round
noncomputable def pointOne : FunctionEnclosure midPoint.argument midPoint.argument (fun _ => (1 : ℝ)) :=
  (FunctionEnclosure.const midPoint.argument midPoint.argument 1).congr (fun _ => Rat.cast_one)
noncomputable def pointZ := logBesselEndpoints midPoint midPoint point_zl point_zu (by decide +kernel)
noncomputable def pointPlus := logCompose (pointOne.radd pointT) point_pl point_pu (by decide +kernel)
noncomputable def pointMinus := logCompose (pointOne.rsub pointT) point_ml point_mu (by decide +kernel)
noncomputable def pointW1lower := checkedWeightOfLog 1 pointT.value.lower point_wl (by decide +kernel)
noncomputable def pointW1upper := checkedWeightOfLog 1 pointT.value.upper point_wu (by decide +kernel)
noncomputable def pointW1 := (weightCompose pointT 1 (by omega)
  pointW1lower pointW1upper (by decide +kernel)).round
noncomputable def pointW2lower := checkedWeightOfLog 2 pointT.value.lower point_wl (by decide +kernel)
noncomputable def pointW2upper := checkedWeightOfLog 2 pointT.value.upper point_wu (by decide +kernel)
noncomputable def pointW2 := (weightCompose pointT 2 (by omega)
  pointW2lower pointW2upper (by decide +kernel)).round
noncomputable def pointBase := gammaBaseFunctionEnclosure pointH pointT pointZ pointPlus pointMinus
  (by decide +kernel) (by decide +kernel)
noncomputable def pointData : GammaEnclosureData midPoint.argument midPoint.argument :=
  ⟨pointBase,pointT,pointSecond,pointThird,pointW1,pointW2⟩
theorem pointDataAccepted : pointData.check=true := by decide +kernel
noncomputable def pointGamma := pointData.enclosure pointDataAccepted
theorem panelAccepted : gammaPanelCheck BracketBatch0036.bracket0579 BracketBatch0036.bracket0580 (3500546434687924648914930243711494724743/20000000000000000000000000000000000000000) (138898926913515160517976358797469809/2000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0036.bracket0579 BracketBatch0036.bracket0580
  (3500546434687924648914930243711494724743/20000000000000000000000000000000000000000) (138898926913515160517976358797469809/2000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0579
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0580
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0090.rows BesselBatch0090.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0090.rows BesselBatch0090.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0090.rows BesselBatch0090.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0090.rows BesselBatch0090.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0090.rows BesselBatch0090.accepted ⟨44,by decide⟩
]
theorem leftAccepted : besselPointCheck (875659858010021242988718553007095249921/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (875659858010021242988718553007095249921/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0090.rows BesselBatch0090.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0090.rows BesselBatch0090.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0090.rows BesselBatch0090.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0090.rows BesselBatch0090.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0090.rows BesselBatch0090.accepted ⟨59,by decide⟩
]
theorem rightAccepted : besselPointCheck (1753412938552307011246831517777273023401/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1753412938552307011246831517777273023401/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0534.rows BesselBatch0534.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0534.rows BesselBatch0534.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0534.rows BesselBatch0534.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0534.rows BesselBatch0534.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0534.rows BesselBatch0534.accepted ⟨18,by decide⟩
]
theorem midAccepted : besselPointCheck (3504732654572349497224268623791463523243/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (3504732654572349497224268623791463523243/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0072.rows ScalarLogs0072.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0072.rows ScalarLogs0072.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0072.rows ScalarLogs0072.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0072.rows ScalarLogs0072.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0072.rows ScalarLogs0072.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0072.rows ScalarLogs0072.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0072.rows ScalarLogs0072.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0072.rows ScalarLogs0072.accepted ⟨71,by decide⟩
noncomputable def wholeH := identityFunctionEnclosure leftPoint.argument rightPoint.argument
noncomputable def wholeT := (firstMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeSecond := (secondMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeThird := (thirdMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeOne : FunctionEnclosure leftPoint.argument rightPoint.argument (fun _ => (1 : ℝ)) :=
  (FunctionEnclosure.const leftPoint.argument rightPoint.argument 1).congr (fun _ => Rat.cast_one)
noncomputable def wholeZ := logBesselEndpoints leftPoint rightPoint whole_zl whole_zu (by decide +kernel)
noncomputable def wholePlus := logCompose (wholeOne.radd wholeT) whole_pl whole_pu (by decide +kernel)
noncomputable def wholeMinus := logCompose (wholeOne.rsub wholeT) whole_ml whole_mu (by decide +kernel)
noncomputable def wholeW1lower := checkedWeightOfLog 1 wholeT.value.lower whole_wl (by decide +kernel)
noncomputable def wholeW1upper := checkedWeightOfLog 1 wholeT.value.upper whole_wu (by decide +kernel)
noncomputable def wholeW1 := (weightCompose wholeT 1 (by omega)
  wholeW1lower wholeW1upper (by decide +kernel)).round
noncomputable def wholeW2lower := checkedWeightOfLog 2 wholeT.value.lower whole_wl (by decide +kernel)
noncomputable def wholeW2upper := checkedWeightOfLog 2 wholeT.value.upper whole_wu (by decide +kernel)
noncomputable def wholeW2 := (weightCompose wholeT 2 (by omega)
  wholeW2lower wholeW2upper (by decide +kernel)).round
noncomputable def wholeBase := gammaBaseFunctionEnclosure wholeH wholeT wholeZ wholePlus wholeMinus
  (by decide +kernel) (by decide +kernel)
noncomputable def wholeData : GammaEnclosureData leftPoint.argument rightPoint.argument :=
  ⟨wholeBase,wholeT,wholeSecond,wholeThird,wholeW1,wholeW2⟩
theorem wholeDataAccepted : wholeData.check=true := by decide +kernel
noncomputable def wholeGamma := wholeData.enclosure wholeDataAccepted
def point_wl := checkedLogOfRows ScalarLogs0072.rows ScalarLogs0072.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0072.rows ScalarLogs0072.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0072.rows ScalarLogs0072.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0072.rows ScalarLogs0072.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0072.rows ScalarLogs0072.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0072.rows ScalarLogs0072.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0072.rows ScalarLogs0072.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0072.rows ScalarLogs0072.accepted ⟨79,by decide⟩
noncomputable def pointH := identityFunctionEnclosure midPoint.argument midPoint.argument
noncomputable def pointT := (firstMomentEnclosure midPoint midPoint).round
noncomputable def pointSecond := (secondMomentEnclosure midPoint midPoint).round
noncomputable def pointThird := (thirdMomentEnclosure midPoint midPoint).round
noncomputable def pointOne : FunctionEnclosure midPoint.argument midPoint.argument (fun _ => (1 : ℝ)) :=
  (FunctionEnclosure.const midPoint.argument midPoint.argument 1).congr (fun _ => Rat.cast_one)
noncomputable def pointZ := logBesselEndpoints midPoint midPoint point_zl point_zu (by decide +kernel)
noncomputable def pointPlus := logCompose (pointOne.radd pointT) point_pl point_pu (by decide +kernel)
noncomputable def pointMinus := logCompose (pointOne.rsub pointT) point_ml point_mu (by decide +kernel)
noncomputable def pointW1lower := checkedWeightOfLog 1 pointT.value.lower point_wl (by decide +kernel)
noncomputable def pointW1upper := checkedWeightOfLog 1 pointT.value.upper point_wu (by decide +kernel)
noncomputable def pointW1 := (weightCompose pointT 1 (by omega)
  pointW1lower pointW1upper (by decide +kernel)).round
noncomputable def pointW2lower := checkedWeightOfLog 2 pointT.value.lower point_wl (by decide +kernel)
noncomputable def pointW2upper := checkedWeightOfLog 2 pointT.value.upper point_wu (by decide +kernel)
noncomputable def pointW2 := (weightCompose pointT 2 (by omega)
  pointW2lower pointW2upper (by decide +kernel)).round
noncomputable def pointBase := gammaBaseFunctionEnclosure pointH pointT pointZ pointPlus pointMinus
  (by decide +kernel) (by decide +kernel)
noncomputable def pointData : GammaEnclosureData midPoint.argument midPoint.argument :=
  ⟨pointBase,pointT,pointSecond,pointThird,pointW1,pointW2⟩
theorem pointDataAccepted : pointData.check=true := by decide +kernel
noncomputable def pointGamma := pointData.enclosure pointDataAccepted
theorem panelAccepted : gammaPanelCheck BracketBatch0036.bracket0580 BracketBatch0036.bracket0581 (3504732654572349497224268623791463523243/20000000000000000000000000000000000000000) (69774648670280190573752304449095223/1000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0036.bracket0580 BracketBatch0036.bracket0581
  (3504732654572349497224268623791463523243/20000000000000000000000000000000000000000) (69774648670280190573752304449095223/1000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0580
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0581
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0090.rows BesselBatch0090.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0090.rows BesselBatch0090.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0090.rows BesselBatch0090.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0090.rows BesselBatch0090.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0090.rows BesselBatch0090.accepted ⟨54,by decide⟩
]
theorem leftAccepted : besselPointCheck (876706469276153505623415758888636511699/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (876706469276153505623415758888636511699/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0091.rows BesselBatch0091.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0091.rows BesselBatch0091.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0091.rows BesselBatch0091.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0091.rows BesselBatch0091.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0091.rows BesselBatch0091.accepted ⟨5,by decide⟩
]
theorem rightAccepted : besselPointCheck (1755506386570609539373499061802669919513/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1755506386570609539373499061802669919513/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0534.rows BesselBatch0534.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0534.rows BesselBatch0534.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0534.rows BesselBatch0534.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0534.rows BesselBatch0534.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0534.rows BesselBatch0534.accepted ⟨23,by decide⟩
]
theorem midAccepted : besselPointCheck (3508919325122916550620330579579942942911/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (3508919325122916550620330579579942942911/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0072.rows ScalarLogs0072.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0072.rows ScalarLogs0072.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0072.rows ScalarLogs0072.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0072.rows ScalarLogs0072.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0072.rows ScalarLogs0072.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0072.rows ScalarLogs0072.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0072.rows ScalarLogs0072.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0072.rows ScalarLogs0072.accepted ⟨87,by decide⟩
noncomputable def wholeH := identityFunctionEnclosure leftPoint.argument rightPoint.argument
noncomputable def wholeT := (firstMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeSecond := (secondMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeThird := (thirdMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeOne : FunctionEnclosure leftPoint.argument rightPoint.argument (fun _ => (1 : ℝ)) :=
  (FunctionEnclosure.const leftPoint.argument rightPoint.argument 1).congr (fun _ => Rat.cast_one)
noncomputable def wholeZ := logBesselEndpoints leftPoint rightPoint whole_zl whole_zu (by decide +kernel)
noncomputable def wholePlus := logCompose (wholeOne.radd wholeT) whole_pl whole_pu (by decide +kernel)
noncomputable def wholeMinus := logCompose (wholeOne.rsub wholeT) whole_ml whole_mu (by decide +kernel)
noncomputable def wholeW1lower := checkedWeightOfLog 1 wholeT.value.lower whole_wl (by decide +kernel)
noncomputable def wholeW1upper := checkedWeightOfLog 1 wholeT.value.upper whole_wu (by decide +kernel)
noncomputable def wholeW1 := (weightCompose wholeT 1 (by omega)
  wholeW1lower wholeW1upper (by decide +kernel)).round
noncomputable def wholeW2lower := checkedWeightOfLog 2 wholeT.value.lower whole_wl (by decide +kernel)
noncomputable def wholeW2upper := checkedWeightOfLog 2 wholeT.value.upper whole_wu (by decide +kernel)
noncomputable def wholeW2 := (weightCompose wholeT 2 (by omega)
  wholeW2lower wholeW2upper (by decide +kernel)).round
noncomputable def wholeBase := gammaBaseFunctionEnclosure wholeH wholeT wholeZ wholePlus wholeMinus
  (by decide +kernel) (by decide +kernel)
noncomputable def wholeData : GammaEnclosureData leftPoint.argument rightPoint.argument :=
  ⟨wholeBase,wholeT,wholeSecond,wholeThird,wholeW1,wholeW2⟩
theorem wholeDataAccepted : wholeData.check=true := by decide +kernel
noncomputable def wholeGamma := wholeData.enclosure wholeDataAccepted
def point_wl := checkedLogOfRows ScalarLogs0072.rows ScalarLogs0072.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0072.rows ScalarLogs0072.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0072.rows ScalarLogs0072.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0072.rows ScalarLogs0072.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0072.rows ScalarLogs0072.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0072.rows ScalarLogs0072.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0072.rows ScalarLogs0072.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0072.rows ScalarLogs0072.accepted ⟨95,by decide⟩
noncomputable def pointH := identityFunctionEnclosure midPoint.argument midPoint.argument
noncomputable def pointT := (firstMomentEnclosure midPoint midPoint).round
noncomputable def pointSecond := (secondMomentEnclosure midPoint midPoint).round
noncomputable def pointThird := (thirdMomentEnclosure midPoint midPoint).round
noncomputable def pointOne : FunctionEnclosure midPoint.argument midPoint.argument (fun _ => (1 : ℝ)) :=
  (FunctionEnclosure.const midPoint.argument midPoint.argument 1).congr (fun _ => Rat.cast_one)
noncomputable def pointZ := logBesselEndpoints midPoint midPoint point_zl point_zu (by decide +kernel)
noncomputable def pointPlus := logCompose (pointOne.radd pointT) point_pl point_pu (by decide +kernel)
noncomputable def pointMinus := logCompose (pointOne.rsub pointT) point_ml point_mu (by decide +kernel)
noncomputable def pointW1lower := checkedWeightOfLog 1 pointT.value.lower point_wl (by decide +kernel)
noncomputable def pointW1upper := checkedWeightOfLog 1 pointT.value.upper point_wu (by decide +kernel)
noncomputable def pointW1 := (weightCompose pointT 1 (by omega)
  pointW1lower pointW1upper (by decide +kernel)).round
noncomputable def pointW2lower := checkedWeightOfLog 2 pointT.value.lower point_wl (by decide +kernel)
noncomputable def pointW2upper := checkedWeightOfLog 2 pointT.value.upper point_wu (by decide +kernel)
noncomputable def pointW2 := (weightCompose pointT 2 (by omega)
  pointW2lower pointW2upper (by decide +kernel)).round
noncomputable def pointBase := gammaBaseFunctionEnclosure pointH pointT pointZ pointPlus pointMinus
  (by decide +kernel) (by decide +kernel)
noncomputable def pointData : GammaEnclosureData midPoint.argument midPoint.argument :=
  ⟨pointBase,pointT,pointSecond,pointThird,pointW1,pointW2⟩
theorem pointDataAccepted : pointData.check=true := by decide +kernel
noncomputable def pointGamma := pointData.enclosure pointDataAccepted
theorem panelAccepted : gammaPanelCheck BracketBatch0036.bracket0581 BracketBatch0036.bracket0582 (3508919325122916550620330579579942942911/20000000000000000000000000000000000000000) (5608078468095824815143443232368093/80000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0036.bracket0581 BracketBatch0036.bracket0582
  (3508919325122916550620330579579942942911/20000000000000000000000000000000000000000) (5608078468095824815143443232368093/80000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0581
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0582
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0090.rows BesselBatch0090.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0090.rows BesselBatch0090.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0090.rows BesselBatch0090.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0090.rows BesselBatch0090.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0091.rows BesselBatch0091.accepted ⟨0,by decide⟩
]
theorem leftAccepted : besselPointCheck (175550638657060953937349906180266991951/1000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (175550638657060953937349906180266991951/1000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0091.rows BesselBatch0091.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0091.rows BesselBatch0091.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0091.rows BesselBatch0091.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0091.rows BesselBatch0091.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0091.rows BesselBatch0091.accepted ⟨15,by decide⟩
]
theorem rightAccepted : besselPointCheck (1757600060381052640823568074815766981871/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1757600060381052640823568074815766981871/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0534.rows BesselBatch0534.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0534.rows BesselBatch0534.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0534.rows BesselBatch0534.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0534.rows BesselBatch0534.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0534.rows BesselBatch0534.accepted ⟨28,by decide⟩
]
theorem midAccepted : besselPointCheck (3513106446951662180197067136618436901381/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (3513106446951662180197067136618436901381/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0072.rows ScalarLogs0072.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0072.rows ScalarLogs0072.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0072.rows ScalarLogs0072.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0072.rows ScalarLogs0072.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0072.rows ScalarLogs0072.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0072.rows ScalarLogs0072.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0072.rows ScalarLogs0072.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0072.rows ScalarLogs0072.accepted ⟨103,by decide⟩
noncomputable def wholeH := identityFunctionEnclosure leftPoint.argument rightPoint.argument
noncomputable def wholeT := (firstMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeSecond := (secondMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeThird := (thirdMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeOne : FunctionEnclosure leftPoint.argument rightPoint.argument (fun _ => (1 : ℝ)) :=
  (FunctionEnclosure.const leftPoint.argument rightPoint.argument 1).congr (fun _ => Rat.cast_one)
noncomputable def wholeZ := logBesselEndpoints leftPoint rightPoint whole_zl whole_zu (by decide +kernel)
noncomputable def wholePlus := logCompose (wholeOne.radd wholeT) whole_pl whole_pu (by decide +kernel)
noncomputable def wholeMinus := logCompose (wholeOne.rsub wholeT) whole_ml whole_mu (by decide +kernel)
noncomputable def wholeW1lower := checkedWeightOfLog 1 wholeT.value.lower whole_wl (by decide +kernel)
noncomputable def wholeW1upper := checkedWeightOfLog 1 wholeT.value.upper whole_wu (by decide +kernel)
noncomputable def wholeW1 := (weightCompose wholeT 1 (by omega)
  wholeW1lower wholeW1upper (by decide +kernel)).round
noncomputable def wholeW2lower := checkedWeightOfLog 2 wholeT.value.lower whole_wl (by decide +kernel)
noncomputable def wholeW2upper := checkedWeightOfLog 2 wholeT.value.upper whole_wu (by decide +kernel)
noncomputable def wholeW2 := (weightCompose wholeT 2 (by omega)
  wholeW2lower wholeW2upper (by decide +kernel)).round
noncomputable def wholeBase := gammaBaseFunctionEnclosure wholeH wholeT wholeZ wholePlus wholeMinus
  (by decide +kernel) (by decide +kernel)
noncomputable def wholeData : GammaEnclosureData leftPoint.argument rightPoint.argument :=
  ⟨wholeBase,wholeT,wholeSecond,wholeThird,wholeW1,wholeW2⟩
theorem wholeDataAccepted : wholeData.check=true := by decide +kernel
noncomputable def wholeGamma := wholeData.enclosure wholeDataAccepted
def point_wl := checkedLogOfRows ScalarLogs0072.rows ScalarLogs0072.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0072.rows ScalarLogs0072.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0072.rows ScalarLogs0072.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0072.rows ScalarLogs0072.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0072.rows ScalarLogs0072.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0072.rows ScalarLogs0072.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0072.rows ScalarLogs0072.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0072.rows ScalarLogs0072.accepted ⟨111,by decide⟩
noncomputable def pointH := identityFunctionEnclosure midPoint.argument midPoint.argument
noncomputable def pointT := (firstMomentEnclosure midPoint midPoint).round
noncomputable def pointSecond := (secondMomentEnclosure midPoint midPoint).round
noncomputable def pointThird := (thirdMomentEnclosure midPoint midPoint).round
noncomputable def pointOne : FunctionEnclosure midPoint.argument midPoint.argument (fun _ => (1 : ℝ)) :=
  (FunctionEnclosure.const midPoint.argument midPoint.argument 1).congr (fun _ => Rat.cast_one)
noncomputable def pointZ := logBesselEndpoints midPoint midPoint point_zl point_zu (by decide +kernel)
noncomputable def pointPlus := logCompose (pointOne.radd pointT) point_pl point_pu (by decide +kernel)
noncomputable def pointMinus := logCompose (pointOne.rsub pointT) point_ml point_mu (by decide +kernel)
noncomputable def pointW1lower := checkedWeightOfLog 1 pointT.value.lower point_wl (by decide +kernel)
noncomputable def pointW1upper := checkedWeightOfLog 1 pointT.value.upper point_wu (by decide +kernel)
noncomputable def pointW1 := (weightCompose pointT 1 (by omega)
  pointW1lower pointW1upper (by decide +kernel)).round
noncomputable def pointW2lower := checkedWeightOfLog 2 pointT.value.lower point_wl (by decide +kernel)
noncomputable def pointW2upper := checkedWeightOfLog 2 pointT.value.upper point_wu (by decide +kernel)
noncomputable def pointW2 := (weightCompose pointT 2 (by omega)
  pointW2lower pointW2upper (by decide +kernel)).round
noncomputable def pointBase := gammaBaseFunctionEnclosure pointH pointT pointZ pointPlus pointMinus
  (by decide +kernel) (by decide +kernel)
noncomputable def pointData : GammaEnclosureData midPoint.argument midPoint.argument :=
  ⟨pointBase,pointT,pointSecond,pointThird,pointW1,pointW2⟩
theorem pointDataAccepted : pointData.check=true := by decide +kernel
noncomputable def pointGamma := pointData.enclosure pointDataAccepted
theorem panelAccepted : gammaPanelCheck BracketBatch0036.bracket0582 BracketBatch0036.bracket0583 (3513106446951662180197067136618436901381/20000000000000000000000000000000000000000) (352142313714544888886028925929919251/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0036.bracket0582 BracketBatch0036.bracket0583
  (3513106446951662180197067136618436901381/20000000000000000000000000000000000000000) (352142313714544888886028925929919251/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0582
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0583
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0091.rows BesselBatch0091.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0091.rows BesselBatch0091.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0091.rows BesselBatch0091.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0091.rows BesselBatch0091.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0091.rows BesselBatch0091.accepted ⟨10,by decide⟩
]
theorem leftAccepted : besselPointCheck (439400015095263160205892018703941745467/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (439400015095263160205892018703941745467/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0091.rows BesselBatch0091.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0091.rows BesselBatch0091.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0091.rows BesselBatch0091.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0091.rows BesselBatch0091.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0091.rows BesselBatch0091.accepted ⟨25,by decide⟩
]
theorem rightAccepted : besselPointCheck (219961745036238491308209814585479424157/1250000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (219961745036238491308209814585479424157/1250000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0534.rows BesselBatch0534.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0534.rows BesselBatch0534.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0534.rows BesselBatch0534.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0534.rows BesselBatch0534.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0534.rows BesselBatch0534.accepted ⟨33,by decide⟩
]
theorem midAccepted : besselPointCheck (879323505167740142822311647874900593781/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (879323505167740142822311647874900593781/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0072.rows ScalarLogs0072.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0072.rows ScalarLogs0072.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0072.rows ScalarLogs0072.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0072.rows ScalarLogs0072.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0072.rows ScalarLogs0072.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0072.rows ScalarLogs0072.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0072.rows ScalarLogs0072.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0072.rows ScalarLogs0072.accepted ⟨119,by decide⟩
noncomputable def wholeH := identityFunctionEnclosure leftPoint.argument rightPoint.argument
noncomputable def wholeT := (firstMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeSecond := (secondMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeThird := (thirdMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeOne : FunctionEnclosure leftPoint.argument rightPoint.argument (fun _ => (1 : ℝ)) :=
  (FunctionEnclosure.const leftPoint.argument rightPoint.argument 1).congr (fun _ => Rat.cast_one)
noncomputable def wholeZ := logBesselEndpoints leftPoint rightPoint whole_zl whole_zu (by decide +kernel)
noncomputable def wholePlus := logCompose (wholeOne.radd wholeT) whole_pl whole_pu (by decide +kernel)
noncomputable def wholeMinus := logCompose (wholeOne.rsub wholeT) whole_ml whole_mu (by decide +kernel)
noncomputable def wholeW1lower := checkedWeightOfLog 1 wholeT.value.lower whole_wl (by decide +kernel)
noncomputable def wholeW1upper := checkedWeightOfLog 1 wholeT.value.upper whole_wu (by decide +kernel)
noncomputable def wholeW1 := (weightCompose wholeT 1 (by omega)
  wholeW1lower wholeW1upper (by decide +kernel)).round
noncomputable def wholeW2lower := checkedWeightOfLog 2 wholeT.value.lower whole_wl (by decide +kernel)
noncomputable def wholeW2upper := checkedWeightOfLog 2 wholeT.value.upper whole_wu (by decide +kernel)
noncomputable def wholeW2 := (weightCompose wholeT 2 (by omega)
  wholeW2lower wholeW2upper (by decide +kernel)).round
noncomputable def wholeBase := gammaBaseFunctionEnclosure wholeH wholeT wholeZ wholePlus wholeMinus
  (by decide +kernel) (by decide +kernel)
noncomputable def wholeData : GammaEnclosureData leftPoint.argument rightPoint.argument :=
  ⟨wholeBase,wholeT,wholeSecond,wholeThird,wholeW1,wholeW2⟩
theorem wholeDataAccepted : wholeData.check=true := by decide +kernel
noncomputable def wholeGamma := wholeData.enclosure wholeDataAccepted
def point_wl := checkedLogOfRows ScalarLogs0072.rows ScalarLogs0072.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0072.rows ScalarLogs0072.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0072.rows ScalarLogs0072.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0072.rows ScalarLogs0072.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0072.rows ScalarLogs0072.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0072.rows ScalarLogs0072.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0072.rows ScalarLogs0072.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0072.rows ScalarLogs0072.accepted ⟨127,by decide⟩
noncomputable def pointH := identityFunctionEnclosure midPoint.argument midPoint.argument
noncomputable def pointT := (firstMomentEnclosure midPoint midPoint).round
noncomputable def pointSecond := (secondMomentEnclosure midPoint midPoint).round
noncomputable def pointThird := (thirdMomentEnclosure midPoint midPoint).round
noncomputable def pointOne : FunctionEnclosure midPoint.argument midPoint.argument (fun _ => (1 : ℝ)) :=
  (FunctionEnclosure.const midPoint.argument midPoint.argument 1).congr (fun _ => Rat.cast_one)
noncomputable def pointZ := logBesselEndpoints midPoint midPoint point_zl point_zu (by decide +kernel)
noncomputable def pointPlus := logCompose (pointOne.radd pointT) point_pl point_pu (by decide +kernel)
noncomputable def pointMinus := logCompose (pointOne.rsub pointT) point_ml point_mu (by decide +kernel)
noncomputable def pointW1lower := checkedWeightOfLog 1 pointT.value.lower point_wl (by decide +kernel)
noncomputable def pointW1upper := checkedWeightOfLog 1 pointT.value.upper point_wu (by decide +kernel)
noncomputable def pointW1 := (weightCompose pointT 1 (by omega)
  pointW1lower pointW1upper (by decide +kernel)).round
noncomputable def pointW2lower := checkedWeightOfLog 2 pointT.value.lower point_wl (by decide +kernel)
noncomputable def pointW2upper := checkedWeightOfLog 2 pointT.value.upper point_wu (by decide +kernel)
noncomputable def pointW2 := (weightCompose pointT 2 (by omega)
  pointW2lower pointW2upper (by decide +kernel)).round
noncomputable def pointBase := gammaBaseFunctionEnclosure pointH pointT pointZ pointPlus pointMinus
  (by decide +kernel) (by decide +kernel)
noncomputable def pointData : GammaEnclosureData midPoint.argument midPoint.argument :=
  ⟨pointBase,pointT,pointSecond,pointThird,pointW1,pointW2⟩
theorem pointDataAccepted : pointData.check=true := by decide +kernel
noncomputable def pointGamma := pointData.enclosure pointDataAccepted
theorem panelAccepted : gammaPanelCheck BracketBatch0036.bracket0583 BracketBatch0036.bracket0584 (879323505167740142822311647874900593781/5000000000000000000000000000000000000000) (707570970923851714831439606459418311/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0036.bracket0583 BracketBatch0036.bracket0584
  (879323505167740142822311647874900593781/5000000000000000000000000000000000000000) (707570970923851714831439606459418311/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0583
