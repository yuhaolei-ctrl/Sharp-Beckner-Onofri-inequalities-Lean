module

public import BecknerOnofri.EntropyScalarCertificate.Bessel0466
public import BecknerOnofri.EntropyScalarCertificate.Bessel0467
public import BecknerOnofri.EntropyScalarCertificate.Bessel0722
public import BecknerOnofri.EntropyScalarCertificate.Brackets0186
public import BecknerOnofri.EntropyScalarCertificate.Brackets0187
public import BecknerOnofri.EntropyScalarCertificate.Logs0373
public import BecknerOnofri.ScalarElementaryComposition
public import BecknerOnofri.ScalarGammaEnclosure
public import BecknerOnofri.ScalarLogBesselEndpoints

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2984
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0466.rows BesselBatch0466.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0466.rows BesselBatch0466.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0466.rows BesselBatch0466.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0466.rows BesselBatch0466.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0466.rows BesselBatch0466.accepted ⟨20,by decide⟩
]
theorem leftAccepted : besselPointCheck (1454741611049532697401430751026795087666759/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1454741611049532697401430751026795087666759/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0466.rows BesselBatch0466.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0466.rows BesselBatch0466.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0466.rows BesselBatch0466.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0466.rows BesselBatch0466.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0466.rows BesselBatch0466.accepted ⟨35,by decide⟩
]
theorem rightAccepted : besselPointCheck (729489588511045661934515407418637127395197/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (729489588511045661934515407418637127395197/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0722.rows BesselBatch0722.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0722.rows BesselBatch0722.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0722.rows BesselBatch0722.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0722.rows BesselBatch0722.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0722.rows BesselBatch0722.accepted ⟨6,by decide⟩
]
theorem midAccepted : besselPointCheck (2913720788071624021270461565864069342457153/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (2913720788071624021270461565864069342457153/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0373.rows ScalarLogs0373.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0373.rows ScalarLogs0373.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0373.rows ScalarLogs0373.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0373.rows ScalarLogs0373.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0373.rows ScalarLogs0373.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0373.rows ScalarLogs0373.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0373.rows ScalarLogs0373.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0373.rows ScalarLogs0373.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0373.rows ScalarLogs0373.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0373.rows ScalarLogs0373.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0373.rows ScalarLogs0373.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0373.rows ScalarLogs0373.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0373.rows ScalarLogs0373.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0373.rows ScalarLogs0373.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0373.rows ScalarLogs0373.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0373.rows ScalarLogs0373.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0186.bracket2984 BracketBatch0186.bracket2985 (2913720788071624021270461565864069342457153/20000000000000000000000000000000000000000) (836271647919946370729268128670456477089/1250000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0186.bracket2984 BracketBatch0186.bracket2985
  (2913720788071624021270461565864069342457153/20000000000000000000000000000000000000000) (836271647919946370729268128670456477089/1250000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2984
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2985
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0466.rows BesselBatch0466.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0466.rows BesselBatch0466.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0466.rows BesselBatch0466.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0466.rows BesselBatch0466.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0466.rows BesselBatch0466.accepted ⟨30,by decide⟩
]
theorem leftAccepted : besselPointCheck (1458979177022091323869030814837274254790391/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1458979177022091323869030814837274254790391/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0466.rows BesselBatch0466.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0466.rows BesselBatch0466.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0466.rows BesselBatch0466.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0466.rows BesselBatch0466.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0466.rows BesselBatch0466.accepted ⟨45,by decide⟩
]
theorem rightAccepted : besselPointCheck (1463241524137747592691476923357608244952939/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1463241524137747592691476923357608244952939/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0722.rows BesselBatch0722.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0722.rows BesselBatch0722.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0722.rows BesselBatch0722.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0722.rows BesselBatch0722.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0722.rows BesselBatch0722.accepted ⟨11,by decide⟩
]
theorem midAccepted : besselPointCheck (292222070115983891656050773819488249974333/2000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (292222070115983891656050773819488249974333/2000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0373.rows ScalarLogs0373.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0373.rows ScalarLogs0373.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0373.rows ScalarLogs0373.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0373.rows ScalarLogs0373.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0373.rows ScalarLogs0373.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0373.rows ScalarLogs0373.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0373.rows ScalarLogs0373.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0373.rows ScalarLogs0373.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0373.rows ScalarLogs0373.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0373.rows ScalarLogs0373.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0373.rows ScalarLogs0373.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0373.rows ScalarLogs0373.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0373.rows ScalarLogs0373.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0373.rows ScalarLogs0373.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0373.rows ScalarLogs0373.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0373.rows ScalarLogs0373.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0186.bracket2985 BracketBatch0186.bracket2986 (292222070115983891656050773819488249974333/2000000000000000000000000000000000000000) (1673658061001858580433191243289463970539/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0186.bracket2985 BracketBatch0186.bracket2986
  (292222070115983891656050773819488249974333/2000000000000000000000000000000000000000) (1673658061001858580433191243289463970539/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2985
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2986
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0466.rows BesselBatch0466.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0466.rows BesselBatch0466.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0466.rows BesselBatch0466.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0466.rows BesselBatch0466.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0466.rows BesselBatch0466.accepted ⟨40,by decide⟩
]
theorem leftAccepted : besselPointCheck (182905190517218449086434615419701030619117/1250000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (182905190517218449086434615419701030619117/1250000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0466.rows BesselBatch0466.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0466.rows BesselBatch0466.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0466.rows BesselBatch0466.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0466.rows BesselBatch0466.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0466.rows BesselBatch0466.accepted ⟨55,by decide⟩
]
theorem rightAccepted : besselPointCheck (1467528870412421068669371633687071578324097/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1467528870412421068669371633687071578324097/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0722.rows BesselBatch0722.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0722.rows BesselBatch0722.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0722.rows BesselBatch0722.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0722.rows BesselBatch0722.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0722.rows BesselBatch0722.accepted ⟨16,by decide⟩
]
theorem midAccepted : besselPointCheck (2930770394550168661360848557044679823277033/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (2930770394550168661360848557044679823277033/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0373.rows ScalarLogs0373.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0373.rows ScalarLogs0373.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0373.rows ScalarLogs0373.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0373.rows ScalarLogs0373.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0373.rows ScalarLogs0373.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0373.rows ScalarLogs0373.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0373.rows ScalarLogs0373.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0373.rows ScalarLogs0373.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0373.rows ScalarLogs0373.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0373.rows ScalarLogs0373.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0373.rows ScalarLogs0373.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0373.rows ScalarLogs0373.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0373.rows ScalarLogs0373.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0373.rows ScalarLogs0373.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0373.rows ScalarLogs0373.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0373.rows ScalarLogs0373.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0186.bracket2986 BracketBatch0186.bracket2987 (2930770394550168661360848557044679823277033/20000000000000000000000000000000000000000) (837387976362739718362518782091330427299/1250000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0186.bracket2986 BracketBatch0186.bracket2987
  (2930770394550168661360848557044679823277033/20000000000000000000000000000000000000000) (837387976362739718362518782091330427299/1250000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2986
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2987
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0466.rows BesselBatch0466.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0466.rows BesselBatch0466.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0466.rows BesselBatch0466.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0466.rows BesselBatch0466.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0466.rows BesselBatch0466.accepted ⟨50,by decide⟩
]
theorem leftAccepted : besselPointCheck (733764435206210534334685816843535789162047/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (733764435206210534334685816843535789162047/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0466.rows BesselBatch0466.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0466.rows BesselBatch0466.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0466.rows BesselBatch0466.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0467.rows BesselBatch0467.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0467.rows BesselBatch0467.accepted ⟨1,by decide⟩
]
theorem rightAccepted : besselPointCheck (1471841436426924488113607596863901804587643/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1471841436426924488113607596863901804587643/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0722.rows BesselBatch0722.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0722.rows BesselBatch0722.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0722.rows BesselBatch0722.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0722.rows BesselBatch0722.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0722.rows BesselBatch0722.accepted ⟨21,by decide⟩
]
theorem midAccepted : besselPointCheck (2939370306839345556782979230550973382911737/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (2939370306839345556782979230550973382911737/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0373.rows ScalarLogs0373.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0373.rows ScalarLogs0373.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0373.rows ScalarLogs0373.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0373.rows ScalarLogs0373.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0373.rows ScalarLogs0373.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0373.rows ScalarLogs0373.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0373.rows ScalarLogs0373.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0373.rows ScalarLogs0373.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0373.rows ScalarLogs0373.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0373.rows ScalarLogs0373.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0373.rows ScalarLogs0373.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0373.rows ScalarLogs0373.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0373.rows ScalarLogs0373.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0373.rows ScalarLogs0373.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0373.rows ScalarLogs0373.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0373.rows ScalarLogs0373.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0186.bracket2987 BracketBatch0186.bracket2988 (2939370306839345556782979230550973382911737/20000000000000000000000000000000000000000) (6703587947782742758167971108104278944681/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0186.bracket2987 BracketBatch0186.bracket2988
  (2939370306839345556782979230550973382911737/20000000000000000000000000000000000000000) (6703587947782742758167971108104278944681/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2987
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2988
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0466.rows BesselBatch0466.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0466.rows BesselBatch0466.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0466.rows BesselBatch0466.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0466.rows BesselBatch0466.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0466.rows BesselBatch0466.accepted ⟨60,by decide⟩
]
theorem leftAccepted : besselPointCheck (36796035910673112202840189921597545114691/250000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (36796035910673112202840189921597545114691/250000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0467.rows BesselBatch0467.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0467.rows BesselBatch0467.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0467.rows BesselBatch0467.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0467.rows BesselBatch0467.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0467.rows BesselBatch0467.accepted ⟨11,by decide⟩
]
theorem rightAccepted : besselPointCheck (738089722682397020805492946446940586605463/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (738089722682397020805492946446940586605463/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0722.rows BesselBatch0722.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0722.rows BesselBatch0722.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0722.rows BesselBatch0722.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0722.rows BesselBatch0722.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0722.rows BesselBatch0722.accepted ⟨26,by decide⟩
]
theorem midAccepted : besselPointCheck (1474010440895859264862296744878891488899283/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1474010440895859264862296744878891488899283/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0373.rows ScalarLogs0373.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0373.rows ScalarLogs0373.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0373.rows ScalarLogs0373.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0373.rows ScalarLogs0373.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0373.rows ScalarLogs0373.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0373.rows ScalarLogs0373.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0373.rows ScalarLogs0373.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0373.rows ScalarLogs0373.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0373.rows ScalarLogs0373.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0373.rows ScalarLogs0373.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0373.rows ScalarLogs0373.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0373.rows ScalarLogs0373.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0373.rows ScalarLogs0373.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0373.rows ScalarLogs0373.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0373.rows ScalarLogs0373.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0373.rows ScalarLogs0373.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0186.bracket2988 BracketBatch0186.bracket2989 (1474010440895859264862296744878891488899283/10000000000000000000000000000000000000000) (6708084718811737470535984169329982322061/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0186.bracket2988 BracketBatch0186.bracket2989
  (1474010440895859264862296744878891488899283/10000000000000000000000000000000000000000) (6708084718811737470535984169329982322061/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2988
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2989
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0467.rows BesselBatch0467.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0467.rows BesselBatch0467.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0467.rows BesselBatch0467.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0467.rows BesselBatch0467.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0467.rows BesselBatch0467.accepted ⟨6,by decide⟩
]
theorem leftAccepted : besselPointCheck (1476179445364794041610985892893881173210923/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1476179445364794041610985892893881173210923/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0467.rows BesselBatch0467.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0467.rows BesselBatch0467.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0467.rows BesselBatch0467.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0467.rows BesselBatch0467.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0467.rows BesselBatch0467.accepted ⟨21,by decide⟩
]
theorem rightAccepted : besselPointCheck (148054312305079120027088084888863569583393/1000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (148054312305079120027088084888863569583393/1000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0722.rows BesselBatch0722.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0722.rows BesselBatch0722.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0722.rows BesselBatch0722.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0722.rows BesselBatch0722.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0722.rows BesselBatch0722.accepted ⟨31,by decide⟩
]
theorem midAccepted : besselPointCheck (2956722568415585241881866741782516869044853/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (2956722568415585241881866741782516869044853/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0373.rows ScalarLogs0373.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0373.rows ScalarLogs0373.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0373.rows ScalarLogs0373.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0373.rows ScalarLogs0373.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0373.rows ScalarLogs0373.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0373.rows ScalarLogs0373.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0373.rows ScalarLogs0373.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0373.rows ScalarLogs0373.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0373.rows ScalarLogs0373.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0373.rows ScalarLogs0373.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0373.rows ScalarLogs0373.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0373.rows ScalarLogs0373.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0373.rows ScalarLogs0373.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0373.rows ScalarLogs0373.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0373.rows ScalarLogs0373.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0373.rows ScalarLogs0373.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0186.bracket2989 BracketBatch0186.bracket2990 (2956722568415585241881866741782516869044853/20000000000000000000000000000000000000000) (1342518837715074684773788645558537676011/2000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0186.bracket2989 BracketBatch0186.bracket2990
  (2956722568415585241881866741782516869044853/20000000000000000000000000000000000000000) (1342518837715074684773788645558537676011/2000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2989
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2990
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0467.rows BesselBatch0467.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0467.rows BesselBatch0467.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0467.rows BesselBatch0467.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0467.rows BesselBatch0467.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0467.rows BesselBatch0467.accepted ⟨16,by decide⟩
]
theorem leftAccepted : besselPointCheck (1480543123050791200270880848888635695833927/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1480543123050791200270880848888635695833927/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0467.rows BesselBatch0467.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0467.rows BesselBatch0467.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0467.rows BesselBatch0467.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0467.rows BesselBatch0467.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0467.rows BesselBatch0467.accepted ⟨31,by decide⟩
]
theorem rightAccepted : besselPointCheck (1484932697990090034427335095154709865308837/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1484932697990090034427335095154709865308837/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0722.rows BesselBatch0722.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0722.rows BesselBatch0722.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0722.rows BesselBatch0722.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0722.rows BesselBatch0722.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0722.rows BesselBatch0722.accepted ⟨36,by decide⟩
]
theorem midAccepted : besselPointCheck (741368955260220308674553986010836390285691/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (741368955260220308674553986010836390285691/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0373.rows ScalarLogs0373.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0373.rows ScalarLogs0373.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0373.rows ScalarLogs0373.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0373.rows ScalarLogs0373.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0373.rows ScalarLogs0373.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0373.rows ScalarLogs0373.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0373.rows ScalarLogs0373.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0373.rows ScalarLogs0373.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0373.rows ScalarLogs0373.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0373.rows ScalarLogs0373.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0373.rows ScalarLogs0373.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0373.rows ScalarLogs0373.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0373.rows ScalarLogs0373.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0373.rows ScalarLogs0373.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0373.rows ScalarLogs0373.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0373.rows ScalarLogs0373.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0186.bracket2990 BracketBatch0186.bracket2991 (741368955260220308674553986010836390285691/5000000000000000000000000000000000000000) (3358558211043644998531973231536242905227/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0186.bracket2990 BracketBatch0186.bracket2991
  (741368955260220308674553986010836390285691/5000000000000000000000000000000000000000) (3358558211043644998531973231536242905227/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2990
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2991
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0467.rows BesselBatch0467.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0467.rows BesselBatch0467.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0467.rows BesselBatch0467.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0467.rows BesselBatch0467.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0467.rows BesselBatch0467.accepted ⟨26,by decide⟩
]
theorem leftAccepted : besselPointCheck (742466348995045017213667547577354932654417/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (742466348995045017213667547577354932654417/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0467.rows BesselBatch0467.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0467.rows BesselBatch0467.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0467.rows BesselBatch0467.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0467.rows BesselBatch0467.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0467.rows BesselBatch0467.accepted ⟨41,by decide⟩
]
theorem rightAccepted : besselPointCheck (1489348401408164305889406322523072256228767/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1489348401408164305889406322523072256228767/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0722.rows BesselBatch0722.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0722.rows BesselBatch0722.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0722.rows BesselBatch0722.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0722.rows BesselBatch0722.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0722.rows BesselBatch0722.accepted ⟨41,by decide⟩
]
theorem midAccepted : besselPointCheck (2974281099398254340316741417677782121537601/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (2974281099398254340316741417677782121537601/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0373.rows ScalarLogs0373.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0373.rows ScalarLogs0373.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0373.rows ScalarLogs0373.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0373.rows ScalarLogs0373.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0373.rows ScalarLogs0373.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0373.rows ScalarLogs0373.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0373.rows ScalarLogs0373.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0373.rows ScalarLogs0373.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0373.rows ScalarLogs0373.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0373.rows ScalarLogs0373.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0373.rows ScalarLogs0373.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0373.rows ScalarLogs0373.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0373.rows ScalarLogs0373.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0373.rows ScalarLogs0373.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0373.rows ScalarLogs0373.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0373.rows ScalarLogs0373.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0186.bracket2991 BracketBatch0187.bracket2992 (2974281099398254340316741417677782121537601/20000000000000000000000000000000000000000) (6721651484790805015250289981917165088057/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0186.bracket2991 BracketBatch0187.bracket2992
  (2974281099398254340316741417677782121537601/20000000000000000000000000000000000000000) (6721651484790805015250289981917165088057/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2991
