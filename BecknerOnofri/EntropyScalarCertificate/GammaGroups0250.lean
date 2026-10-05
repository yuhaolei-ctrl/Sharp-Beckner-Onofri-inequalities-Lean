module

public import BecknerOnofri.EntropyScalarCertificate.Bessel0312
public import BecknerOnofri.EntropyScalarCertificate.Bessel0313
public import BecknerOnofri.EntropyScalarCertificate.Bessel0645
public import BecknerOnofri.EntropyScalarCertificate.Brackets0125
public import BecknerOnofri.EntropyScalarCertificate.Logs0250
public import BecknerOnofri.ScalarElementaryComposition
public import BecknerOnofri.ScalarGammaEnclosure
public import BecknerOnofri.ScalarLogBesselEndpoints

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2000
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0312.rows BesselBatch0312.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0312.rows BesselBatch0312.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0312.rows BesselBatch0312.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0312.rows BesselBatch0312.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0312.rows BesselBatch0312.accepted ⟨36,by decide⟩
]
theorem leftAccepted : besselPointCheck (10730828272981786826990772706817350850327/2000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (10730828272981786826990772706817350850327/2000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0312.rows BesselBatch0312.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0312.rows BesselBatch0312.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0312.rows BesselBatch0312.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0312.rows BesselBatch0312.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0312.rows BesselBatch0312.accepted ⟨51,by decide⟩
]
theorem rightAccepted : besselPointCheck (2150541489404114024591918767613901115879/400000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (2150541489404114024591918767613901115879/400000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0645.rows BesselBatch0645.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0645.rows BesselBatch0645.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0645.rows BesselBatch0645.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0645.rows BesselBatch0645.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0645.rows BesselBatch0645.accepted ⟨14,by decide⟩
]
theorem midAccepted : besselPointCheck (10741767860001178474975183272443428214861/2000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (10741767860001178474975183272443428214861/2000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0250.rows ScalarLogs0250.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0250.rows ScalarLogs0250.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0250.rows ScalarLogs0250.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0250.rows ScalarLogs0250.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0250.rows ScalarLogs0250.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0250.rows ScalarLogs0250.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0250.rows ScalarLogs0250.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0250.rows ScalarLogs0250.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0250.rows ScalarLogs0250.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0250.rows ScalarLogs0250.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0250.rows ScalarLogs0250.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0250.rows ScalarLogs0250.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0250.rows ScalarLogs0250.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0250.rows ScalarLogs0250.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0250.rows ScalarLogs0250.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0250.rows ScalarLogs0250.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0125.bracket2000 BracketBatch0125.bracket2001 (10741767860001178474975183272443428214861/2000000000000000000000000000000000000000) (1958286096831708740816177265395439053661/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0125.bracket2000 BracketBatch0125.bracket2001
  (10741767860001178474975183272443428214861/2000000000000000000000000000000000000000) (1958286096831708740816177265395439053661/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2000
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2001
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0312.rows BesselBatch0312.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0312.rows BesselBatch0312.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0312.rows BesselBatch0312.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0312.rows BesselBatch0312.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0312.rows BesselBatch0312.accepted ⟨46,by decide⟩
]
theorem leftAccepted : besselPointCheck (13440884308775712653699492297586881974243/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (13440884308775712653699492297586881974243/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0312.rows BesselBatch0312.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0312.rows BesselBatch0312.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0312.rows BesselBatch0312.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0312.rows BesselBatch0312.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0312.rows BesselBatch0312.accepted ⟨61,by decide⟩
]
theorem rightAccepted : besselPointCheck (10774678799380903997435287625226781023151/2000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (10774678799380903997435287625226781023151/2000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0645.rows BesselBatch0645.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0645.rows BesselBatch0645.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0645.rows BesselBatch0645.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0645.rows BesselBatch0645.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0645.rows BesselBatch0645.accepted ⟨19,by decide⟩
]
theorem midAccepted : besselPointCheck (107636931232007370601974407316481433012727/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (107636931232007370601974407316481433012727/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0250.rows ScalarLogs0250.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0250.rows ScalarLogs0250.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0250.rows ScalarLogs0250.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0250.rows ScalarLogs0250.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0250.rows ScalarLogs0250.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0250.rows ScalarLogs0250.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0250.rows ScalarLogs0250.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0250.rows ScalarLogs0250.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0250.rows ScalarLogs0250.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0250.rows ScalarLogs0250.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0250.rows ScalarLogs0250.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0250.rows ScalarLogs0250.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0250.rows ScalarLogs0250.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0250.rows ScalarLogs0250.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0250.rows ScalarLogs0250.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0250.rows ScalarLogs0250.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0125.bracket2001 BracketBatch0125.bracket2002 (107636931232007370601974407316481433012727/20000000000000000000000000000000000000000) (1960856839020026242737286911922421904351/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0125.bracket2001 BracketBatch0125.bracket2002
  (107636931232007370601974407316481433012727/20000000000000000000000000000000000000000) (1960856839020026242737286911922421904351/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2001
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2002
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0312.rows BesselBatch0312.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0312.rows BesselBatch0312.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0312.rows BesselBatch0312.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0312.rows BesselBatch0312.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0312.rows BesselBatch0312.accepted ⟨56,by decide⟩
]
theorem leftAccepted : besselPointCheck (6734174249613064998397054765766738139469/1250000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (6734174249613064998397054765766738139469/1250000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0313.rows BesselBatch0313.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0313.rows BesselBatch0313.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0313.rows BesselBatch0313.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0313.rows BesselBatch0313.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0313.rows BesselBatch0313.accepted ⟨7,by decide⟩
]
theorem rightAccepted : besselPointCheck (6747964319942526323601449814610336069117/1250000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (6747964319942526323601449814610336069117/1250000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0645.rows BesselBatch0645.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0645.rows BesselBatch0645.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0645.rows BesselBatch0645.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0645.rows BesselBatch0645.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0645.rows BesselBatch0645.accepted ⟨24,by decide⟩
]
theorem midAccepted : besselPointCheck (6741069284777795660999252290188537104293/1250000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (6741069284777795660999252290188537104293/1250000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0250.rows ScalarLogs0250.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0250.rows ScalarLogs0250.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0250.rows ScalarLogs0250.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0250.rows ScalarLogs0250.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0250.rows ScalarLogs0250.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0250.rows ScalarLogs0250.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0250.rows ScalarLogs0250.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0250.rows ScalarLogs0250.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0250.rows ScalarLogs0250.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0250.rows ScalarLogs0250.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0250.rows ScalarLogs0250.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0250.rows ScalarLogs0250.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0250.rows ScalarLogs0250.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0250.rows ScalarLogs0250.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0250.rows ScalarLogs0250.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0250.rows ScalarLogs0250.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0125.bracket2002 BracketBatch0125.bracket2003 (6741069284777795660999252290188537104293/1250000000000000000000000000000000000000) (490858409342462635795135360863758089939/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0125.bracket2002 BracketBatch0125.bracket2003
  (6741069284777795660999252290188537104293/1250000000000000000000000000000000000000) (490858409342462635795135360863758089939/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2002
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2003
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0312.rows BesselBatch0312.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0312.rows BesselBatch0312.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0313.rows BesselBatch0313.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0313.rows BesselBatch0313.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0313.rows BesselBatch0313.accepted ⟨2,by decide⟩
]
theorem leftAccepted : besselPointCheck (53983714559540210588811598516882688552933/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (53983714559540210588811598516882688552933/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0313.rows BesselBatch0313.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0313.rows BesselBatch0313.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0313.rows BesselBatch0313.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0313.rows BesselBatch0313.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0313.rows BesselBatch0313.accepted ⟨17,by decide⟩
]
theorem rightAccepted : besselPointCheck (1690453183024769244568366397098316322819/312500000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1690453183024769244568366397098316322819/312500000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0645.rows BesselBatch0645.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0645.rows BesselBatch0645.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0645.rows BesselBatch0645.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0645.rows BesselBatch0645.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0645.rows BesselBatch0645.accepted ⟨29,by decide⟩
]
theorem midAccepted : besselPointCheck (108078216416332826414999323224028810883141/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (108078216416332826414999323224028810883141/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0250.rows ScalarLogs0250.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0250.rows ScalarLogs0250.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0250.rows ScalarLogs0250.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0250.rows ScalarLogs0250.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0250.rows ScalarLogs0250.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0250.rows ScalarLogs0250.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0250.rows ScalarLogs0250.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0250.rows ScalarLogs0250.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0250.rows ScalarLogs0250.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0250.rows ScalarLogs0250.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0250.rows ScalarLogs0250.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0250.rows ScalarLogs0250.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0250.rows ScalarLogs0250.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0250.rows ScalarLogs0250.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0250.rows ScalarLogs0250.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0250.rows ScalarLogs0250.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0125.bracket2003 BracketBatch0125.bracket2004 (108078216416332826414999323224028810883141/20000000000000000000000000000000000000000) (491504129433974586711866874686727030023/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0125.bracket2003 BracketBatch0125.bracket2004
  (108078216416332826414999323224028810883141/20000000000000000000000000000000000000000) (491504129433974586711866874686727030023/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2003
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2004
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0313.rows BesselBatch0313.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0313.rows BesselBatch0313.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0313.rows BesselBatch0313.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0313.rows BesselBatch0313.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0313.rows BesselBatch0313.accepted ⟨12,by decide⟩
]
theorem leftAccepted : besselPointCheck (10818900371358523165237544941429224466041/2000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (10818900371358523165237544941429224466041/2000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0313.rows BesselBatch0313.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0313.rows BesselBatch0313.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0313.rows BesselBatch0313.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0313.rows BesselBatch0313.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0313.rows BesselBatch0313.accepted ⟨27,by decide⟩
]
theorem rightAccepted : besselPointCheck (54205758847260402859451897258198299405783/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (54205758847260402859451897258198299405783/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0645.rows BesselBatch0645.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0645.rows BesselBatch0645.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0645.rows BesselBatch0645.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0645.rows BesselBatch0645.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0645.rows BesselBatch0645.accepted ⟨34,by decide⟩
]
theorem midAccepted : besselPointCheck (27075065176013254671409905491336105433997/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (27075065176013254671409905491336105433997/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0250.rows ScalarLogs0250.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0250.rows ScalarLogs0250.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0250.rows ScalarLogs0250.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0250.rows ScalarLogs0250.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0250.rows ScalarLogs0250.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0250.rows ScalarLogs0250.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0250.rows ScalarLogs0250.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0250.rows ScalarLogs0250.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0250.rows ScalarLogs0250.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0250.rows ScalarLogs0250.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0250.rows ScalarLogs0250.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0250.rows ScalarLogs0250.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0250.rows ScalarLogs0250.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0250.rows ScalarLogs0250.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0250.rows ScalarLogs0250.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0250.rows ScalarLogs0250.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0125.bracket2004 BracketBatch0125.bracket2005 (27075065176013254671409905491336105433997/5000000000000000000000000000000000000000) (1968605506142446422552420176685697777393/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0125.bracket2004 BracketBatch0125.bracket2005
  (27075065176013254671409905491336105433997/5000000000000000000000000000000000000000) (1968605506142446422552420176685697777393/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2004
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2005
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0313.rows BesselBatch0313.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0313.rows BesselBatch0313.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0313.rows BesselBatch0313.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0313.rows BesselBatch0313.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0313.rows BesselBatch0313.accepted ⟨22,by decide⟩
]
theorem leftAccepted : besselPointCheck (2710287942363020142972594862909914970289/500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (2710287942363020142972594862909914970289/500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0313.rows BesselBatch0313.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0313.rows BesselBatch0313.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0313.rows BesselBatch0313.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0313.rows BesselBatch0313.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0313.rows BesselBatch0313.accepted ⟨37,by decide⟩
]
theorem rightAccepted : besselPointCheck (27158744257310530314637472153083335334611/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (27158744257310530314637472153083335334611/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0645.rows BesselBatch0645.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0645.rows BesselBatch0645.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0645.rows BesselBatch0645.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0645.rows BesselBatch0645.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0645.rows BesselBatch0645.accepted ⟨39,by decide⟩
]
theorem midAccepted : besselPointCheck (54261623680940731744363420782182485037501/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (54261623680940731744363420782182485037501/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0250.rows ScalarLogs0250.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0250.rows ScalarLogs0250.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0250.rows ScalarLogs0250.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0250.rows ScalarLogs0250.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0250.rows ScalarLogs0250.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0250.rows ScalarLogs0250.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0250.rows ScalarLogs0250.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0250.rows ScalarLogs0250.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0250.rows ScalarLogs0250.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0250.rows ScalarLogs0250.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0250.rows ScalarLogs0250.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0250.rows ScalarLogs0250.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0250.rows ScalarLogs0250.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0250.rows ScalarLogs0250.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0250.rows ScalarLogs0250.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0250.rows ScalarLogs0250.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0125.bracket2005 BracketBatch0125.bracket2006 (54261623680940731744363420782182485037501/10000000000000000000000000000000000000000) (394240125756958389725755836051218515657/2000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0125.bracket2005 BracketBatch0125.bracket2006
  (54261623680940731744363420782182485037501/10000000000000000000000000000000000000000) (394240125756958389725755836051218515657/2000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2005
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2006
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0313.rows BesselBatch0313.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0313.rows BesselBatch0313.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0313.rows BesselBatch0313.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0313.rows BesselBatch0313.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0313.rows BesselBatch0313.accepted ⟨32,by decide⟩
]
theorem leftAccepted : besselPointCheck (54317488514621060629274944306166670669219/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (54317488514621060629274944306166670669219/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0313.rows BesselBatch0313.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0313.rows BesselBatch0313.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0313.rows BesselBatch0313.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0313.rows BesselBatch0313.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0313.rows BesselBatch0313.accepted ⟨47,by decide⟩
]
theorem rightAccepted : besselPointCheck (27214846933948548133601668896711902256291/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (27214846933948548133601668896711902256291/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0645.rows BesselBatch0645.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0645.rows BesselBatch0645.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0645.rows BesselBatch0645.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0645.rows BesselBatch0645.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0645.rows BesselBatch0645.accepted ⟨44,by decide⟩
]
theorem midAccepted : besselPointCheck (108747182382518156896478282099590475181801/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (108747182382518156896478282099590475181801/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0250.rows ScalarLogs0250.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0250.rows ScalarLogs0250.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0250.rows ScalarLogs0250.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0250.rows ScalarLogs0250.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0250.rows ScalarLogs0250.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0250.rows ScalarLogs0250.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0250.rows ScalarLogs0250.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0250.rows ScalarLogs0250.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0250.rows ScalarLogs0250.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0250.rows ScalarLogs0250.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0250.rows ScalarLogs0250.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0250.rows ScalarLogs0250.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0250.rows ScalarLogs0250.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0250.rows ScalarLogs0250.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0250.rows ScalarLogs0250.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0250.rows ScalarLogs0250.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0125.bracket2006 BracketBatch0125.bracket2007 (108747182382518156896478282099590475181801/20000000000000000000000000000000000000000) (493450478007682097382743394429542101549/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0125.bracket2006 BracketBatch0125.bracket2007
  (108747182382518156896478282099590475181801/20000000000000000000000000000000000000000) (493450478007682097382743394429542101549/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2006
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2007
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0313.rows BesselBatch0313.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0313.rows BesselBatch0313.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0313.rows BesselBatch0313.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0313.rows BesselBatch0313.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0313.rows BesselBatch0313.accepted ⟨42,by decide⟩
]
theorem leftAccepted : besselPointCheck (54429693867897096267203337793423804512579/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (54429693867897096267203337793423804512579/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0313.rows BesselBatch0313.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0313.rows BesselBatch0313.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0313.rows BesselBatch0313.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0313.rows BesselBatch0313.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0313.rows BesselBatch0313.accepted ⟨57,by decide⟩
]
theorem rightAccepted : besselPointCheck (27271188970862814882345106863418573594411/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (27271188970862814882345106863418573594411/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0645.rows BesselBatch0645.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0645.rows BesselBatch0645.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0645.rows BesselBatch0645.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0645.rows BesselBatch0645.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0645.rows BesselBatch0645.accepted ⟨49,by decide⟩
]
theorem midAccepted : besselPointCheck (108972071809622726031893551520260951701401/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (108972071809622726031893551520260951701401/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0250.rows ScalarLogs0250.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0250.rows ScalarLogs0250.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0250.rows ScalarLogs0250.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0250.rows ScalarLogs0250.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0250.rows ScalarLogs0250.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0250.rows ScalarLogs0250.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0250.rows ScalarLogs0250.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0250.rows ScalarLogs0250.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0250.rows ScalarLogs0250.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0250.rows ScalarLogs0250.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0250.rows ScalarLogs0250.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0250.rows ScalarLogs0250.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0250.rows ScalarLogs0250.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0250.rows ScalarLogs0250.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0250.rows ScalarLogs0250.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0250.rows ScalarLogs0250.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0125.bracket2007 BracketBatch0125.bracket2008 (108972071809622726031893551520260951701401/20000000000000000000000000000000000000000) (494102345605509275179891920572713893583/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0125.bracket2007 BracketBatch0125.bracket2008
  (108972071809622726031893551520260951701401/20000000000000000000000000000000000000000) (494102345605509275179891920572713893583/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2007
