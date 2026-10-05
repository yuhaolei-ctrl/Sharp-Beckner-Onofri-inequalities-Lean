module

public import BecknerOnofri.EntropyScalarCertificate.Bessel0471
public import BecknerOnofri.EntropyScalarCertificate.Bessel0472
public import BecknerOnofri.EntropyScalarCertificate.Bessel0724
public import BecknerOnofri.EntropyScalarCertificate.Bessel0725
public import BecknerOnofri.EntropyScalarCertificate.Brackets0188
public import BecknerOnofri.EntropyScalarCertificate.Brackets0189
public import BecknerOnofri.EntropyScalarCertificate.Logs0377
public import BecknerOnofri.ScalarElementaryComposition
public import BecknerOnofri.ScalarGammaEnclosure
public import BecknerOnofri.ScalarLogBesselEndpoints

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel3016
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0471.rows BesselBatch0471.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0471.rows BesselBatch0471.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0471.rows BesselBatch0471.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0471.rows BesselBatch0471.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0471.rows BesselBatch0471.accepted ⟨20,by decide⟩
]
theorem leftAccepted : besselPointCheck (1603817039037958173727404045457576132838181/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1603817039037958173727404045457576132838181/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0471.rows BesselBatch0471.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0471.rows BesselBatch0471.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0471.rows BesselBatch0471.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0471.rows BesselBatch0471.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0471.rows BesselBatch0471.accepted ⟨35,by decide⟩
]
theorem rightAccepted : besselPointCheck (1608969968825853252655568656533033555152749/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1608969968825853252655568656533033555152749/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0724.rows BesselBatch0724.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0724.rows BesselBatch0724.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0724.rows BesselBatch0724.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0724.rows BesselBatch0724.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0724.rows BesselBatch0724.accepted ⟨38,by decide⟩
]
theorem midAccepted : besselPointCheck (321278700786381142638297270199060968799093/2000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (321278700786381142638297270199060968799093/2000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0377.rows ScalarLogs0377.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0377.rows ScalarLogs0377.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0377.rows ScalarLogs0377.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0377.rows ScalarLogs0377.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0377.rows ScalarLogs0377.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0377.rows ScalarLogs0377.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0377.rows ScalarLogs0377.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0377.rows ScalarLogs0377.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0377.rows ScalarLogs0377.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0377.rows ScalarLogs0377.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0377.rows ScalarLogs0377.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0377.rows ScalarLogs0377.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0377.rows ScalarLogs0377.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0377.rows ScalarLogs0377.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0377.rows ScalarLogs0377.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0377.rows ScalarLogs0377.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0188.bracket3016 BracketBatch0188.bracket3017 (321278700786381142638297270199060968799093/2000000000000000000000000000000000000000) (68393980445945666166993681168504954869/100000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0188.bracket3016 BracketBatch0188.bracket3017
  (321278700786381142638297270199060968799093/2000000000000000000000000000000000000000) (68393980445945666166993681168504954869/100000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel3016
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel3017
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0471.rows BesselBatch0471.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0471.rows BesselBatch0471.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0471.rows BesselBatch0471.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0471.rows BesselBatch0471.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0471.rows BesselBatch0471.accepted ⟨30,by decide⟩
]
theorem leftAccepted : besselPointCheck (804484984412926626327784328266516777576373/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (804484984412926626327784328266516777576373/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0471.rows BesselBatch0471.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0471.rows BesselBatch0471.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0471.rows BesselBatch0471.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0471.rows BesselBatch0471.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0471.rows BesselBatch0471.accepted ⟨45,by decide⟩
]
theorem rightAccepted : besselPointCheck (403539035845813704610013351993952597033693/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (403539035845813704610013351993952597033693/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0724.rows BesselBatch0724.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0724.rows BesselBatch0724.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0724.rows BesselBatch0724.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0724.rows BesselBatch0724.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0724.rows BesselBatch0724.accepted ⟨43,by decide⟩
]
theorem midAccepted : besselPointCheck (1611563056104554035547811032254421971643759/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1611563056104554035547811032254421971643759/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0377.rows ScalarLogs0377.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0377.rows ScalarLogs0377.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0377.rows ScalarLogs0377.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0377.rows ScalarLogs0377.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0377.rows ScalarLogs0377.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0377.rows ScalarLogs0377.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0377.rows ScalarLogs0377.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0377.rows ScalarLogs0377.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0377.rows ScalarLogs0377.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0377.rows ScalarLogs0377.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0377.rows ScalarLogs0377.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0377.rows ScalarLogs0377.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0377.rows ScalarLogs0377.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0377.rows ScalarLogs0377.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0377.rows ScalarLogs0377.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0377.rows ScalarLogs0377.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0188.bracket3017 BracketBatch0188.bracket3018 (1611563056104554035547811032254421971643759/10000000000000000000000000000000000000000) (6844291100915393727206603918872190046807/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0188.bracket3017 BracketBatch0188.bracket3018
  (1611563056104554035547811032254421971643759/10000000000000000000000000000000000000000) (6844291100915393727206603918872190046807/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel3017
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel3018
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0471.rows BesselBatch0471.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0471.rows BesselBatch0471.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0471.rows BesselBatch0471.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0471.rows BesselBatch0471.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0471.rows BesselBatch0471.accepted ⟨40,by decide⟩
]
theorem leftAccepted : besselPointCheck (1614156143383254818440053407975810388134769/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1614156143383254818440053407975810388134769/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0471.rows BesselBatch0471.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0471.rows BesselBatch0471.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0471.rows BesselBatch0471.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0471.rows BesselBatch0471.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0471.rows BesselBatch0471.accepted ⟨55,by decide⟩
]
theorem rightAccepted : besselPointCheck (809687942737456516227492616748333809801843/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (809687942737456516227492616748333809801843/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0724.rows BesselBatch0724.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0724.rows BesselBatch0724.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0724.rows BesselBatch0724.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0724.rows BesselBatch0724.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0724.rows BesselBatch0724.accepted ⟨48,by decide⟩
]
theorem midAccepted : besselPointCheck (646706405771633570179007728294495601547691/4000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (646706405771633570179007728294495601547691/4000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0377.rows ScalarLogs0377.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0377.rows ScalarLogs0377.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0377.rows ScalarLogs0377.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0377.rows ScalarLogs0377.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0377.rows ScalarLogs0377.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0377.rows ScalarLogs0377.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0377.rows ScalarLogs0377.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0377.rows ScalarLogs0377.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0377.rows ScalarLogs0377.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0377.rows ScalarLogs0377.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0377.rows ScalarLogs0377.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0377.rows ScalarLogs0377.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0377.rows ScalarLogs0377.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0377.rows ScalarLogs0377.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0377.rows ScalarLogs0377.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0377.rows ScalarLogs0377.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0188.bracket3018 BracketBatch0188.bracket3019 (646706405771633570179007728294495601547691/4000000000000000000000000000000000000000) (6849198924310640749548579461685140414803/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0188.bracket3018 BracketBatch0188.bracket3019
  (646706405771633570179007728294495601547691/4000000000000000000000000000000000000000) (6849198924310640749548579461685140414803/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel3018
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel3019
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0471.rows BesselBatch0471.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0471.rows BesselBatch0471.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0471.rows BesselBatch0471.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0471.rows BesselBatch0471.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0471.rows BesselBatch0471.accepted ⟨50,by decide⟩
]
theorem leftAccepted : besselPointCheck (1619375885474913032454985233496667619603683/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1619375885474913032454985233496667619603683/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0471.rows BesselBatch0471.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0471.rows BesselBatch0471.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0471.rows BesselBatch0471.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0472.rows BesselBatch0472.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0472.rows BesselBatch0472.accepted ⟨1,by decide⟩
]
theorem rightAccepted : besselPointCheck (3173104535268218863956713518891260999857/19531250000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (3173104535268218863956713518891260999857/19531250000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0724.rows BesselBatch0724.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0724.rows BesselBatch0724.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0724.rows BesselBatch0724.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0724.rows BesselBatch0724.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0724.rows BesselBatch0724.accepted ⟨53,by decide⟩
]
theorem midAccepted : besselPointCheck (3244005407532241090800822555168993251530467/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (3244005407532241090800822555168993251530467/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0377.rows ScalarLogs0377.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0377.rows ScalarLogs0377.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0377.rows ScalarLogs0377.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0377.rows ScalarLogs0377.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0377.rows ScalarLogs0377.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0377.rows ScalarLogs0377.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0377.rows ScalarLogs0377.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0377.rows ScalarLogs0377.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0377.rows ScalarLogs0377.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0377.rows ScalarLogs0377.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0377.rows ScalarLogs0377.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0377.rows ScalarLogs0377.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0377.rows ScalarLogs0377.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0377.rows ScalarLogs0377.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0377.rows ScalarLogs0377.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0377.rows ScalarLogs0377.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0188.bracket3019 BracketBatch0188.bracket3020 (3244005407532241090800822555168993251530467/20000000000000000000000000000000000000000) (3427060796579679521277664387483207291721/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0188.bracket3019 BracketBatch0188.bracket3020
  (3244005407532241090800822555168993251530467/20000000000000000000000000000000000000000) (3427060796579679521277664387483207291721/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel3019
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel3020
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0471.rows BesselBatch0471.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0471.rows BesselBatch0471.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0471.rows BesselBatch0471.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0471.rows BesselBatch0471.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0471.rows BesselBatch0471.accepted ⟨60,by decide⟩
]
theorem leftAccepted : besselPointCheck (1624629522057328058345837321672325631926781/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1624629522057328058345837321672325631926781/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0472.rows BesselBatch0472.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0472.rows BesselBatch0472.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0472.rows BesselBatch0472.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0472.rows BesselBatch0472.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0472.rows BesselBatch0472.accepted ⟨11,by decide⟩
]
theorem rightAccepted : besselPointCheck (12733729565211090672190163777483358492859/78125000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (12733729565211090672190163777483358492859/78125000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0724.rows BesselBatch0724.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0724.rows BesselBatch0724.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0724.rows BesselBatch0724.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0724.rows BesselBatch0724.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0724.rows BesselBatch0724.accepted ⟨58,by decide⟩
]
theorem midAccepted : besselPointCheck (3254546906404347664386178285190195519012733/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (3254546906404347664386178285190195519012733/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0377.rows ScalarLogs0377.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0377.rows ScalarLogs0377.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0377.rows ScalarLogs0377.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0377.rows ScalarLogs0377.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0377.rows ScalarLogs0377.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0377.rows ScalarLogs0377.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0377.rows ScalarLogs0377.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0377.rows ScalarLogs0377.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0377.rows ScalarLogs0377.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0377.rows ScalarLogs0377.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0377.rows ScalarLogs0377.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0377.rows ScalarLogs0377.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0377.rows ScalarLogs0377.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0377.rows ScalarLogs0377.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0377.rows ScalarLogs0377.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0377.rows ScalarLogs0377.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0188.bracket3020 BracketBatch0188.bracket3021 (3254546906404347664386178285190195519012733/20000000000000000000000000000000000000000) (6859059186328069040497183722504183574219/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0188.bracket3020 BracketBatch0188.bracket3021
  (3254546906404347664386178285190195519012733/20000000000000000000000000000000000000000) (6859059186328069040497183722504183574219/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel3020
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel3021
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0472.rows BesselBatch0472.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0472.rows BesselBatch0472.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0472.rows BesselBatch0472.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0472.rows BesselBatch0472.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0472.rows BesselBatch0472.accepted ⟨6,by decide⟩
]
theorem leftAccepted : besselPointCheck (1629917384347019606040340963517869887085949/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1629917384347019606040340963517869887085949/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0472.rows BesselBatch0472.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0472.rows BesselBatch0472.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0472.rows BesselBatch0472.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0472.rows BesselBatch0472.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0472.rows BesselBatch0472.accepted ⟨21,by decide⟩
]
theorem rightAccepted : besselPointCheck (1635239807890135094269415283574838427321611/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1635239807890135094269415283574838427321611/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0724.rows BesselBatch0724.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0724.rows BesselBatch0724.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0724.rows BesselBatch0724.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0724.rows BesselBatch0724.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0724.rows BesselBatch0724.accepted ⟨63,by decide⟩
]
theorem midAccepted : besselPointCheck (81628929805928867507743906177317707860189/500000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (81628929805928867507743906177317707860189/500000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0377.rows ScalarLogs0377.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0377.rows ScalarLogs0377.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0377.rows ScalarLogs0377.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0377.rows ScalarLogs0377.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0377.rows ScalarLogs0377.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0377.rows ScalarLogs0377.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0377.rows ScalarLogs0377.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0377.rows ScalarLogs0377.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0377.rows ScalarLogs0377.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0377.rows ScalarLogs0377.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0377.rows ScalarLogs0377.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0377.rows ScalarLogs0377.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0377.rows ScalarLogs0377.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0377.rows ScalarLogs0377.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0377.rows ScalarLogs0377.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0377.rows ScalarLogs0377.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0188.bracket3021 BracketBatch0188.bracket3022 (81628929805928867507743906177317707860189/500000000000000000000000000000000000000) (6864011783171801239649436345165085625821/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0188.bracket3021 BracketBatch0188.bracket3022
  (81628929805928867507743906177317707860189/500000000000000000000000000000000000000) (6864011783171801239649436345165085625821/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel3021
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel3022
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0472.rows BesselBatch0472.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0472.rows BesselBatch0472.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0472.rows BesselBatch0472.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0472.rows BesselBatch0472.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0472.rows BesselBatch0472.accepted ⟨16,by decide⟩
]
theorem leftAccepted : besselPointCheck (204404975986266886783676910446854803415201/1250000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (204404975986266886783676910446854803415201/1250000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0472.rows BesselBatch0472.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0472.rows BesselBatch0472.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0472.rows BesselBatch0472.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0472.rows BesselBatch0472.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0472.rows BesselBatch0472.accepted ⟨31,by decide⟩
]
theorem rightAccepted : besselPointCheck (1640597132633427153990148051840505826512119/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1640597132633427153990148051840505826512119/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0725.rows BesselBatch0725.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0725.rows BesselBatch0725.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0725.rows BesselBatch0725.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0725.rows BesselBatch0725.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0725.rows BesselBatch0725.accepted ⟨4,by decide⟩
]
theorem midAccepted : besselPointCheck (3275836940523562248259563335415344253833727/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (3275836940523562248259563335415344253833727/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0377.rows ScalarLogs0377.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0377.rows ScalarLogs0377.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0377.rows ScalarLogs0377.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0377.rows ScalarLogs0377.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0377.rows ScalarLogs0377.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0377.rows ScalarLogs0377.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0377.rows ScalarLogs0377.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0377.rows ScalarLogs0377.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0377.rows ScalarLogs0377.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0377.rows ScalarLogs0377.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0377.rows ScalarLogs0377.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0377.rows ScalarLogs0377.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0377.rows ScalarLogs0377.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0377.rows ScalarLogs0377.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0377.rows ScalarLogs0377.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0377.rows ScalarLogs0377.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0188.bracket3022 BracketBatch0188.bracket3023 (3275836940523562248259563335415344253833727/20000000000000000000000000000000000000000) (3434489731767517091323983867152363844753/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0188.bracket3022 BracketBatch0188.bracket3023
  (3275836940523562248259563335415344253833727/20000000000000000000000000000000000000000) (3434489731767517091323983867152363844753/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel3022
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel3023
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0472.rows BesselBatch0472.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0472.rows BesselBatch0472.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0472.rows BesselBatch0472.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0472.rows BesselBatch0472.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0472.rows BesselBatch0472.accepted ⟨26,by decide⟩
]
theorem leftAccepted : besselPointCheck (410149283158356788497537012960126456628029/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (410149283158356788497537012960126456628029/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0472.rows BesselBatch0472.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0472.rows BesselBatch0472.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0472.rows BesselBatch0472.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0472.rows BesselBatch0472.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0472.rows BesselBatch0472.accepted ⟨41,by decide⟩
]
theorem rightAccepted : besselPointCheck (1645989702996632003586861647477707925115179/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1645989702996632003586861647477707925115179/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0725.rows BesselBatch0725.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0725.rows BesselBatch0725.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0725.rows BesselBatch0725.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0725.rows BesselBatch0725.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0725.rows BesselBatch0725.accepted ⟨9,by decide⟩
]
theorem midAccepted : besselPointCheck (657317367126011831515401939863642750325459/4000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (657317367126011831515401939863642750325459/4000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0377.rows ScalarLogs0377.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0377.rows ScalarLogs0377.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0377.rows ScalarLogs0377.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0377.rows ScalarLogs0377.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0377.rows ScalarLogs0377.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0377.rows ScalarLogs0377.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0377.rows ScalarLogs0377.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0377.rows ScalarLogs0377.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0377.rows ScalarLogs0377.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0377.rows ScalarLogs0377.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0377.rows ScalarLogs0377.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0377.rows ScalarLogs0377.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0377.rows ScalarLogs0377.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0377.rows ScalarLogs0377.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0377.rows ScalarLogs0377.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0377.rows ScalarLogs0377.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0188.bracket3023 BracketBatch0189.bracket3024 (657317367126011831515401939863642750325459/4000000000000000000000000000000000000000) (1374792461550504858920532576646971816463/2000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0188.bracket3023 BracketBatch0189.bracket3024
  (657317367126011831515401939863642750325459/4000000000000000000000000000000000000000) (1374792461550504858920532576646971816463/2000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel3023
