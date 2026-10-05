module

public import BecknerOnofri.EntropyScalarCertificate.Bessel0351
public import BecknerOnofri.EntropyScalarCertificate.Bessel0352
public import BecknerOnofri.EntropyScalarCertificate.Bessel0664
public import BecknerOnofri.EntropyScalarCertificate.Bessel0665
public import BecknerOnofri.EntropyScalarCertificate.Brackets0140
public import BecknerOnofri.EntropyScalarCertificate.Brackets0141
public import BecknerOnofri.EntropyScalarCertificate.Logs0281
public import BecknerOnofri.ScalarElementaryComposition
public import BecknerOnofri.ScalarGammaEnclosure
public import BecknerOnofri.ScalarLogBesselEndpoints

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2248
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0351.rows BesselBatch0351.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0351.rows BesselBatch0351.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0351.rows BesselBatch0351.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0351.rows BesselBatch0351.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0351.rows BesselBatch0351.accepted ⟨20,by decide⟩
]
theorem leftAccepted : besselPointCheck (109991495871894411514974542325207452820139/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (109991495871894411514974542325207452820139/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0351.rows BesselBatch0351.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0351.rows BesselBatch0351.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0351.rows BesselBatch0351.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0351.rows BesselBatch0351.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0351.rows BesselBatch0351.accepted ⟨35,by decide⟩
]
theorem rightAccepted : besselPointCheck (55232968557064040135347342042849506122377/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (55232968557064040135347342042849506122377/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0664.rows BesselBatch0664.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0664.rows BesselBatch0664.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0664.rows BesselBatch0664.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0664.rows BesselBatch0664.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0664.rows BesselBatch0664.accepted ⟨38,by decide⟩
]
theorem midAccepted : besselPointCheck (220457432986022491785669226410906465064893/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (220457432986022491785669226410906465064893/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0281.rows ScalarLogs0281.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0281.rows ScalarLogs0281.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0281.rows ScalarLogs0281.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0281.rows ScalarLogs0281.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0281.rows ScalarLogs0281.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0281.rows ScalarLogs0281.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0281.rows ScalarLogs0281.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0281.rows ScalarLogs0281.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0281.rows ScalarLogs0281.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0281.rows ScalarLogs0281.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0281.rows ScalarLogs0281.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0281.rows ScalarLogs0281.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0281.rows ScalarLogs0281.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0281.rows ScalarLogs0281.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0281.rows ScalarLogs0281.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0281.rows ScalarLogs0281.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0140.bracket2248 BracketBatch0140.bracket2249 (220457432986022491785669226410906465064893/20000000000000000000000000000000000000000) (2890283391613054036096017305119137823077/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0140.bracket2248 BracketBatch0140.bracket2249
  (220457432986022491785669226410906465064893/20000000000000000000000000000000000000000) (2890283391613054036096017305119137823077/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2248
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2249
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0351.rows BesselBatch0351.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0351.rows BesselBatch0351.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0351.rows BesselBatch0351.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0351.rows BesselBatch0351.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0351.rows BesselBatch0351.accepted ⟨30,by decide⟩
]
theorem leftAccepted : besselPointCheck (110465937114128080270694684085699012244751/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (110465937114128080270694684085699012244751/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0351.rows BesselBatch0351.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0351.rows BesselBatch0351.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0351.rows BesselBatch0351.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0351.rows BesselBatch0351.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0351.rows BesselBatch0351.accepted ⟨45,by decide⟩
]
theorem rightAccepted : besselPointCheck (110944542108222825853616407976688313165499/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (110944542108222825853616407976688313165499/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0664.rows BesselBatch0664.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0664.rows BesselBatch0664.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0664.rows BesselBatch0664.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0664.rows BesselBatch0664.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0664.rows BesselBatch0664.accepted ⟨43,by decide⟩
]
theorem midAccepted : besselPointCheck (885641916889403624497244368249549301641/80000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (885641916889403624497244368249549301641/80000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0281.rows ScalarLogs0281.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0281.rows ScalarLogs0281.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0281.rows ScalarLogs0281.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0281.rows ScalarLogs0281.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0281.rows ScalarLogs0281.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0281.rows ScalarLogs0281.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0281.rows ScalarLogs0281.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0281.rows ScalarLogs0281.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0281.rows ScalarLogs0281.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0281.rows ScalarLogs0281.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0281.rows ScalarLogs0281.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0281.rows ScalarLogs0281.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0281.rows ScalarLogs0281.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0281.rows ScalarLogs0281.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0281.rows ScalarLogs0281.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0281.rows ScalarLogs0281.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0140.bracket2249 BracketBatch0140.bracket2250 (885641916889403624497244368249549301641/80000000000000000000000000000000000000) (2896006963764755732863786991137496728981/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0140.bracket2249 BracketBatch0140.bracket2250
  (885641916889403624497244368249549301641/80000000000000000000000000000000000000) (2896006963764755732863786991137496728981/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2249
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2250
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0351.rows BesselBatch0351.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0351.rows BesselBatch0351.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0351.rows BesselBatch0351.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0351.rows BesselBatch0351.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0351.rows BesselBatch0351.accepted ⟨40,by decide⟩
]
theorem leftAccepted : besselPointCheck (13868067763527853231702050997086039145687/1250000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (13868067763527853231702050997086039145687/1250000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0351.rows BesselBatch0351.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0351.rows BesselBatch0351.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0351.rows BesselBatch0351.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0351.rows BesselBatch0351.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0351.rows BesselBatch0351.accepted ⟨55,by decide⟩
]
theorem rightAccepted : besselPointCheck (111427365879913620024476286545709889205533/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (111427365879913620024476286545709889205533/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0664.rows BesselBatch0664.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0664.rows BesselBatch0664.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0664.rows BesselBatch0664.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0664.rows BesselBatch0664.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0664.rows BesselBatch0664.accepted ⟨48,by decide⟩
]
theorem midAccepted : besselPointCheck (222371907988136445878092694522398202371029/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (222371907988136445878092694522398202371029/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0281.rows ScalarLogs0281.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0281.rows ScalarLogs0281.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0281.rows ScalarLogs0281.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0281.rows ScalarLogs0281.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0281.rows ScalarLogs0281.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0281.rows ScalarLogs0281.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0281.rows ScalarLogs0281.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0281.rows ScalarLogs0281.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0281.rows ScalarLogs0281.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0281.rows ScalarLogs0281.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0281.rows ScalarLogs0281.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0281.rows ScalarLogs0281.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0281.rows ScalarLogs0281.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0281.rows ScalarLogs0281.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0281.rows ScalarLogs0281.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0281.rows ScalarLogs0281.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0140.bracket2250 BracketBatch0140.bracket2251 (222371907988136445878092694522398202371029/20000000000000000000000000000000000000000) (1450878597604490909105619824941983096109/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0140.bracket2250 BracketBatch0140.bracket2251
  (222371907988136445878092694522398202371029/20000000000000000000000000000000000000000) (1450878597604490909105619824941983096109/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2250
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2251
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0351.rows BesselBatch0351.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0351.rows BesselBatch0351.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0351.rows BesselBatch0351.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0351.rows BesselBatch0351.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0351.rows BesselBatch0351.accepted ⟨50,by decide⟩
]
theorem leftAccepted : besselPointCheck (11142736587991362002447628654570988920553/1000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (11142736587991362002447628654570988920553/1000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0351.rows BesselBatch0351.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0351.rows BesselBatch0351.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0351.rows BesselBatch0351.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0352.rows BesselBatch0352.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0352.rows BesselBatch0352.accepted ⟨1,by decide⟩
]
theorem rightAccepted : besselPointCheck (55957232214422912326026259783889820232367/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (55957232214422912326026259783889820232367/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0664.rows BesselBatch0664.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0664.rows BesselBatch0664.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0664.rows BesselBatch0664.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0664.rows BesselBatch0664.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0664.rows BesselBatch0664.accepted ⟨53,by decide⟩
]
theorem midAccepted : besselPointCheck (27917728788594930584566100764186191208783/2500000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (27917728788594930584566100764186191208783/2500000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0281.rows ScalarLogs0281.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0281.rows ScalarLogs0281.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0281.rows ScalarLogs0281.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0281.rows ScalarLogs0281.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0281.rows ScalarLogs0281.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0281.rows ScalarLogs0281.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0281.rows ScalarLogs0281.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0281.rows ScalarLogs0281.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0281.rows ScalarLogs0281.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0281.rows ScalarLogs0281.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0281.rows ScalarLogs0281.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0281.rows ScalarLogs0281.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0281.rows ScalarLogs0281.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0281.rows ScalarLogs0281.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0281.rows ScalarLogs0281.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0281.rows ScalarLogs0281.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0140.bracket2251 BracketBatch0140.bracket2252 (27917728788594930584566100764186191208783/2500000000000000000000000000000000000000) (2907534314955018982255078063739314884369/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0140.bracket2251 BracketBatch0140.bracket2252
  (27917728788594930584566100764186191208783/2500000000000000000000000000000000000000) (2907534314955018982255078063739314884369/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2251
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2252
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0351.rows BesselBatch0351.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0351.rows BesselBatch0351.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0351.rows BesselBatch0351.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0351.rows BesselBatch0351.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0351.rows BesselBatch0351.accepted ⟨60,by decide⟩
]
theorem leftAccepted : besselPointCheck (111914464428845824652052519567779640464731/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (111914464428845824652052519567779640464731/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0352.rows BesselBatch0352.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0352.rows BesselBatch0352.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0352.rows BesselBatch0352.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0352.rows BesselBatch0352.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0352.rows BesselBatch0352.accepted ⟨11,by decide⟩
]
theorem rightAccepted : besselPointCheck (112405894750217632224260853735874510687131/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (112405894750217632224260853735874510687131/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0664.rows BesselBatch0664.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0664.rows BesselBatch0664.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0664.rows BesselBatch0664.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0664.rows BesselBatch0664.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0664.rows BesselBatch0664.accepted ⟨58,by decide⟩
]
theorem midAccepted : besselPointCheck (112160179589531728438156686651827075575931/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (112160179589531728438156686651827075575931/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0281.rows ScalarLogs0281.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0281.rows ScalarLogs0281.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0281.rows ScalarLogs0281.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0281.rows ScalarLogs0281.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0281.rows ScalarLogs0281.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0281.rows ScalarLogs0281.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0281.rows ScalarLogs0281.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0281.rows ScalarLogs0281.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0281.rows ScalarLogs0281.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0281.rows ScalarLogs0281.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0281.rows ScalarLogs0281.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0281.rows ScalarLogs0281.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0281.rows ScalarLogs0281.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0281.rows ScalarLogs0281.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0281.rows ScalarLogs0281.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0281.rows ScalarLogs0281.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0140.bracket2252 BracketBatch0140.bracket2253 (112160179589531728438156686651827075575931/10000000000000000000000000000000000000000) (284505718240309766873433349710188263/976562500000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0140.bracket2252 BracketBatch0140.bracket2253
  (112160179589531728438156686651827075575931/10000000000000000000000000000000000000000) (284505718240309766873433349710188263/976562500000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2252
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2253
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0352.rows BesselBatch0352.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0352.rows BesselBatch0352.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0352.rows BesselBatch0352.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0352.rows BesselBatch0352.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0352.rows BesselBatch0352.accepted ⟨6,by decide⟩
]
theorem leftAccepted : besselPointCheck (14050736843777204028032606716984313835891/1250000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (14050736843777204028032606716984313835891/1250000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0352.rows BesselBatch0352.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0352.rows BesselBatch0352.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0352.rows BesselBatch0352.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0352.rows BesselBatch0352.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0352.rows BesselBatch0352.accepted ⟨21,by decide⟩
]
theorem rightAccepted : besselPointCheck (112901714857002214658590261537176287603109/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (112901714857002214658590261537176287603109/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0664.rows BesselBatch0664.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0664.rows BesselBatch0664.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0664.rows BesselBatch0664.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0664.rows BesselBatch0664.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0664.rows BesselBatch0664.accepted ⟨63,by decide⟩
]
theorem midAccepted : besselPointCheck (225307609607219846882851115273050798290237/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (225307609607219846882851115273050798290237/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0281.rows ScalarLogs0281.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0281.rows ScalarLogs0281.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0281.rows ScalarLogs0281.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0281.rows ScalarLogs0281.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0281.rows ScalarLogs0281.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0281.rows ScalarLogs0281.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0281.rows ScalarLogs0281.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0281.rows ScalarLogs0281.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0281.rows ScalarLogs0281.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0281.rows ScalarLogs0281.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0281.rows ScalarLogs0281.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0281.rows ScalarLogs0281.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0281.rows ScalarLogs0281.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0281.rows ScalarLogs0281.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0281.rows ScalarLogs0281.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0281.rows ScalarLogs0281.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0140.bracket2253 BracketBatch0140.bracket2254 (225307609607219846882851115273050798290237/20000000000000000000000000000000000000000) (291917014927325771672368898182741738831/1000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0140.bracket2253 BracketBatch0140.bracket2254
  (225307609607219846882851115273050798290237/20000000000000000000000000000000000000000) (291917014927325771672368898182741738831/1000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2253
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2254
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0352.rows BesselBatch0352.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0352.rows BesselBatch0352.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0352.rows BesselBatch0352.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0352.rows BesselBatch0352.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0352.rows BesselBatch0352.accepted ⟨16,by decide⟩
]
theorem leftAccepted : besselPointCheck (56450857428501107329295130768588143801553/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (56450857428501107329295130768588143801553/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0352.rows BesselBatch0352.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0352.rows BesselBatch0352.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0352.rows BesselBatch0352.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0352.rows BesselBatch0352.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0352.rows BesselBatch0352.accepted ⟨31,by decide⟩
]
theorem rightAccepted : besselPointCheck (113401983802767777532769623656788670776579/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (113401983802767777532769623656788670776579/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0665.rows BesselBatch0665.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0665.rows BesselBatch0665.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0665.rows BesselBatch0665.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0665.rows BesselBatch0665.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0665.rows BesselBatch0665.accepted ⟨4,by decide⟩
]
theorem midAccepted : besselPointCheck (45260739731953998438271977038792991675937/4000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (45260739731953998438271977038792991675937/4000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0281.rows ScalarLogs0281.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0281.rows ScalarLogs0281.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0281.rows ScalarLogs0281.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0281.rows ScalarLogs0281.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0281.rows ScalarLogs0281.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0281.rows ScalarLogs0281.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0281.rows ScalarLogs0281.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0281.rows ScalarLogs0281.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0281.rows ScalarLogs0281.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0281.rows ScalarLogs0281.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0281.rows ScalarLogs0281.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0281.rows ScalarLogs0281.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0281.rows ScalarLogs0281.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0281.rows ScalarLogs0281.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0281.rows ScalarLogs0281.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0281.rows ScalarLogs0281.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0140.bracket2254 BracketBatch0140.bracket2255 (45260739731953998438271977038792991675937/4000000000000000000000000000000000000000) (2925029335869712133562922870077133171623/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0140.bracket2254 BracketBatch0140.bracket2255
  (45260739731953998438271977038792991675937/4000000000000000000000000000000000000000) (2925029335869712133562922870077133171623/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2254
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2255
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0352.rows BesselBatch0352.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0352.rows BesselBatch0352.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0352.rows BesselBatch0352.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0352.rows BesselBatch0352.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0352.rows BesselBatch0352.accepted ⟨26,by decide⟩
]
theorem leftAccepted : besselPointCheck (442976499229561630987381342409330745221/39062500000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (442976499229561630987381342409330745221/39062500000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0352.rows BesselBatch0352.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0352.rows BesselBatch0352.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0352.rows BesselBatch0352.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0352.rows BesselBatch0352.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0352.rows BesselBatch0352.accepted ⟨41,by decide⟩
]
theorem rightAccepted : besselPointCheck (56953380852557186304334342300674149903177/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (56953380852557186304334342300674149903177/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0665.rows BesselBatch0665.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0665.rows BesselBatch0665.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0665.rows BesselBatch0665.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0665.rows BesselBatch0665.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0665.rows BesselBatch0665.accepted ⟨9,by decide⟩
]
theorem midAccepted : besselPointCheck (22730874550788215014143830825813697058293/2000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (22730874550788215014143830825813697058293/2000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0281.rows ScalarLogs0281.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0281.rows ScalarLogs0281.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0281.rows ScalarLogs0281.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0281.rows ScalarLogs0281.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0281.rows ScalarLogs0281.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0281.rows ScalarLogs0281.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0281.rows ScalarLogs0281.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0281.rows ScalarLogs0281.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0281.rows ScalarLogs0281.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0281.rows ScalarLogs0281.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0281.rows ScalarLogs0281.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0281.rows ScalarLogs0281.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0281.rows ScalarLogs0281.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0281.rows ScalarLogs0281.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0281.rows ScalarLogs0281.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0281.rows ScalarLogs0281.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0140.bracket2255 BracketBatch0141.bracket2256 (22730874550788215014143830825813697058293/2000000000000000000000000000000000000000) (732729088724829183410327559411835858103/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0140.bracket2255 BracketBatch0141.bracket2256
  (22730874550788215014143830825813697058293/2000000000000000000000000000000000000000) (732729088724829183410327559411835858103/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2255
