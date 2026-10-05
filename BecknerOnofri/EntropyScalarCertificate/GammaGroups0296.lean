module

public import BecknerOnofri.EntropyScalarCertificate.Bessel0370
public import BecknerOnofri.EntropyScalarCertificate.Bessel0371
public import BecknerOnofri.EntropyScalarCertificate.Bessel0673
public import BecknerOnofri.EntropyScalarCertificate.Bessel0674
public import BecknerOnofri.EntropyScalarCertificate.Brackets0148
public import BecknerOnofri.EntropyScalarCertificate.Logs0296
public import BecknerOnofri.ScalarElementaryComposition
public import BecknerOnofri.ScalarGammaEnclosure
public import BecknerOnofri.ScalarLogBesselEndpoints

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2368
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0370.rows BesselBatch0370.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0370.rows BesselBatch0370.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0370.rows BesselBatch0370.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0370.rows BesselBatch0370.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0370.rows BesselBatch0370.accepted ⟨4,by decide⟩
]
theorem leftAccepted : besselPointCheck (114271971944308444860241107672955375443241/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (114271971944308444860241107672955375443241/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0370.rows BesselBatch0370.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0370.rows BesselBatch0370.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0370.rows BesselBatch0370.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0370.rows BesselBatch0370.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0370.rows BesselBatch0370.accepted ⟨19,by decide⟩
]
theorem rightAccepted : besselPointCheck (115314408171227047067405766563606469286651/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (115314408171227047067405766563606469286651/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0673.rows BesselBatch0673.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0673.rows BesselBatch0673.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0673.rows BesselBatch0673.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0673.rows BesselBatch0673.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0673.rows BesselBatch0673.accepted ⟨62,by decide⟩
]
theorem midAccepted : besselPointCheck (57396595028883872981911718559140461182473/2500000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (57396595028883872981911718559140461182473/2500000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0296.rows ScalarLogs0296.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0296.rows ScalarLogs0296.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0296.rows ScalarLogs0296.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0296.rows ScalarLogs0296.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0296.rows ScalarLogs0296.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0296.rows ScalarLogs0296.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0296.rows ScalarLogs0296.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0296.rows ScalarLogs0296.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0296.rows ScalarLogs0296.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0296.rows ScalarLogs0296.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0296.rows ScalarLogs0296.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0296.rows ScalarLogs0296.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0296.rows ScalarLogs0296.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0296.rows ScalarLogs0296.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0296.rows ScalarLogs0296.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0296.rows ScalarLogs0296.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0148.bracket2368 BracketBatch0148.bracket2369 (57396595028883872981911718559140461182473/2500000000000000000000000000000000000000) (3866134829058516135144307212751676775119/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0148.bracket2368 BracketBatch0148.bracket2369
  (57396595028883872981911718559140461182473/2500000000000000000000000000000000000000) (3866134829058516135144307212751676775119/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2368
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2369
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0370.rows BesselBatch0370.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0370.rows BesselBatch0370.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0370.rows BesselBatch0370.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0370.rows BesselBatch0370.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0370.rows BesselBatch0370.accepted ⟨14,by decide⟩
]
theorem leftAccepted : besselPointCheck (230628816342454094134811533127212938573299/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (230628816342454094134811533127212938573299/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0370.rows BesselBatch0370.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0370.rows BesselBatch0370.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0370.rows BesselBatch0370.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0370.rows BesselBatch0370.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0370.rows BesselBatch0370.accepted ⟨29,by decide⟩
]
theorem rightAccepted : besselPointCheck (232752301326690693115112676269433959405889/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (232752301326690693115112676269433959405889/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0673.rows BesselBatch0673.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0674.rows BesselBatch0674.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0674.rows BesselBatch0674.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0674.rows BesselBatch0674.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0674.rows BesselBatch0674.accepted ⟨3,by decide⟩
]
theorem midAccepted : besselPointCheck (115845279417286196812481052349161724494797/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (115845279417286196812481052349161724494797/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0296.rows ScalarLogs0296.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0296.rows ScalarLogs0296.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0296.rows ScalarLogs0296.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0296.rows ScalarLogs0296.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0296.rows ScalarLogs0296.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0296.rows ScalarLogs0296.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0296.rows ScalarLogs0296.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0296.rows ScalarLogs0296.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0296.rows ScalarLogs0296.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0296.rows ScalarLogs0296.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0296.rows ScalarLogs0296.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0296.rows ScalarLogs0296.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0296.rows ScalarLogs0296.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0296.rows ScalarLogs0296.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0296.rows ScalarLogs0296.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0296.rows ScalarLogs0296.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0148.bracket2369 BracketBatch0148.bracket2370 (115845279417286196812481052349161724494797/5000000000000000000000000000000000000000) (3878089179675437646941895093143033309357/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0148.bracket2369 BracketBatch0148.bracket2370
  (115845279417286196812481052349161724494797/5000000000000000000000000000000000000000) (3878089179675437646941895093143033309357/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2369
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2370
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0370.rows BesselBatch0370.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0370.rows BesselBatch0370.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0370.rows BesselBatch0370.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0370.rows BesselBatch0370.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0370.rows BesselBatch0370.accepted ⟨24,by decide⟩
]
theorem leftAccepted : besselPointCheck (116376150663345346557556338134716979702943/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (116376150663345346557556338134716979702943/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0370.rows BesselBatch0370.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0370.rows BesselBatch0370.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0370.rows BesselBatch0370.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0370.rows BesselBatch0370.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0370.rows BesselBatch0370.accepted ⟨39,by decide⟩
]
theorem rightAccepted : besselPointCheck (117457740716260608876946644887858389217057/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (117457740716260608876946644887858389217057/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0674.rows BesselBatch0674.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0674.rows BesselBatch0674.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0674.rows BesselBatch0674.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0674.rows BesselBatch0674.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0674.rows BesselBatch0674.accepted ⟨8,by decide⟩
]
theorem midAccepted : besselPointCheck (5845847284490148885862574575564384223/250000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (5845847284490148885862574575564384223/250000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0296.rows ScalarLogs0296.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0296.rows ScalarLogs0296.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0296.rows ScalarLogs0296.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0296.rows ScalarLogs0296.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0296.rows ScalarLogs0296.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0296.rows ScalarLogs0296.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0296.rows ScalarLogs0296.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0296.rows ScalarLogs0296.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0296.rows ScalarLogs0296.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0296.rows ScalarLogs0296.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0296.rows ScalarLogs0296.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0296.rows ScalarLogs0296.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0296.rows ScalarLogs0296.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0296.rows ScalarLogs0296.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0296.rows ScalarLogs0296.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0296.rows ScalarLogs0296.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0148.bracket2370 BracketBatch0148.bracket2371 (5845847284490148885862574575564384223/250000000000000000000000000000000000) (3890138926183546617993499768139494797667/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0148.bracket2370 BracketBatch0148.bracket2371
  (5845847284490148885862574575564384223/250000000000000000000000000000000000) (3890138926183546617993499768139494797667/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2370
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2371
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0370.rows BesselBatch0370.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0370.rows BesselBatch0370.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0370.rows BesselBatch0370.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0370.rows BesselBatch0370.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0370.rows BesselBatch0370.accepted ⟨34,by decide⟩
]
theorem leftAccepted : besselPointCheck (234915481432521217753893289775716778434111/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (234915481432521217753893289775716778434111/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0370.rows BesselBatch0370.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0370.rows BesselBatch0370.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0370.rows BesselBatch0370.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0370.rows BesselBatch0370.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0370.rows BesselBatch0370.accepted ⟨49,by decide⟩
]
theorem rightAccepted : besselPointCheck (118559740051821665577080421461184520886869/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (118559740051821665577080421461184520886869/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0674.rows BesselBatch0674.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0674.rows BesselBatch0674.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0674.rows BesselBatch0674.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0674.rows BesselBatch0674.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0674.rows BesselBatch0674.accepted ⟨13,by decide⟩
]
theorem midAccepted : besselPointCheck (472034961536164548908054132698085820207849/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (472034961536164548908054132698085820207849/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0296.rows ScalarLogs0296.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0296.rows ScalarLogs0296.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0296.rows ScalarLogs0296.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0296.rows ScalarLogs0296.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0296.rows ScalarLogs0296.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0296.rows ScalarLogs0296.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0296.rows ScalarLogs0296.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0296.rows ScalarLogs0296.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0296.rows ScalarLogs0296.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0296.rows ScalarLogs0296.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0296.rows ScalarLogs0296.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0296.rows ScalarLogs0296.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0296.rows ScalarLogs0296.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0296.rows ScalarLogs0296.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0296.rows ScalarLogs0296.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0296.rows ScalarLogs0296.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0148.bracket2371 BracketBatch0148.bracket2372 (472034961536164548908054132698085820207849/20000000000000000000000000000000000000000) (243892816771910804554948624959763341721/625000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0148.bracket2371 BracketBatch0148.bracket2372
  (472034961536164548908054132698085820207849/20000000000000000000000000000000000000000) (243892816771910804554948624959763341721/625000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2371
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2372
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0370.rows BesselBatch0370.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0370.rows BesselBatch0370.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0370.rows BesselBatch0370.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0370.rows BesselBatch0370.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0370.rows BesselBatch0370.accepted ⟨44,by decide⟩
]
theorem leftAccepted : besselPointCheck (47423896020728666230832168584473808354747/2000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (47423896020728666230832168584473808354747/2000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0370.rows BesselBatch0370.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0370.rows BesselBatch0370.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0370.rows BesselBatch0370.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0370.rows BesselBatch0370.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0370.rows BesselBatch0370.accepted ⟨59,by decide⟩
]
theorem rightAccepted : besselPointCheck (11968273179080755272414998799269198832543/500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (11968273179080755272414998799269198832543/500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0674.rows BesselBatch0674.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0674.rows BesselBatch0674.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0674.rows BesselBatch0674.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0674.rows BesselBatch0674.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0674.rows BesselBatch0674.accepted ⟨18,by decide⟩
]
theorem midAccepted : besselPointCheck (95296988737051687320492163781550603684919/4000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (95296988737051687320492163781550603684919/4000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0296.rows ScalarLogs0296.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0296.rows ScalarLogs0296.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0296.rows ScalarLogs0296.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0296.rows ScalarLogs0296.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0296.rows ScalarLogs0296.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0296.rows ScalarLogs0296.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0296.rows ScalarLogs0296.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0296.rows ScalarLogs0296.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0296.rows ScalarLogs0296.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0296.rows ScalarLogs0296.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0296.rows ScalarLogs0296.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0296.rows ScalarLogs0296.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0296.rows ScalarLogs0296.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0296.rows ScalarLogs0296.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0296.rows ScalarLogs0296.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0296.rows ScalarLogs0296.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0148.bracket2372 BracketBatch0148.bracket2373 (95296988737051687320492163781550603684919/4000000000000000000000000000000000000000) (489316074666140768455182106396569362749/1250000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0148.bracket2372 BracketBatch0148.bracket2373
  (95296988737051687320492163781550603684919/4000000000000000000000000000000000000000) (489316074666140768455182106396569362749/1250000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2372
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2373
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0370.rows BesselBatch0370.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0370.rows BesselBatch0370.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0370.rows BesselBatch0370.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0370.rows BesselBatch0370.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0370.rows BesselBatch0370.accepted ⟨54,by decide⟩
]
theorem leftAccepted : besselPointCheck (239365463581615105448299975985383976650857/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (239365463581615105448299975985383976650857/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0371.rows BesselBatch0371.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0371.rows BesselBatch0371.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0371.rows BesselBatch0371.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0371.rows BesselBatch0371.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0371.rows BesselBatch0371.accepted ⟨5,by decide⟩
]
theorem rightAccepted : besselPointCheck (241654642963444449479456472139632807584053/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (241654642963444449479456472139632807584053/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0674.rows BesselBatch0674.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0674.rows BesselBatch0674.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0674.rows BesselBatch0674.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0674.rows BesselBatch0674.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0674.rows BesselBatch0674.accepted ⟨23,by decide⟩
]
theorem midAccepted : besselPointCheck (48102010654505955492775644812501678423491/2000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (48102010654505955492775644812501678423491/2000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0296.rows ScalarLogs0296.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0296.rows ScalarLogs0296.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0296.rows ScalarLogs0296.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0296.rows ScalarLogs0296.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0296.rows ScalarLogs0296.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0296.rows ScalarLogs0296.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0296.rows ScalarLogs0296.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0296.rows ScalarLogs0296.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0296.rows ScalarLogs0296.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0296.rows ScalarLogs0296.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0296.rows ScalarLogs0296.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0296.rows ScalarLogs0296.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0296.rows ScalarLogs0296.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0296.rows ScalarLogs0296.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0296.rows ScalarLogs0296.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0296.rows ScalarLogs0296.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0148.bracket2373 BracketBatch0148.bracket2374 (48102010654505955492775644812501678423491/2000000000000000000000000000000000000000) (1963435246635487810390158891429313389663/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0148.bracket2373 BracketBatch0148.bracket2374
  (48102010654505955492775644812501678423491/2000000000000000000000000000000000000000) (1963435246635487810390158891429313389663/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2373
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2374
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0370.rows BesselBatch0370.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0370.rows BesselBatch0370.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0370.rows BesselBatch0370.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0370.rows BesselBatch0370.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0371.rows BesselBatch0371.accepted ⟨0,by decide⟩
]
theorem leftAccepted : besselPointCheck (4833092859268888989589129442792656151681/200000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (4833092859268888989589129442792656151681/200000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0371.rows BesselBatch0371.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0371.rows BesselBatch0371.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0371.rows BesselBatch0371.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0371.rows BesselBatch0371.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0371.rows BesselBatch0371.accepted ⟨15,by decide⟩
]
theorem rightAccepted : besselPointCheck (243988276379038114859954856301498708313497/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (243988276379038114859954856301498708313497/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0674.rows BesselBatch0674.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0674.rows BesselBatch0674.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0674.rows BesselBatch0674.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0674.rows BesselBatch0674.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0674.rows BesselBatch0674.accepted ⟨28,by decide⟩
]
theorem midAccepted : besselPointCheck (485642919342482564339411328441131515897547/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (485642919342482564339411328441131515897547/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0296.rows ScalarLogs0296.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0296.rows ScalarLogs0296.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0296.rows ScalarLogs0296.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0296.rows ScalarLogs0296.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0296.rows ScalarLogs0296.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0296.rows ScalarLogs0296.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0296.rows ScalarLogs0296.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0296.rows ScalarLogs0296.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0296.rows ScalarLogs0296.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0296.rows ScalarLogs0296.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0296.rows ScalarLogs0296.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0296.rows ScalarLogs0296.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0296.rows ScalarLogs0296.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0296.rows ScalarLogs0296.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0296.rows ScalarLogs0296.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0296.rows ScalarLogs0296.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0148.bracket2374 BracketBatch0148.bracket2375 (485642919342482564339411328441131515897547/20000000000000000000000000000000000000000) (3939311722691060372056882209772340105931/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0148.bracket2374 BracketBatch0148.bracket2375
  (485642919342482564339411328441131515897547/20000000000000000000000000000000000000000) (3939311722691060372056882209772340105931/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2374
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2375
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0371.rows BesselBatch0371.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0371.rows BesselBatch0371.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0371.rows BesselBatch0371.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0371.rows BesselBatch0371.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0371.rows BesselBatch0371.accepted ⟨10,by decide⟩
]
theorem leftAccepted : besselPointCheck (121994138189519057429977428150749354156747/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (121994138189519057429977428150749354156747/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0371.rows BesselBatch0371.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0371.rows BesselBatch0371.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0371.rows BesselBatch0371.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0371.rows BesselBatch0371.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0371.rows BesselBatch0371.accepted ⟨25,by decide⟩
]
theorem rightAccepted : besselPointCheck (246367671296735937745948706295460838347351/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (246367671296735937745948706295460838347351/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0674.rows BesselBatch0674.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0674.rows BesselBatch0674.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0674.rows BesselBatch0674.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0674.rows BesselBatch0674.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0674.rows BesselBatch0674.accepted ⟨33,by decide⟩
]
theorem midAccepted : besselPointCheck (98071189535154810521180712519391909332169/4000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (98071189535154810521180712519391909332169/4000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0296.rows ScalarLogs0296.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0296.rows ScalarLogs0296.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0296.rows ScalarLogs0296.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0296.rows ScalarLogs0296.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0296.rows ScalarLogs0296.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0296.rows ScalarLogs0296.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0296.rows ScalarLogs0296.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0296.rows ScalarLogs0296.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0296.rows ScalarLogs0296.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0296.rows ScalarLogs0296.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0296.rows ScalarLogs0296.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0296.rows ScalarLogs0296.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0296.rows ScalarLogs0296.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0296.rows ScalarLogs0296.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0296.rows ScalarLogs0296.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0296.rows ScalarLogs0296.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0148.bracket2375 BracketBatch0148.bracket2376 (98071189535154810521180712519391909332169/4000000000000000000000000000000000000000) (395185323555627720520590924401040917821/1000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0148.bracket2375 BracketBatch0148.bracket2376
  (98071189535154810521180712519391909332169/4000000000000000000000000000000000000000) (395185323555627720520590924401040917821/1000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2375
