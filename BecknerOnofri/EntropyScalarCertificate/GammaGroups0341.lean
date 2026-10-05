module

public import BecknerOnofri.EntropyScalarCertificate.Bessel0426
public import BecknerOnofri.EntropyScalarCertificate.Bessel0427
public import BecknerOnofri.EntropyScalarCertificate.Bessel0702
public import BecknerOnofri.EntropyScalarCertificate.Brackets0170
public import BecknerOnofri.EntropyScalarCertificate.Brackets0171
public import BecknerOnofri.EntropyScalarCertificate.Logs0341
public import BecknerOnofri.ScalarElementaryComposition
public import BecknerOnofri.ScalarGammaEnclosure
public import BecknerOnofri.ScalarLogBesselEndpoints

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2728
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0426.rows BesselBatch0426.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0426.rows BesselBatch0426.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0426.rows BesselBatch0426.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0426.rows BesselBatch0426.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0426.rows BesselBatch0426.accepted ⟨20,by decide⟩
]
theorem leftAccepted : besselPointCheck (417294500498086746662707710146364593441007/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (417294500498086746662707710146364593441007/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0426.rows BesselBatch0426.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0426.rows BesselBatch0426.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0426.rows BesselBatch0426.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0426.rows BesselBatch0426.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0426.rows BesselBatch0426.accepted ⟨35,by decide⟩
]
theorem rightAccepted : besselPointCheck (835980199046450184366464839118613584135561/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (835980199046450184366464839118613584135561/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0702.rows BesselBatch0702.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0702.rows BesselBatch0702.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0702.rows BesselBatch0702.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0702.rows BesselBatch0702.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0702.rows BesselBatch0702.accepted ⟨6,by decide⟩
]
theorem midAccepted : besselPointCheck (66822768001704947107675210376453710840703/800000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (66822768001704947107675210376453710840703/800000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0341.rows ScalarLogs0341.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0341.rows ScalarLogs0341.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0341.rows ScalarLogs0341.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0341.rows ScalarLogs0341.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0341.rows ScalarLogs0341.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0341.rows ScalarLogs0341.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0341.rows ScalarLogs0341.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0341.rows ScalarLogs0341.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0341.rows ScalarLogs0341.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0341.rows ScalarLogs0341.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0341.rows ScalarLogs0341.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0341.rows ScalarLogs0341.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0341.rows ScalarLogs0341.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0341.rows ScalarLogs0341.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0341.rows ScalarLogs0341.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0341.rows ScalarLogs0341.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0170.bracket2728 BracketBatch0170.bracket2729 (66822768001704947107675210376453710840703/800000000000000000000000000000000000000) (1458899875187532289759396900106431171477/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0170.bracket2728 BracketBatch0170.bracket2729
  (66822768001704947107675210376453710840703/800000000000000000000000000000000000000) (1458899875187532289759396900106431171477/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2728
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2729
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0426.rows BesselBatch0426.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0426.rows BesselBatch0426.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0426.rows BesselBatch0426.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0426.rows BesselBatch0426.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0426.rows BesselBatch0426.accepted ⟨30,by decide⟩
]
theorem leftAccepted : besselPointCheck (417990099523225092183232419559306792067779/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (417990099523225092183232419559306792067779/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0426.rows BesselBatch0426.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0426.rows BesselBatch0426.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0426.rows BesselBatch0426.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0426.rows BesselBatch0426.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0426.rows BesselBatch0426.accepted ⟨45,by decide⟩
]
theorem rightAccepted : besselPointCheck (837376049965090246665505415613047411714877/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (837376049965090246665505415613047411714877/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0702.rows BesselBatch0702.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0702.rows BesselBatch0702.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0702.rows BesselBatch0702.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0702.rows BesselBatch0702.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0702.rows BesselBatch0702.accepted ⟨11,by decide⟩
]
theorem midAccepted : besselPointCheck (334671249802308086206394050946332199170087/4000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (334671249802308086206394050946332199170087/4000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0341.rows ScalarLogs0341.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0341.rows ScalarLogs0341.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0341.rows ScalarLogs0341.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0341.rows ScalarLogs0341.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0341.rows ScalarLogs0341.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0341.rows ScalarLogs0341.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0341.rows ScalarLogs0341.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0341.rows ScalarLogs0341.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0341.rows ScalarLogs0341.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0341.rows ScalarLogs0341.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0341.rows ScalarLogs0341.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0341.rows ScalarLogs0341.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0341.rows ScalarLogs0341.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0341.rows ScalarLogs0341.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0341.rows ScalarLogs0341.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0341.rows ScalarLogs0341.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0170.bracket2729 BracketBatch0170.bracket2730 (334671249802308086206394050946332199170087/4000000000000000000000000000000000000000) (291907722024418635430799669249691414399/500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0170.bracket2729 BracketBatch0170.bracket2730
  (334671249802308086206394050946332199170087/4000000000000000000000000000000000000000) (291907722024418635430799669249691414399/500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2729
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2730
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0426.rows BesselBatch0426.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0426.rows BesselBatch0426.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0426.rows BesselBatch0426.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0426.rows BesselBatch0426.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0426.rows BesselBatch0426.accepted ⟨40,by decide⟩
]
theorem leftAccepted : besselPointCheck (418688024982545123332752707806523705857437/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (418688024982545123332752707806523705857437/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0426.rows BesselBatch0426.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0426.rows BesselBatch0426.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0426.rows BesselBatch0426.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0426.rows BesselBatch0426.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0426.rows BesselBatch0426.accepted ⟨55,by decide⟩
]
theorem rightAccepted : besselPointCheck (838776577133340505440888694600828505393741/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (838776577133340505440888694600828505393741/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0702.rows BesselBatch0702.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0702.rows BesselBatch0702.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0702.rows BesselBatch0702.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0702.rows BesselBatch0702.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0702.rows BesselBatch0702.accepted ⟨16,by decide⟩
]
theorem midAccepted : besselPointCheck (335230525419686150421278822042775183421723/4000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (335230525419686150421278822042775183421723/4000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0341.rows ScalarLogs0341.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0341.rows ScalarLogs0341.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0341.rows ScalarLogs0341.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0341.rows ScalarLogs0341.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0341.rows ScalarLogs0341.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0341.rows ScalarLogs0341.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0341.rows ScalarLogs0341.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0341.rows ScalarLogs0341.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0341.rows ScalarLogs0341.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0341.rows ScalarLogs0341.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0341.rows ScalarLogs0341.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0341.rows ScalarLogs0341.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0341.rows ScalarLogs0341.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0341.rows ScalarLogs0341.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0341.rows ScalarLogs0341.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0341.rows ScalarLogs0341.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0170.bracket2730 BracketBatch0170.bracket2731 (335230525419686150421278822042775183421723/4000000000000000000000000000000000000000) (5840713762481680893522272133618366921809/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0170.bracket2730 BracketBatch0170.bracket2731
  (335230525419686150421278822042775183421723/4000000000000000000000000000000000000000) (5840713762481680893522272133618366921809/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2730
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2731
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0426.rows BesselBatch0426.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0426.rows BesselBatch0426.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0426.rows BesselBatch0426.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0426.rows BesselBatch0426.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0426.rows BesselBatch0426.accepted ⟨50,by decide⟩
]
theorem leftAccepted : besselPointCheck (419388288566670252720444347300414252696869/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (419388288566670252720444347300414252696869/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0426.rows BesselBatch0426.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0426.rows BesselBatch0426.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0426.rows BesselBatch0426.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0427.rows BesselBatch0427.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0427.rows BesselBatch0427.accepted ⟨1,by decide⟩
]
theorem rightAccepted : besselPointCheck (840181804089368905637413295613715923923081/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (840181804089368905637413295613715923923081/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0702.rows BesselBatch0702.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0702.rows BesselBatch0702.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0702.rows BesselBatch0702.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0702.rows BesselBatch0702.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0702.rows BesselBatch0702.accepted ⟨21,by decide⟩
]
theorem midAccepted : besselPointCheck (1678958381222709411078301990214544429316819/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1678958381222709411078301990214544429316819/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0341.rows ScalarLogs0341.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0341.rows ScalarLogs0341.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0341.rows ScalarLogs0341.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0341.rows ScalarLogs0341.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0341.rows ScalarLogs0341.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0341.rows ScalarLogs0341.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0341.rows ScalarLogs0341.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0341.rows ScalarLogs0341.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0341.rows ScalarLogs0341.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0341.rows ScalarLogs0341.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0341.rows ScalarLogs0341.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0341.rows ScalarLogs0341.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0341.rows ScalarLogs0341.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0341.rows ScalarLogs0341.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0341.rows ScalarLogs0341.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0341.rows ScalarLogs0341.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0170.bracket2731 BracketBatch0170.bracket2732 (1678958381222709411078301990214544429316819/20000000000000000000000000000000000000000) (5843277481108372385070595408246890705979/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0170.bracket2731 BracketBatch0170.bracket2732
  (1678958381222709411078301990214544429316819/20000000000000000000000000000000000000000) (5843277481108372385070595408246890705979/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2731
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2732
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0426.rows BesselBatch0426.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0426.rows BesselBatch0426.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0426.rows BesselBatch0426.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0426.rows BesselBatch0426.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0426.rows BesselBatch0426.accepted ⟨60,by decide⟩
]
theorem leftAccepted : besselPointCheck (420090902044684452818706647806857961961539/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (420090902044684452818706647806857961961539/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0427.rows BesselBatch0427.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0427.rows BesselBatch0427.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0427.rows BesselBatch0427.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0427.rows BesselBatch0427.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0427.rows BesselBatch0427.accepted ⟨11,by decide⟩
]
theorem rightAccepted : besselPointCheck (841591754529583176797963671438301547728703/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (841591754529583176797963671438301547728703/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0702.rows BesselBatch0702.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0702.rows BesselBatch0702.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0702.rows BesselBatch0702.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0702.rows BesselBatch0702.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0702.rows BesselBatch0702.accepted ⟨26,by decide⟩
]
theorem midAccepted : besselPointCheck (1681773558618952082435376967052017471651781/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1681773558618952082435376967052017471651781/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0341.rows ScalarLogs0341.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0341.rows ScalarLogs0341.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0341.rows ScalarLogs0341.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0341.rows ScalarLogs0341.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0341.rows ScalarLogs0341.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0341.rows ScalarLogs0341.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0341.rows ScalarLogs0341.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0341.rows ScalarLogs0341.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0341.rows ScalarLogs0341.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0341.rows ScalarLogs0341.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0341.rows ScalarLogs0341.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0341.rows ScalarLogs0341.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0341.rows ScalarLogs0341.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0341.rows ScalarLogs0341.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0341.rows ScalarLogs0341.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0341.rows ScalarLogs0341.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0170.bracket2732 BracketBatch0170.bracket2733 (1681773558618952082435376967052017471651781/20000000000000000000000000000000000000000) (5845845610816214008673188514908560027171/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0170.bracket2732 BracketBatch0170.bracket2733
  (1681773558618952082435376967052017471651781/20000000000000000000000000000000000000000) (5845845610816214008673188514908560027171/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2732
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2733
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0427.rows BesselBatch0427.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0427.rows BesselBatch0427.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0427.rows BesselBatch0427.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0427.rows BesselBatch0427.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0427.rows BesselBatch0427.accepted ⟨6,by decide⟩
]
theorem leftAccepted : besselPointCheck (8415917545295831767979636714383015477287/100000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (8415917545295831767979636714383015477287/100000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0427.rows BesselBatch0427.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0427.rows BesselBatch0427.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0427.rows BesselBatch0427.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0427.rows BesselBatch0427.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0427.rows BesselBatch0427.accepted ⟨21,by decide⟩
]
theorem rightAccepted : besselPointCheck (8430064523099628177823371392579548152073/100000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (8430064523099628177823371392579548152073/100000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0702.rows BesselBatch0702.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0702.rows BesselBatch0702.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0702.rows BesselBatch0702.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0702.rows BesselBatch0702.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0702.rows BesselBatch0702.accepted ⟨31,by decide⟩
]
theorem midAccepted : besselPointCheck (210574775854943249322537601337032045367/2500000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (210574775854943249322537601337032045367/2500000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0341.rows ScalarLogs0341.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0341.rows ScalarLogs0341.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0341.rows ScalarLogs0341.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0341.rows ScalarLogs0341.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0341.rows ScalarLogs0341.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0341.rows ScalarLogs0341.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0341.rows ScalarLogs0341.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0341.rows ScalarLogs0341.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0341.rows ScalarLogs0341.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0341.rows ScalarLogs0341.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0341.rows ScalarLogs0341.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0341.rows ScalarLogs0341.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0341.rows ScalarLogs0341.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0341.rows ScalarLogs0341.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0341.rows ScalarLogs0341.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0341.rows ScalarLogs0341.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0170.bracket2733 BracketBatch0170.bracket2734 (210574775854943249322537601337032045367/2500000000000000000000000000000000000) (5848418166122857976951624033644822966151/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0170.bracket2733 BracketBatch0170.bracket2734
  (210574775854943249322537601337032045367/2500000000000000000000000000000000000) (5848418166122857976951624033644822966151/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2733
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2734
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0427.rows BesselBatch0427.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0427.rows BesselBatch0427.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0427.rows BesselBatch0427.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0427.rows BesselBatch0427.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0427.rows BesselBatch0427.accepted ⟨16,by decide⟩
]
theorem leftAccepted : besselPointCheck (843006452309962817782337139257954815207297/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (843006452309962817782337139257954815207297/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0427.rows BesselBatch0427.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0427.rows BesselBatch0427.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0427.rows BesselBatch0427.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0427.rows BesselBatch0427.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0427.rows BesselBatch0427.accepted ⟨31,by decide⟩
]
theorem rightAccepted : besselPointCheck (844425921447404558565856685076524650559721/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (844425921447404558565856685076524650559721/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0702.rows BesselBatch0702.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0702.rows BesselBatch0702.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0702.rows BesselBatch0702.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0702.rows BesselBatch0702.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0702.rows BesselBatch0702.accepted ⟨36,by decide⟩
]
theorem midAccepted : besselPointCheck (843716186878683688174096912167239732883509/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (843716186878683688174096912167239732883509/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0341.rows ScalarLogs0341.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0341.rows ScalarLogs0341.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0341.rows ScalarLogs0341.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0341.rows ScalarLogs0341.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0341.rows ScalarLogs0341.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0341.rows ScalarLogs0341.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0341.rows ScalarLogs0341.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0341.rows ScalarLogs0341.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0341.rows ScalarLogs0341.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0341.rows ScalarLogs0341.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0341.rows ScalarLogs0341.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0341.rows ScalarLogs0341.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0341.rows ScalarLogs0341.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0341.rows ScalarLogs0341.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0341.rows ScalarLogs0341.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0341.rows ScalarLogs0341.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0170.bracket2734 BracketBatch0170.bracket2735 (843716186878683688174096912167239732883509/10000000000000000000000000000000000000000) (5850995161616282458355970383863504860799/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0170.bracket2734 BracketBatch0170.bracket2735
  (843716186878683688174096912167239732883509/10000000000000000000000000000000000000000) (5850995161616282458355970383863504860799/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2734
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2735
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0427.rows BesselBatch0427.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0427.rows BesselBatch0427.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0427.rows BesselBatch0427.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0427.rows BesselBatch0427.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0427.rows BesselBatch0427.accepted ⟨26,by decide⟩
]
theorem leftAccepted : besselPointCheck (422212960723702279282928342538262325279859/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (422212960723702279282928342538262325279859/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0427.rows BesselBatch0427.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0427.rows BesselBatch0427.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0427.rows BesselBatch0427.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0427.rows BesselBatch0427.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0427.rows BesselBatch0427.accepted ⟨41,by decide⟩
]
theorem rightAccepted : besselPointCheck (52865636632567591154695742075116059906829/625000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (52865636632567591154695742075116059906829/625000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0702.rows BesselBatch0702.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0702.rows BesselBatch0702.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0702.rows BesselBatch0702.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0702.rows BesselBatch0702.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0702.rows BesselBatch0702.accepted ⟨41,by decide⟩
]
theorem midAccepted : besselPointCheck (845138053784243008520494279139190804534491/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (845138053784243008520494279139190804534491/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0341.rows ScalarLogs0341.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0341.rows ScalarLogs0341.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0341.rows ScalarLogs0341.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0341.rows ScalarLogs0341.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0341.rows ScalarLogs0341.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0341.rows ScalarLogs0341.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0341.rows ScalarLogs0341.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0341.rows ScalarLogs0341.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0341.rows ScalarLogs0341.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0341.rows ScalarLogs0341.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0341.rows ScalarLogs0341.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0341.rows ScalarLogs0341.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0341.rows ScalarLogs0341.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0341.rows ScalarLogs0341.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0341.rows ScalarLogs0341.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0341.rows ScalarLogs0341.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0170.bracket2735 BracketBatch0171.bracket2736 (845138053784243008520494279139190804534491/10000000000000000000000000000000000000000) (5853576611955235510455466517997323805477/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0170.bracket2735 BracketBatch0171.bracket2736
  (845138053784243008520494279139190804534491/10000000000000000000000000000000000000000) (5853576611955235510455466517997323805477/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2735
