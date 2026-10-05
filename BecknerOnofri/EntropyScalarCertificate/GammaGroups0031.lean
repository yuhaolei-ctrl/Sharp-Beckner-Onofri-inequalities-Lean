module

public import BecknerOnofri.EntropyScalarCertificate.Bessel0038
public import BecknerOnofri.EntropyScalarCertificate.Bessel0039
public import BecknerOnofri.EntropyScalarCertificate.Bessel0040
public import BecknerOnofri.EntropyScalarCertificate.Bessel0508
public import BecknerOnofri.EntropyScalarCertificate.Brackets0015
public import BecknerOnofri.EntropyScalarCertificate.Brackets0016
public import BecknerOnofri.EntropyScalarCertificate.Logs0031
public import BecknerOnofri.ScalarElementaryComposition
public import BecknerOnofri.ScalarGammaEnclosure
public import BecknerOnofri.ScalarLogBesselEndpoints

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0248
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0038.rows BesselBatch0038.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0038.rows BesselBatch0038.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0038.rows BesselBatch0038.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0038.rows BesselBatch0038.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0038.rows BesselBatch0038.accepted ⟨52,by decide⟩
]
theorem leftAccepted : besselPointCheck (1067028578793084840623664985369937423731/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1067028578793084840623664985369937423731/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0038.rows BesselBatch0038.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0039.rows BesselBatch0039.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0039.rows BesselBatch0039.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0039.rows BesselBatch0039.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0039.rows BesselBatch0039.accepted ⟨3,by decide⟩
]
theorem rightAccepted : besselPointCheck (534531476102581471040894204517030928639/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (534531476102581471040894204517030928639/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0508.rows BesselBatch0508.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0508.rows BesselBatch0508.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0508.rows BesselBatch0508.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0508.rows BesselBatch0508.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0508.rows BesselBatch0508.accepted ⟨22,by decide⟩
]
theorem midAccepted : besselPointCheck (2136091530998247782705453394403999281009/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (2136091530998247782705453394403999281009/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0031.rows ScalarLogs0031.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0031.rows ScalarLogs0031.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0031.rows ScalarLogs0031.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0031.rows ScalarLogs0031.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0031.rows ScalarLogs0031.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0031.rows ScalarLogs0031.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0031.rows ScalarLogs0031.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0031.rows ScalarLogs0031.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0031.rows ScalarLogs0031.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0031.rows ScalarLogs0031.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0031.rows ScalarLogs0031.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0031.rows ScalarLogs0031.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0031.rows ScalarLogs0031.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0031.rows ScalarLogs0031.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0031.rows ScalarLogs0031.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0031.rows ScalarLogs0031.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0015.bracket0248 BracketBatch0015.bracket0249 (2136091530998247782705453394403999281009/20000000000000000000000000000000000000000) (24690114624545367967263308134203073/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0015.bracket0248 BracketBatch0015.bracket0249
  (2136091530998247782705453394403999281009/20000000000000000000000000000000000000000) (24690114624545367967263308134203073/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0248
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0249
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0038.rows BesselBatch0038.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0038.rows BesselBatch0038.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0038.rows BesselBatch0038.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0038.rows BesselBatch0038.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0038.rows BesselBatch0038.accepted ⟨62,by decide⟩
]
theorem leftAccepted : besselPointCheck (42762518088206517683271536361362474291/400000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (42762518088206517683271536361362474291/400000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0039.rows BesselBatch0039.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0039.rows BesselBatch0039.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0039.rows BesselBatch0039.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0039.rows BesselBatch0039.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0039.rows BesselBatch0039.accepted ⟨13,by decide⟩
]
theorem rightAccepted : besselPointCheck (535548728636575128431567424287606922811/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (535548728636575128431567424287606922811/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0508.rows BesselBatch0508.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0508.rows BesselBatch0508.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0508.rows BesselBatch0508.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0508.rows BesselBatch0508.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0508.rows BesselBatch0508.accepted ⟨27,by decide⟩
]
theorem midAccepted : besselPointCheck (2140160409478313198944923257609275702897/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (2140160409478313198944923257609275702897/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0031.rows ScalarLogs0031.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0031.rows ScalarLogs0031.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0031.rows ScalarLogs0031.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0031.rows ScalarLogs0031.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0031.rows ScalarLogs0031.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0031.rows ScalarLogs0031.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0031.rows ScalarLogs0031.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0031.rows ScalarLogs0031.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0031.rows ScalarLogs0031.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0031.rows ScalarLogs0031.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0031.rows ScalarLogs0031.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0031.rows ScalarLogs0031.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0031.rows ScalarLogs0031.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0031.rows ScalarLogs0031.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0031.rows ScalarLogs0031.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0031.rows ScalarLogs0031.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0015.bracket0249 BracketBatch0015.bracket0250 (2140160409478313198944923257609275702897/20000000000000000000000000000000000000000) (24878007657342277181089961296941553/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0015.bracket0249 BracketBatch0015.bracket0250
  (2140160409478313198944923257609275702897/20000000000000000000000000000000000000000) (24878007657342277181089961296941553/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0249
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0250
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0039.rows BesselBatch0039.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0039.rows BesselBatch0039.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0039.rows BesselBatch0039.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0039.rows BesselBatch0039.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0039.rows BesselBatch0039.accepted ⟨8,by decide⟩
]
theorem leftAccepted : besselPointCheck (1071097457273150256863134848575213845619/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1071097457273150256863134848575213845619/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0039.rows BesselBatch0039.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0039.rows BesselBatch0039.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0039.rows BesselBatch0039.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0039.rows BesselBatch0039.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0039.rows BesselBatch0039.accepted ⟨23,by decide⟩
]
theorem rightAccepted : besselPointCheck (536566047130282401719582803452907308941/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (536566047130282401719582803452907308941/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0508.rows BesselBatch0508.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0508.rows BesselBatch0508.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0508.rows BesselBatch0508.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0508.rows BesselBatch0508.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0508.rows BesselBatch0508.accepted ⟨32,by decide⟩
]
theorem midAccepted : besselPointCheck (2144229551533715060302300455481028463501/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (2144229551533715060302300455481028463501/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0031.rows ScalarLogs0031.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0031.rows ScalarLogs0031.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0031.rows ScalarLogs0031.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0031.rows ScalarLogs0031.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0031.rows ScalarLogs0031.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0031.rows ScalarLogs0031.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0031.rows ScalarLogs0031.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0031.rows ScalarLogs0031.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0031.rows ScalarLogs0031.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0031.rows ScalarLogs0031.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0031.rows ScalarLogs0031.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0031.rows ScalarLogs0031.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0031.rows ScalarLogs0031.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0031.rows ScalarLogs0031.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0031.rows ScalarLogs0031.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0031.rows ScalarLogs0031.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0015.bracket0250 BracketBatch0015.bracket0251 (2144229551533715060302300455481028463501/20000000000000000000000000000000000000000) (100267876719733227534877851937522293/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0015.bracket0250 BracketBatch0015.bracket0251
  (2144229551533715060302300455481028463501/20000000000000000000000000000000000000000) (100267876719733227534877851937522293/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0250
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0251
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0039.rows BesselBatch0039.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0039.rows BesselBatch0039.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0039.rows BesselBatch0039.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0039.rows BesselBatch0039.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0039.rows BesselBatch0039.accepted ⟨18,by decide⟩
]
theorem leftAccepted : besselPointCheck (1073132094260564803439165606905814617879/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1073132094260564803439165606905814617879/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0039.rows BesselBatch0039.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0039.rows BesselBatch0039.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0039.rows BesselBatch0039.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0039.rows BesselBatch0039.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0039.rows BesselBatch0039.accepted ⟨33,by decide⟩
]
theorem rightAccepted : besselPointCheck (1075166863431016498194694022861585653753/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1075166863431016498194694022861585653753/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0508.rows BesselBatch0508.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0508.rows BesselBatch0508.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0508.rows BesselBatch0508.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0508.rows BesselBatch0508.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0508.rows BesselBatch0508.accepted ⟨37,by decide⟩
]
theorem midAccepted : besselPointCheck (134268684855723831352116226860462516977/1250000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (134268684855723831352116226860462516977/1250000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0031.rows ScalarLogs0031.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0031.rows ScalarLogs0031.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0031.rows ScalarLogs0031.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0031.rows ScalarLogs0031.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0031.rows ScalarLogs0031.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0031.rows ScalarLogs0031.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0031.rows ScalarLogs0031.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0031.rows ScalarLogs0031.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0031.rows ScalarLogs0031.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0031.rows ScalarLogs0031.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0031.rows ScalarLogs0031.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0031.rows ScalarLogs0031.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0031.rows ScalarLogs0031.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0031.rows ScalarLogs0031.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0031.rows ScalarLogs0031.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0031.rows ScalarLogs0031.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0015.bracket0251 BracketBatch0015.bracket0252 (134268684855723831352116226860462516977/1250000000000000000000000000000000000000) (101028013052849275858619243237332047/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0015.bracket0251 BracketBatch0015.bracket0252
  (134268684855723831352116226860462516977/1250000000000000000000000000000000000000) (101028013052849275858619243237332047/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0251
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0252
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0039.rows BesselBatch0039.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0039.rows BesselBatch0039.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0039.rows BesselBatch0039.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0039.rows BesselBatch0039.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0039.rows BesselBatch0039.accepted ⟨28,by decide⟩
]
theorem leftAccepted : besselPointCheck (860133490744813198555755218289268523/8000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (860133490744813198555755218289268523/8000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0039.rows BesselBatch0039.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0039.rows BesselBatch0039.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0039.rows BesselBatch0039.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0039.rows BesselBatch0039.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0039.rows BesselBatch0039.accepted ⟨43,by decide⟩
]
theorem rightAccepted : besselPointCheck (1077201765048207354292460141498711863841/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1077201765048207354292460141498711863841/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0508.rows BesselBatch0508.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0508.rows BesselBatch0508.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0508.rows BesselBatch0508.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0508.rows BesselBatch0508.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0508.rows BesselBatch0508.accepted ⟨42,by decide⟩
]
theorem midAccepted : besselPointCheck (2152368628479223852487154164360297517591/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (2152368628479223852487154164360297517591/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0031.rows ScalarLogs0031.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0031.rows ScalarLogs0031.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0031.rows ScalarLogs0031.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0031.rows ScalarLogs0031.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0031.rows ScalarLogs0031.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0031.rows ScalarLogs0031.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0031.rows ScalarLogs0031.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0031.rows ScalarLogs0031.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0031.rows ScalarLogs0031.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0031.rows ScalarLogs0031.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0031.rows ScalarLogs0031.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0031.rows ScalarLogs0031.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0031.rows ScalarLogs0031.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0031.rows ScalarLogs0031.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0031.rows ScalarLogs0031.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0031.rows ScalarLogs0031.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0015.bracket0252 BracketBatch0015.bracket0253 (2152368628479223852487154164360297517591/20000000000000000000000000000000000000000) (50896227972155778620380875808324021/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0015.bracket0252 BracketBatch0015.bracket0253
  (2152368628479223852487154164360297517591/20000000000000000000000000000000000000000) (50896227972155778620380875808324021/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0252
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0253
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0039.rows BesselBatch0039.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0039.rows BesselBatch0039.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0039.rows BesselBatch0039.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0039.rows BesselBatch0039.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0039.rows BesselBatch0039.accepted ⟨38,by decide⟩
]
theorem leftAccepted : besselPointCheck (538600882524103677146230070749355931919/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (538600882524103677146230070749355931919/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0039.rows BesselBatch0039.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0039.rows BesselBatch0039.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0039.rows BesselBatch0039.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0039.rows BesselBatch0039.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0039.rows BesselBatch0039.accepted ⟨53,by decide⟩
]
theorem rightAccepted : besselPointCheck (53961839968796584034693920632177146433/500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (53961839968796584034693920632177146433/500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0508.rows BesselBatch0508.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0508.rows BesselBatch0508.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0508.rows BesselBatch0508.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0508.rows BesselBatch0508.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0508.rows BesselBatch0508.accepted ⟨47,by decide⟩
]
theorem midAccepted : besselPointCheck (1078219282212069517493169277071127396249/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1078219282212069517493169277071127396249/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0031.rows ScalarLogs0031.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0031.rows ScalarLogs0031.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0031.rows ScalarLogs0031.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0031.rows ScalarLogs0031.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0031.rows ScalarLogs0031.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0031.rows ScalarLogs0031.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0031.rows ScalarLogs0031.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0031.rows ScalarLogs0031.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0031.rows ScalarLogs0031.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0031.rows ScalarLogs0031.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0031.rows ScalarLogs0031.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0031.rows ScalarLogs0031.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0031.rows ScalarLogs0031.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0031.rows ScalarLogs0031.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0031.rows ScalarLogs0031.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0031.rows ScalarLogs0031.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0015.bracket0253 BracketBatch0015.bracket0254 (1078219282212069517493169277071127396249/10000000000000000000000000000000000000000) (25640305435435342772130700053792157/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0015.bracket0253 BracketBatch0015.bracket0254
  (1078219282212069517493169277071127396249/10000000000000000000000000000000000000000) (25640305435435342772130700053792157/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0253
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0254
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0039.rows BesselBatch0039.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0039.rows BesselBatch0039.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0039.rows BesselBatch0039.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0039.rows BesselBatch0039.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0039.rows BesselBatch0039.accepted ⟨48,by decide⟩
]
theorem leftAccepted : besselPointCheck (1079236799375931680693878412643542928657/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1079236799375931680693878412643542928657/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0039.rows BesselBatch0039.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0039.rows BesselBatch0039.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0039.rows BesselBatch0039.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0039.rows BesselBatch0039.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0039.rows BesselBatch0039.accepted ⟨63,by decide⟩
]
theorem rightAccepted : besselPointCheck (1081271966678076281336331080900782690849/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1081271966678076281336331080900782690849/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0508.rows BesselBatch0508.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0508.rows BesselBatch0508.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0508.rows BesselBatch0508.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0508.rows BesselBatch0508.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0508.rows BesselBatch0508.accepted ⟨52,by decide⟩
]
theorem midAccepted : besselPointCheck (1080254383027003981015104746772162809753/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1080254383027003981015104746772162809753/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0031.rows ScalarLogs0031.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0031.rows ScalarLogs0031.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0031.rows ScalarLogs0031.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0031.rows ScalarLogs0031.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0031.rows ScalarLogs0031.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0031.rows ScalarLogs0031.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0031.rows ScalarLogs0031.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0031.rows ScalarLogs0031.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0031.rows ScalarLogs0031.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0031.rows ScalarLogs0031.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0031.rows ScalarLogs0031.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0031.rows ScalarLogs0031.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0031.rows ScalarLogs0031.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0031.rows ScalarLogs0031.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0031.rows ScalarLogs0031.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0031.rows ScalarLogs0031.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0015.bracket0254 BracketBatch0015.bracket0255 (1080254383027003981015104746772162809753/10000000000000000000000000000000000000000) (103334326824795169719054500744830453/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0015.bracket0254 BracketBatch0015.bracket0255
  (1080254383027003981015104746772162809753/10000000000000000000000000000000000000000) (103334326824795169719054500744830453/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0254
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0255
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0039.rows BesselBatch0039.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0039.rows BesselBatch0039.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0039.rows BesselBatch0039.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0039.rows BesselBatch0039.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0039.rows BesselBatch0039.accepted ⟨58,by decide⟩
]
theorem leftAccepted : besselPointCheck (540635983339038140668165540450391345423/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (540635983339038140668165540450391345423/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0040.rows BesselBatch0040.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0040.rows BesselBatch0040.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0040.rows BesselBatch0040.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0040.rows BesselBatch0040.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0040.rows BesselBatch0040.accepted ⟨9,by decide⟩
]
theorem rightAccepted : besselPointCheck (33853352100581895452105638075961290257/312500000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (33853352100581895452105638075961290257/312500000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0508.rows BesselBatch0508.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0508.rows BesselBatch0508.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0508.rows BesselBatch0508.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0508.rows BesselBatch0508.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0508.rows BesselBatch0508.accepted ⟨57,by decide⟩
]
theorem midAccepted : besselPointCheck (216457923389669693580371149933154397907/2000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (216457923389669693580371149933154397907/2000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0031.rows ScalarLogs0031.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0031.rows ScalarLogs0031.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0031.rows ScalarLogs0031.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0031.rows ScalarLogs0031.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0031.rows ScalarLogs0031.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0031.rows ScalarLogs0031.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0031.rows ScalarLogs0031.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0031.rows ScalarLogs0031.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0031.rows ScalarLogs0031.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0031.rows ScalarLogs0031.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0031.rows ScalarLogs0031.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0031.rows ScalarLogs0031.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0031.rows ScalarLogs0031.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0031.rows ScalarLogs0031.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0031.rows ScalarLogs0031.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0031.rows ScalarLogs0031.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0015.bracket0255 BracketBatch0016.bracket0256 (216457923389669693580371149933154397907/2000000000000000000000000000000000000000) (5205589380258636629582243044912897/500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0015.bracket0255 BracketBatch0016.bracket0256
  (216457923389669693580371149933154397907/2000000000000000000000000000000000000000) (5205589380258636629582243044912897/500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0255
