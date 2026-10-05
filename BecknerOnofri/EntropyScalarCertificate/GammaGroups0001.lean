module

public import BecknerOnofri.EntropyScalarCertificate.Bessel0001
public import BecknerOnofri.EntropyScalarCertificate.Bessel0002
public import BecknerOnofri.EntropyScalarCertificate.Bessel0489
public import BecknerOnofri.EntropyScalarCertificate.Bessel0490
public import BecknerOnofri.EntropyScalarCertificate.Brackets0000
public import BecknerOnofri.EntropyScalarCertificate.Brackets0001
public import BecknerOnofri.EntropyScalarCertificate.Logs0001
public import BecknerOnofri.ScalarElementaryComposition
public import BecknerOnofri.ScalarGammaEnclosure
public import BecknerOnofri.ScalarLogBesselEndpoints

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0008
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0001.rows BesselBatch0001.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0001.rows BesselBatch0001.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0001.rows BesselBatch0001.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0001.rows BesselBatch0001.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0001.rows BesselBatch0001.accepted ⟨20,by decide⟩
]
theorem leftAccepted : besselPointCheck (630248408863463865341974709946209150129/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (630248408863463865341974709946209150129/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0001.rows BesselBatch0001.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0001.rows BesselBatch0001.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0001.rows BesselBatch0001.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0001.rows BesselBatch0001.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0001.rows BesselBatch0001.accepted ⟨35,by decide⟩
]
theorem rightAccepted : besselPointCheck (157687848737030998523096613991828746903/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (157687848737030998523096613991828746903/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0489.rows BesselBatch0489.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0489.rows BesselBatch0489.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0489.rows BesselBatch0489.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0489.rows BesselBatch0489.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0489.rows BesselBatch0489.accepted ⟨38,by decide⟩
]
theorem midAccepted : besselPointCheck (1260999803811587859434361165913524137741/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1260999803811587859434361165913524137741/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0001.rows ScalarLogs0001.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0001.rows ScalarLogs0001.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0001.rows ScalarLogs0001.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0001.rows ScalarLogs0001.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0001.rows ScalarLogs0001.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0001.rows ScalarLogs0001.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0001.rows ScalarLogs0001.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0001.rows ScalarLogs0001.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0001.rows ScalarLogs0001.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0001.rows ScalarLogs0001.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0001.rows ScalarLogs0001.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0001.rows ScalarLogs0001.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0001.rows ScalarLogs0001.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0001.rows ScalarLogs0001.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0001.rows ScalarLogs0001.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0001.rows ScalarLogs0001.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0000.bracket0008 BracketBatch0000.bracket0009 (1260999803811587859434361165913524137741/20000000000000000000000000000000000000000) (12189575322240620013423482003916497/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0000.bracket0008 BracketBatch0000.bracket0009
  (1260999803811587859434361165913524137741/20000000000000000000000000000000000000000) (12189575322240620013423482003916497/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0008
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0009
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0001.rows BesselBatch0001.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0001.rows BesselBatch0001.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0001.rows BesselBatch0001.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0001.rows BesselBatch0001.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0001.rows BesselBatch0001.accepted ⟨30,by decide⟩
]
theorem leftAccepted : besselPointCheck (630751394948123994092386455967314987609/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (630751394948123994092386455967314987609/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0001.rows BesselBatch0001.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0001.rows BesselBatch0001.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0001.rows BesselBatch0001.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0001.rows BesselBatch0001.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0001.rows BesselBatch0001.accepted ⟨45,by decide⟩
]
theorem rightAccepted : besselPointCheck (631254385806416997383882163219390295053/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (631254385806416997383882163219390295053/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0489.rows BesselBatch0489.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0489.rows BesselBatch0489.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0489.rows BesselBatch0489.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0489.rows BesselBatch0489.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0489.rows BesselBatch0489.accepted ⟨43,by decide⟩
]
theorem midAccepted : besselPointCheck (631002890377270495738134309593352641331/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (631002890377270495738134309593352641331/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0001.rows ScalarLogs0001.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0001.rows ScalarLogs0001.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0001.rows ScalarLogs0001.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0001.rows ScalarLogs0001.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0001.rows ScalarLogs0001.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0001.rows ScalarLogs0001.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0001.rows ScalarLogs0001.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0001.rows ScalarLogs0001.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0001.rows ScalarLogs0001.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0001.rows ScalarLogs0001.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0001.rows ScalarLogs0001.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0001.rows ScalarLogs0001.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0001.rows ScalarLogs0001.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0001.rows ScalarLogs0001.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0001.rows ScalarLogs0001.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0001.rows ScalarLogs0001.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0000.bracket0009 BracketBatch0000.bracket0010 (631002890377270495738134309593352641331/10000000000000000000000000000000000000000) (12228491593277673347746984816062933/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0000.bracket0009 BracketBatch0000.bracket0010
  (631002890377270495738134309593352641331/10000000000000000000000000000000000000000) (12228491593277673347746984816062933/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0009
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0010
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0001.rows BesselBatch0001.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0001.rows BesselBatch0001.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0001.rows BesselBatch0001.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0001.rows BesselBatch0001.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0001.rows BesselBatch0001.accepted ⟨40,by decide⟩
]
theorem leftAccepted : besselPointCheck (12625087716128339947677643264387805901/200000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (12625087716128339947677643264387805901/200000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0001.rows BesselBatch0001.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0001.rows BesselBatch0001.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0001.rows BesselBatch0001.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0001.rows BesselBatch0001.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0001.rows BesselBatch0001.accepted ⟨55,by decide⟩
]
theorem rightAccepted : besselPointCheck (157939345360554614509915480599995234283/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (157939345360554614509915480599995234283/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0489.rows BesselBatch0489.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0489.rows BesselBatch0489.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0489.rows BesselBatch0489.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0489.rows BesselBatch0489.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0489.rows BesselBatch0489.accepted ⟨48,by decide⟩
]
theorem midAccepted : besselPointCheck (631505883624317727711772042809685616091/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (631505883624317727711772042809685616091/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0001.rows ScalarLogs0001.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0001.rows ScalarLogs0001.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0001.rows ScalarLogs0001.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0001.rows ScalarLogs0001.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0001.rows ScalarLogs0001.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0001.rows ScalarLogs0001.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0001.rows ScalarLogs0001.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0001.rows ScalarLogs0001.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0001.rows ScalarLogs0001.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0001.rows ScalarLogs0001.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0001.rows ScalarLogs0001.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0001.rows ScalarLogs0001.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0001.rows ScalarLogs0001.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0001.rows ScalarLogs0001.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0001.rows ScalarLogs0001.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0001.rows ScalarLogs0001.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0000.bracket0010 BracketBatch0000.bracket0011 (631505883624317727711772042809685616091/10000000000000000000000000000000000000000) (766718803502442605356075770953317/625000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0000.bracket0010 BracketBatch0000.bracket0011
  (631505883624317727711772042809685616091/10000000000000000000000000000000000000000) (766718803502442605356075770953317/625000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0010
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0011
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0001.rows BesselBatch0001.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0001.rows BesselBatch0001.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0001.rows BesselBatch0001.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0001.rows BesselBatch0001.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0001.rows BesselBatch0001.accepted ⟨50,by decide⟩
]
theorem leftAccepted : besselPointCheck (631757381442218458039661922399980937129/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (631757381442218458039661922399980937129/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0001.rows BesselBatch0001.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0001.rows BesselBatch0001.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0001.rows BesselBatch0001.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0002.rows BesselBatch0002.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0002.rows BesselBatch0002.accepted ⟨1,by decide⟩
]
theorem rightAccepted : besselPointCheck (632260381859404161029531306760497627089/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (632260381859404161029531306760497627089/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0489.rows BesselBatch0489.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0489.rows BesselBatch0489.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0489.rows BesselBatch0489.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0489.rows BesselBatch0489.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0489.rows BesselBatch0489.accepted ⟨53,by decide⟩
]
theorem midAccepted : besselPointCheck (632008881650811309534596614580239282109/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (632008881650811309534596614580239282109/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0001.rows ScalarLogs0001.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0001.rows ScalarLogs0001.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0001.rows ScalarLogs0001.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0001.rows ScalarLogs0001.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0001.rows ScalarLogs0001.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0001.rows ScalarLogs0001.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0001.rows ScalarLogs0001.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0001.rows ScalarLogs0001.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0001.rows ScalarLogs0001.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0001.rows ScalarLogs0001.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0001.rows ScalarLogs0001.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0001.rows ScalarLogs0001.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0001.rows ScalarLogs0001.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0001.rows ScalarLogs0001.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0001.rows ScalarLogs0001.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0001.rows ScalarLogs0001.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0000.bracket0011 BracketBatch0000.bracket0012 (632008881650811309534596614580239282109/10000000000000000000000000000000000000000) (3076650814724595896565140997708067/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0000.bracket0011 BracketBatch0000.bracket0012
  (632008881650811309534596614580239282109/10000000000000000000000000000000000000000) (3076650814724595896565140997708067/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0011
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0012
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0001.rows BesselBatch0001.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0001.rows BesselBatch0001.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0001.rows BesselBatch0001.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0001.rows BesselBatch0001.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0001.rows BesselBatch0001.accepted ⟨60,by decide⟩
]
theorem leftAccepted : besselPointCheck (316130190929702080514765653380248813543/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (316130190929702080514765653380248813543/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0002.rows BesselBatch0002.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0002.rows BesselBatch0002.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0002.rows BesselBatch0002.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0002.rows BesselBatch0002.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0002.rows BesselBatch0002.accepted ⟨11,by decide⟩
]
theorem rightAccepted : besselPointCheck (632763387061850093638833945271885957517/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (632763387061850093638833945271885957517/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0489.rows BesselBatch0489.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0489.rows BesselBatch0489.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0489.rows BesselBatch0489.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0489.rows BesselBatch0489.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0489.rows BesselBatch0489.accepted ⟨58,by decide⟩
]
theorem midAccepted : besselPointCheck (1265023768921254254668365252032383584603/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1265023768921254254668365252032383584603/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0001.rows ScalarLogs0001.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0001.rows ScalarLogs0001.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0001.rows ScalarLogs0001.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0001.rows ScalarLogs0001.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0001.rows ScalarLogs0001.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0001.rows ScalarLogs0001.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0001.rows ScalarLogs0001.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0001.rows ScalarLogs0001.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0001.rows ScalarLogs0001.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0001.rows ScalarLogs0001.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0001.rows ScalarLogs0001.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0001.rows ScalarLogs0001.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0001.rows ScalarLogs0001.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0001.rows ScalarLogs0001.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0001.rows ScalarLogs0001.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0001.rows ScalarLogs0001.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0000.bracket0012 BracketBatch0000.bracket0013 (1265023768921254254668365252032383584603/20000000000000000000000000000000000000000) (12345798950348802864023307831376981/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0000.bracket0012 BracketBatch0000.bracket0013
  (1265023768921254254668365252032383584603/20000000000000000000000000000000000000000) (12345798950348802864023307831376981/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0012
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0013
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0002.rows BesselBatch0002.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0002.rows BesselBatch0002.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0002.rows BesselBatch0002.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0002.rows BesselBatch0002.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0002.rows BesselBatch0002.accepted ⟨6,by decide⟩
]
theorem leftAccepted : besselPointCheck (316381693530925046819416972635942978757/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (316381693530925046819416972635942978757/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0002.rows BesselBatch0002.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0002.rows BesselBatch0002.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0002.rows BesselBatch0002.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0002.rows BesselBatch0002.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0002.rows BesselBatch0002.accepted ⟨21,by decide⟩
]
theorem rightAccepted : besselPointCheck (79158299631679055704675589005813035299/1250000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (79158299631679055704675589005813035299/1250000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0489.rows BesselBatch0489.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0489.rows BesselBatch0489.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0489.rows BesselBatch0489.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0489.rows BesselBatch0489.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0489.rows BesselBatch0489.accepted ⟨63,by decide⟩
]
theorem midAccepted : besselPointCheck (633014892057641269638119328659195119953/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (633014892057641269638119328659195119953/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0001.rows ScalarLogs0001.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0001.rows ScalarLogs0001.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0001.rows ScalarLogs0001.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0001.rows ScalarLogs0001.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0001.rows ScalarLogs0001.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0001.rows ScalarLogs0001.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0001.rows ScalarLogs0001.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0001.rows ScalarLogs0001.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0001.rows ScalarLogs0001.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0001.rows ScalarLogs0001.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0001.rows ScalarLogs0001.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0001.rows ScalarLogs0001.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0001.rows ScalarLogs0001.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0001.rows ScalarLogs0001.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0001.rows ScalarLogs0001.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0001.rows ScalarLogs0001.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0000.bracket0013 BracketBatch0000.bracket0014 (633014892057641269638119328659195119953/10000000000000000000000000000000000000000) (2477017615800650620826674861851479/2000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0000.bracket0013 BracketBatch0000.bracket0014
  (633014892057641269638119328659195119953/10000000000000000000000000000000000000000) (2477017615800650620826674861851479/2000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0013
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0014
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0002.rows BesselBatch0002.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0002.rows BesselBatch0002.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0002.rows BesselBatch0002.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0002.rows BesselBatch0002.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0002.rows BesselBatch0002.accepted ⟨16,by decide⟩
]
theorem leftAccepted : besselPointCheck (633266397053432445637404712046504282389/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (633266397053432445637404712046504282389/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0002.rows BesselBatch0002.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0002.rows BesselBatch0002.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0002.rows BesselBatch0002.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0002.rows BesselBatch0002.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0002.rows BesselBatch0002.accepted ⟨31,by decide⟩
]
theorem rightAccepted : besselPointCheck (633769411838027609448543549928335701073/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (633769411838027609448543549928335701073/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0490.rows BesselBatch0490.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0490.rows BesselBatch0490.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0490.rows BesselBatch0490.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0490.rows BesselBatch0490.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0490.rows BesselBatch0490.accepted ⟨4,by decide⟩
]
theorem midAccepted : besselPointCheck (633517904445730027542974130987419991731/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (633517904445730027542974130987419991731/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0001.rows ScalarLogs0001.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0001.rows ScalarLogs0001.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0001.rows ScalarLogs0001.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0001.rows ScalarLogs0001.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0001.rows ScalarLogs0001.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0001.rows ScalarLogs0001.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0001.rows ScalarLogs0001.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0001.rows ScalarLogs0001.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0001.rows ScalarLogs0001.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0001.rows ScalarLogs0001.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0001.rows ScalarLogs0001.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0001.rows ScalarLogs0001.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0001.rows ScalarLogs0001.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0001.rows ScalarLogs0001.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0001.rows ScalarLogs0001.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0001.rows ScalarLogs0001.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0000.bracket0014 BracketBatch0000.bracket0015 (633517904445730027542974130987419991731/10000000000000000000000000000000000000000) (3106117698398585545249348811014777/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0000.bracket0014 BracketBatch0000.bracket0015
  (633517904445730027542974130987419991731/10000000000000000000000000000000000000000) (3106117698398585545249348811014777/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0014
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0015
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0002.rows BesselBatch0002.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0002.rows BesselBatch0002.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0002.rows BesselBatch0002.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0002.rows BesselBatch0002.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0002.rows BesselBatch0002.accepted ⟨26,by decide⟩
]
theorem leftAccepted : besselPointCheck (63376941183802760944854354992833570107/1000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (63376941183802760944854354992833570107/1000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0002.rows BesselBatch0002.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0002.rows BesselBatch0002.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0002.rows BesselBatch0002.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0002.rows BesselBatch0002.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0002.rows BesselBatch0002.accepted ⟨41,by decide⟩
]
theorem rightAccepted : besselPointCheck (317136215709756090159004973083744771641/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (317136215709756090159004973083744771641/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0490.rows BesselBatch0490.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0490.rows BesselBatch0490.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0490.rows BesselBatch0490.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0490.rows BesselBatch0490.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0490.rows BesselBatch0490.accepted ⟨9,by decide⟩
]
theorem midAccepted : besselPointCheck (19813153800899059215102398376497269443/312500000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (19813153800899059215102398376497269443/312500000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0001.rows ScalarLogs0001.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0001.rows ScalarLogs0001.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0001.rows ScalarLogs0001.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0001.rows ScalarLogs0001.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0001.rows ScalarLogs0001.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0001.rows ScalarLogs0001.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0001.rows ScalarLogs0001.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0001.rows ScalarLogs0001.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0001.rows ScalarLogs0001.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0001.rows ScalarLogs0001.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0001.rows ScalarLogs0001.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0001.rows ScalarLogs0001.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0001.rows ScalarLogs0001.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0001.rows ScalarLogs0001.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0001.rows ScalarLogs0001.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0001.rows ScalarLogs0001.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0000.bracket0015 BracketBatch0001.bracket0016 (19813153800899059215102398376497269443/312500000000000000000000000000000000000) (778996702685898548794589733510279/625000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0000.bracket0015 BracketBatch0001.bracket0016
  (19813153800899059215102398376497269443/312500000000000000000000000000000000000) (778996702685898548794589733510279/625000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0015
