module

public import BecknerOnofri.EntropyScalarCertificate.Bessel0321
public import BecknerOnofri.EntropyScalarCertificate.Bessel0322
public import BecknerOnofri.EntropyScalarCertificate.Bessel0649
public import BecknerOnofri.EntropyScalarCertificate.Bessel0650
public import BecknerOnofri.EntropyScalarCertificate.Brackets0128
public import BecknerOnofri.EntropyScalarCertificate.Brackets0129
public import BecknerOnofri.EntropyScalarCertificate.Logs0257
public import BecknerOnofri.ScalarElementaryComposition
public import BecknerOnofri.ScalarGammaEnclosure
public import BecknerOnofri.ScalarLogBesselEndpoints

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2056
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0321.rows BesselBatch0321.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0321.rows BesselBatch0321.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0321.rows BesselBatch0321.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0321.rows BesselBatch0321.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0321.rows BesselBatch0321.accepted ⟨20,by decide⟩
]
theorem leftAccepted : besselPointCheck (7572607187472532559794613690175493373719/1250000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (7572607187472532559794613690175493373719/1250000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0321.rows BesselBatch0321.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0321.rows BesselBatch0321.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0321.rows BesselBatch0321.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0321.rows BesselBatch0321.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0321.rows BesselBatch0321.accepted ⟨35,by decide⟩
]
theorem rightAccepted : besselPointCheck (30360666978294746844424386097356102439351/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (30360666978294746844424386097356102439351/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0649.rows BesselBatch0649.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0649.rows BesselBatch0649.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0649.rows BesselBatch0649.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0649.rows BesselBatch0649.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0649.rows BesselBatch0649.accepted ⟨38,by decide⟩
]
theorem midAccepted : besselPointCheck (60651095728184877083602840858058075934227/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (60651095728184877083602840858058075934227/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0257.rows ScalarLogs0257.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0257.rows ScalarLogs0257.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0257.rows ScalarLogs0257.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0257.rows ScalarLogs0257.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0257.rows ScalarLogs0257.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0257.rows ScalarLogs0257.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0257.rows ScalarLogs0257.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0257.rows ScalarLogs0257.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0257.rows ScalarLogs0257.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0257.rows ScalarLogs0257.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0257.rows ScalarLogs0257.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0257.rows ScalarLogs0257.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0257.rows ScalarLogs0257.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0257.rows ScalarLogs0257.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0257.rows ScalarLogs0257.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0257.rows ScalarLogs0257.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0128.bracket2056 BracketBatch0128.bracket2057 (60651095728184877083602840858058075934227/10000000000000000000000000000000000000000) (2112346341046518497660574485974306143297/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0128.bracket2056 BracketBatch0128.bracket2057
  (60651095728184877083602840858058075934227/10000000000000000000000000000000000000000) (2112346341046518497660574485974306143297/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2056
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2057
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0321.rows BesselBatch0321.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0321.rows BesselBatch0321.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0321.rows BesselBatch0321.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0321.rows BesselBatch0321.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0321.rows BesselBatch0321.accepted ⟨30,by decide⟩
]
theorem leftAccepted : besselPointCheck (60721333956589493688848772194712204878699/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (60721333956589493688848772194712204878699/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0321.rows BesselBatch0321.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0321.rows BesselBatch0321.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0321.rows BesselBatch0321.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0321.rows BesselBatch0321.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0321.rows BesselBatch0321.accepted ⟨45,by decide⟩
]
theorem rightAccepted : besselPointCheck (60862480663773103867744944380246101506707/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (60862480663773103867744944380246101506707/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0649.rows BesselBatch0649.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0649.rows BesselBatch0649.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0649.rows BesselBatch0649.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0649.rows BesselBatch0649.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0649.rows BesselBatch0649.accepted ⟨43,by decide⟩
]
theorem midAccepted : besselPointCheck (60791907310181298778296858287479153192703/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (60791907310181298778296858287479153192703/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0257.rows ScalarLogs0257.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0257.rows ScalarLogs0257.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0257.rows ScalarLogs0257.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0257.rows ScalarLogs0257.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0257.rows ScalarLogs0257.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0257.rows ScalarLogs0257.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0257.rows ScalarLogs0257.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0257.rows ScalarLogs0257.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0257.rows ScalarLogs0257.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0257.rows ScalarLogs0257.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0257.rows ScalarLogs0257.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0257.rows ScalarLogs0257.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0257.rows ScalarLogs0257.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0257.rows ScalarLogs0257.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0257.rows ScalarLogs0257.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0257.rows ScalarLogs0257.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0128.bracket2057 BracketBatch0128.bracket2058 (60791907310181298778296858287479153192703/10000000000000000000000000000000000000000) (2115299735832866508593649110955809111819/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0128.bracket2057 BracketBatch0128.bracket2058
  (60791907310181298778296858287479153192703/10000000000000000000000000000000000000000) (2115299735832866508593649110955809111819/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2057
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2058
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0321.rows BesselBatch0321.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0321.rows BesselBatch0321.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0321.rows BesselBatch0321.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0321.rows BesselBatch0321.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0321.rows BesselBatch0321.accepted ⟨40,by decide⟩
]
theorem leftAccepted : besselPointCheck (3803905041485818991734059023765381344169/625000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (3803905041485818991734059023765381344169/625000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0321.rows BesselBatch0321.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0321.rows BesselBatch0321.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0321.rows BesselBatch0321.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0321.rows BesselBatch0321.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0321.rows BesselBatch0321.accepted ⟨55,by decide⟩
]
theorem rightAccepted : besselPointCheck (2440172096747716140908999850396019568447/400000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (2440172096747716140908999850396019568447/400000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0649.rows BesselBatch0649.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0649.rows BesselBatch0649.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0649.rows BesselBatch0649.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0649.rows BesselBatch0649.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0649.rows BesselBatch0649.accepted ⟨48,by decide⟩
]
theorem midAccepted : besselPointCheck (121866783082466007390469940640146590717879/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (121866783082466007390469940640146590717879/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0257.rows ScalarLogs0257.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0257.rows ScalarLogs0257.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0257.rows ScalarLogs0257.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0257.rows ScalarLogs0257.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0257.rows ScalarLogs0257.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0257.rows ScalarLogs0257.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0257.rows ScalarLogs0257.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0257.rows ScalarLogs0257.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0257.rows ScalarLogs0257.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0257.rows ScalarLogs0257.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0257.rows ScalarLogs0257.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0257.rows ScalarLogs0257.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0257.rows ScalarLogs0257.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0257.rows ScalarLogs0257.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0257.rows ScalarLogs0257.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0257.rows ScalarLogs0257.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0128.bracket2058 BracketBatch0128.bracket2059 (121866783082466007390469940640146590717879/20000000000000000000000000000000000000000) (2118260927500963808551497746608095861769/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0128.bracket2058 BracketBatch0128.bracket2059
  (121866783082466007390469940640146590717879/20000000000000000000000000000000000000000) (2118260927500963808551497746608095861769/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2058
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2059
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0321.rows BesselBatch0321.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0321.rows BesselBatch0321.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0321.rows BesselBatch0321.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0321.rows BesselBatch0321.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0321.rows BesselBatch0321.accepted ⟨50,by decide⟩
]
theorem leftAccepted : besselPointCheck (15251075604673225880681249064975122302793/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (15251075604673225880681249064975122302793/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0321.rows BesselBatch0321.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0321.rows BesselBatch0321.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0321.rows BesselBatch0321.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0322.rows BesselBatch0322.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0322.rows BesselBatch0322.accepted ⟨1,by decide⟩
]
theorem rightAccepted : besselPointCheck (30573402032311657711592120015424918998959/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (30573402032311657711592120015424918998959/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0649.rows BesselBatch0649.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0649.rows BesselBatch0649.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0649.rows BesselBatch0649.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0649.rows BesselBatch0649.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0649.rows BesselBatch0649.accepted ⟨53,by decide⟩
]
theorem midAccepted : besselPointCheck (12215110648331621894590923629075032720909/2000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (12215110648331621894590923629075032720909/2000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0257.rows ScalarLogs0257.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0257.rows ScalarLogs0257.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0257.rows ScalarLogs0257.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0257.rows ScalarLogs0257.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0257.rows ScalarLogs0257.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0257.rows ScalarLogs0257.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0257.rows ScalarLogs0257.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0257.rows ScalarLogs0257.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0257.rows ScalarLogs0257.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0257.rows ScalarLogs0257.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0257.rows ScalarLogs0257.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0257.rows ScalarLogs0257.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0257.rows ScalarLogs0257.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0257.rows ScalarLogs0257.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0257.rows ScalarLogs0257.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0257.rows ScalarLogs0257.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0128.bracket2059 BracketBatch0128.bracket2060 (12215110648331621894590923629075032720909/2000000000000000000000000000000000000000) (1060614976997168213543743258949962796743/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0128.bracket2059 BracketBatch0128.bracket2060
  (12215110648331621894590923629075032720909/2000000000000000000000000000000000000000) (1060614976997168213543743258949962796743/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2059
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2060
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0321.rows BesselBatch0321.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0321.rows BesselBatch0321.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0321.rows BesselBatch0321.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0321.rows BesselBatch0321.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0321.rows BesselBatch0321.accepted ⟨60,by decide⟩
]
theorem leftAccepted : besselPointCheck (12229360812924663084636848006169967599583/2000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (12229360812924663084636848006169967599583/2000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0322.rows BesselBatch0322.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0322.rows BesselBatch0322.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0322.rows BesselBatch0322.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0322.rows BesselBatch0322.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0322.rows BesselBatch0322.accepted ⟨11,by decide⟩
]
theorem rightAccepted : besselPointCheck (3830624405706365821118060207279840715509/625000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (3830624405706365821118060207279840715509/625000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0649.rows BesselBatch0649.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0649.rows BesselBatch0649.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0649.rows BesselBatch0649.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0649.rows BesselBatch0649.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0649.rows BesselBatch0649.accepted ⟨58,by decide⟩
]
theorem midAccepted : besselPointCheck (122436794555925168561073203347327289446059/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (122436794555925168561073203347327289446059/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0257.rows ScalarLogs0257.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0257.rows ScalarLogs0257.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0257.rows ScalarLogs0257.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0257.rows ScalarLogs0257.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0257.rows ScalarLogs0257.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0257.rows ScalarLogs0257.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0257.rows ScalarLogs0257.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0257.rows ScalarLogs0257.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0257.rows ScalarLogs0257.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0257.rows ScalarLogs0257.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0257.rows ScalarLogs0257.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0257.rows ScalarLogs0257.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0257.rows ScalarLogs0257.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0257.rows ScalarLogs0257.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0257.rows ScalarLogs0257.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0257.rows ScalarLogs0257.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0128.bracket2060 BracketBatch0128.bracket2061 (122436794555925168561073203347327289446059/20000000000000000000000000000000000000000) (66381464173004356666468374267217574873/312500000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0128.bracket2060 BracketBatch0128.bracket2061
  (122436794555925168561073203347327289446059/20000000000000000000000000000000000000000) (66381464173004356666468374267217574873/312500000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2060
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2061
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0322.rows BesselBatch0322.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0322.rows BesselBatch0322.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0322.rows BesselBatch0322.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0322.rows BesselBatch0322.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0322.rows BesselBatch0322.accepted ⟨6,by decide⟩
]
theorem leftAccepted : besselPointCheck (61289990491301853137888963316477451448141/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (61289990491301853137888963316477451448141/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0322.rows BesselBatch0322.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0322.rows BesselBatch0322.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0322.rows BesselBatch0322.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0322.rows BesselBatch0322.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0322.rows BesselBatch0322.accepted ⟨21,by decide⟩
]
theorem rightAccepted : besselPointCheck (61433866635487541405508764477285034108523/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (61433866635487541405508764477285034108523/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0649.rows BesselBatch0649.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0649.rows BesselBatch0649.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0649.rows BesselBatch0649.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0649.rows BesselBatch0649.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0649.rows BesselBatch0649.accepted ⟨63,by decide⟩
]
theorem midAccepted : besselPointCheck (15340482140848674317924715974220310694583/2500000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (15340482140848674317924715974220310694583/2500000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0257.rows ScalarLogs0257.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0257.rows ScalarLogs0257.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0257.rows ScalarLogs0257.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0257.rows ScalarLogs0257.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0257.rows ScalarLogs0257.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0257.rows ScalarLogs0257.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0257.rows ScalarLogs0257.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0257.rows ScalarLogs0257.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0257.rows ScalarLogs0257.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0257.rows ScalarLogs0257.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0257.rows ScalarLogs0257.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0257.rows ScalarLogs0257.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0257.rows ScalarLogs0257.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0257.rows ScalarLogs0257.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0257.rows ScalarLogs0257.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0257.rows ScalarLogs0257.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0128.bracket2061 BracketBatch0128.bracket2062 (15340482140848674317924715974220310694583/2500000000000000000000000000000000000000) (1063595832315926971587627458246935897777/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0128.bracket2061 BracketBatch0128.bracket2062
  (15340482140848674317924715974220310694583/2500000000000000000000000000000000000000) (1063595832315926971587627458246935897777/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2061
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2062
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0322.rows BesselBatch0322.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0322.rows BesselBatch0322.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0322.rows BesselBatch0322.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0322.rows BesselBatch0322.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0322.rows BesselBatch0322.accepted ⟨16,by decide⟩
]
theorem leftAccepted : besselPointCheck (1535846665887188535137719111932125852713/250000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1535846665887188535137719111932125852713/250000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0322.rows BesselBatch0322.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0322.rows BesselBatch0322.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0322.rows BesselBatch0322.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0322.rows BesselBatch0322.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0322.rows BesselBatch0322.accepted ⟨31,by decide⟩
]
theorem rightAccepted : besselPointCheck (30789218740763705132015233982158131131453/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (30789218740763705132015233982158131131453/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0650.rows BesselBatch0650.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0650.rows BesselBatch0650.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0650.rows BesselBatch0650.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0650.rows BesselBatch0650.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0650.rows BesselBatch0650.accepted ⟨4,by decide⟩
]
theorem midAccepted : besselPointCheck (61506152058507475834769616220800648185713/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (61506152058507475834769616220800648185713/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0257.rows ScalarLogs0257.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0257.rows ScalarLogs0257.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0257.rows ScalarLogs0257.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0257.rows ScalarLogs0257.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0257.rows ScalarLogs0257.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0257.rows ScalarLogs0257.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0257.rows ScalarLogs0257.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0257.rows ScalarLogs0257.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0257.rows ScalarLogs0257.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0257.rows ScalarLogs0257.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0257.rows ScalarLogs0257.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0257.rows ScalarLogs0257.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0257.rows ScalarLogs0257.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0257.rows ScalarLogs0257.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0257.rows ScalarLogs0257.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0257.rows ScalarLogs0257.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0128.bracket2062 BracketBatch0128.bracket2063 (61506152058507475834769616220800648185713/10000000000000000000000000000000000000000) (133136526629501031518493830472606732903/625000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0128.bracket2062 BracketBatch0128.bracket2063
  (61506152058507475834769616220800648185713/10000000000000000000000000000000000000000) (133136526629501031518493830472606732903/625000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2062
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2063
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0322.rows BesselBatch0322.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0322.rows BesselBatch0322.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0322.rows BesselBatch0322.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0322.rows BesselBatch0322.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0322.rows BesselBatch0322.accepted ⟨26,by decide⟩
]
theorem leftAccepted : besselPointCheck (61578437481527410264030467964316262262903/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (61578437481527410264030467964316262262903/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0322.rows BesselBatch0322.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0322.rows BesselBatch0322.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0322.rows BesselBatch0322.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0322.rows BesselBatch0322.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0322.rows BesselBatch0322.accepted ⟨41,by decide⟩
]
theorem rightAccepted : besselPointCheck (30861854030965599726457174598832666019823/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (30861854030965599726457174598832666019823/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0650.rows BesselBatch0650.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0650.rows BesselBatch0650.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0650.rows BesselBatch0650.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0650.rows BesselBatch0650.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0650.rows BesselBatch0650.accepted ⟨9,by decide⟩
]
theorem midAccepted : besselPointCheck (123302145543458609716944817161981594302549/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (123302145543458609716944817161981594302549/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0257.rows ScalarLogs0257.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0257.rows ScalarLogs0257.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0257.rows ScalarLogs0257.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0257.rows ScalarLogs0257.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0257.rows ScalarLogs0257.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0257.rows ScalarLogs0257.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0257.rows ScalarLogs0257.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0257.rows ScalarLogs0257.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0257.rows ScalarLogs0257.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0257.rows ScalarLogs0257.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0257.rows ScalarLogs0257.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0257.rows ScalarLogs0257.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0257.rows ScalarLogs0257.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0257.rows ScalarLogs0257.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0257.rows ScalarLogs0257.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0257.rows ScalarLogs0257.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0128.bracket2063 BracketBatch0129.bracket2064 (123302145543458609716944817161981594302549/20000000000000000000000000000000000000000) (2133185176934980612430734401723989054093/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0128.bracket2063 BracketBatch0129.bracket2064
  (123302145543458609716944817161981594302549/20000000000000000000000000000000000000000) (2133185176934980612430734401723989054093/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2063
