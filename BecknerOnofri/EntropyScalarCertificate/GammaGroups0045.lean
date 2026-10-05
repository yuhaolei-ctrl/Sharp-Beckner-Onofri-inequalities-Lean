module

public import BecknerOnofri.EntropyScalarCertificate.Bessel0056
public import BecknerOnofri.EntropyScalarCertificate.Bessel0057
public import BecknerOnofri.EntropyScalarCertificate.Bessel0517
public import BecknerOnofri.EntropyScalarCertificate.Brackets0022
public import BecknerOnofri.EntropyScalarCertificate.Brackets0023
public import BecknerOnofri.EntropyScalarCertificate.Logs0045
public import BecknerOnofri.ScalarElementaryComposition
public import BecknerOnofri.ScalarGammaEnclosure
public import BecknerOnofri.ScalarLogBesselEndpoints

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0360
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0056.rows BesselBatch0056.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0056.rows BesselBatch0056.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0056.rows BesselBatch0056.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0056.rows BesselBatch0056.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0056.rows BesselBatch0056.accepted ⟨20,by decide⟩
]
theorem leftAccepted : besselPointCheck (647878716465730532994441537828500959417/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (647878716465730532994441537828500959417/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0056.rows BesselBatch0056.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0056.rows BesselBatch0056.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0056.rows BesselBatch0056.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0056.rows BesselBatch0056.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0056.rows BesselBatch0056.accepted ⟨35,by decide⟩
]
theorem rightAccepted : besselPointCheck (1297808212035719435031004045945656529291/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1297808212035719435031004045945656529291/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0517.rows BesselBatch0517.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0517.rows BesselBatch0517.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0517.rows BesselBatch0517.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0517.rows BesselBatch0517.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0517.rows BesselBatch0517.accepted ⟨6,by decide⟩
]
theorem midAccepted : besselPointCheck (4149705031947488801631819394564253517/32000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (4149705031947488801631819394564253517/32000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0045.rows ScalarLogs0045.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0045.rows ScalarLogs0045.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0045.rows ScalarLogs0045.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0045.rows ScalarLogs0045.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0045.rows ScalarLogs0045.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0045.rows ScalarLogs0045.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0045.rows ScalarLogs0045.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0045.rows ScalarLogs0045.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0045.rows ScalarLogs0045.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0045.rows ScalarLogs0045.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0045.rows ScalarLogs0045.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0045.rows ScalarLogs0045.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0045.rows ScalarLogs0045.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0045.rows ScalarLogs0045.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0045.rows ScalarLogs0045.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0045.rows ScalarLogs0045.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0022.bracket0360 BracketBatch0022.bracket0361 (4149705031947488801631819394564253517/32000000000000000000000000000000000000) (213414816800517152413132395682347383/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0022.bracket0360 BracketBatch0022.bracket0361
  (4149705031947488801631819394564253517/32000000000000000000000000000000000000) (213414816800517152413132395682347383/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0360
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0361
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0056.rows BesselBatch0056.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0056.rows BesselBatch0056.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0056.rows BesselBatch0056.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0056.rows BesselBatch0056.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0056.rows BesselBatch0056.accepted ⟨30,by decide⟩
]
theorem leftAccepted : besselPointCheck (162226026504464929378875505743207066161/1250000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (162226026504464929378875505743207066161/1250000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0056.rows BesselBatch0056.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0056.rows BesselBatch0056.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0056.rows BesselBatch0056.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0056.rows BesselBatch0056.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0056.rows BesselBatch0056.accepted ⟨45,by decide⟩
]
theorem rightAccepted : besselPointCheck (64992957646374445107507236052766972223/500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (64992957646374445107507236052766972223/500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0517.rows BesselBatch0517.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0517.rows BesselBatch0517.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0517.rows BesselBatch0517.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0517.rows BesselBatch0517.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0517.rows BesselBatch0517.accepted ⟨11,by decide⟩
]
theorem midAccepted : besselPointCheck (649416841240802084295287191750248993437/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (649416841240802084295287191750248993437/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0045.rows ScalarLogs0045.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0045.rows ScalarLogs0045.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0045.rows ScalarLogs0045.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0045.rows ScalarLogs0045.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0045.rows ScalarLogs0045.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0045.rows ScalarLogs0045.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0045.rows ScalarLogs0045.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0045.rows ScalarLogs0045.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0045.rows ScalarLogs0045.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0045.rows ScalarLogs0045.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0045.rows ScalarLogs0045.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0045.rows ScalarLogs0045.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0045.rows ScalarLogs0045.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0045.rows ScalarLogs0045.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0045.rows ScalarLogs0045.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0045.rows ScalarLogs0045.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0022.bracket0361 BracketBatch0022.bracket0362 (649416841240802084295287191750248993437/5000000000000000000000000000000000000000) (214753641689224476973468347038012699/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0022.bracket0361 BracketBatch0022.bracket0362
  (649416841240802084295287191750248993437/5000000000000000000000000000000000000000) (214753641689224476973468347038012699/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0361
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0362
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0056.rows BesselBatch0056.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0056.rows BesselBatch0056.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0056.rows BesselBatch0056.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0056.rows BesselBatch0056.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0056.rows BesselBatch0056.accepted ⟨40,by decide⟩
]
theorem leftAccepted : besselPointCheck (1299859152927488902150144721055339444457/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1299859152927488902150144721055339444457/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0056.rows BesselBatch0056.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0056.rows BesselBatch0056.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0056.rows BesselBatch0056.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0056.rows BesselBatch0056.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0056.rows BesselBatch0056.accepted ⟨55,by decide⟩
]
theorem rightAccepted : besselPointCheck (1301910255881854172488648121364797607637/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1301910255881854172488648121364797607637/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0517.rows BesselBatch0517.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0517.rows BesselBatch0517.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0517.rows BesselBatch0517.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0517.rows BesselBatch0517.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0517.rows BesselBatch0517.accepted ⟨16,by decide⟩
]
theorem midAccepted : besselPointCheck (1300884704404671537319396421210068526047/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1300884704404671537319396421210068526047/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0045.rows ScalarLogs0045.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0045.rows ScalarLogs0045.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0045.rows ScalarLogs0045.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0045.rows ScalarLogs0045.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0045.rows ScalarLogs0045.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0045.rows ScalarLogs0045.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0045.rows ScalarLogs0045.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0045.rows ScalarLogs0045.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0045.rows ScalarLogs0045.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0045.rows ScalarLogs0045.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0045.rows ScalarLogs0045.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0045.rows ScalarLogs0045.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0045.rows ScalarLogs0045.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0045.rows ScalarLogs0045.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0045.rows ScalarLogs0045.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0045.rows ScalarLogs0045.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0022.bracket0362 BracketBatch0022.bracket0363 (1300884704404671537319396421210068526047/10000000000000000000000000000000000000000) (108049382645122916279809043827410719/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0022.bracket0362 BracketBatch0022.bracket0363
  (1300884704404671537319396421210068526047/10000000000000000000000000000000000000000) (108049382645122916279809043827410719/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0362
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0363
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0056.rows BesselBatch0056.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0056.rows BesselBatch0056.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0056.rows BesselBatch0056.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0056.rows BesselBatch0056.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0056.rows BesselBatch0056.accepted ⟨50,by decide⟩
]
theorem leftAccepted : besselPointCheck (650955127940927086244324060682398803817/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (650955127940927086244324060682398803817/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0056.rows BesselBatch0056.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0056.rows BesselBatch0056.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0056.rows BesselBatch0056.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0057.rows BesselBatch0057.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0057.rows BesselBatch0057.accepted ⟨1,by decide⟩
]
theorem rightAccepted : besselPointCheck (651980760587007590427647536600415179591/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (651980760587007590427647536600415179591/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0517.rows BesselBatch0517.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0517.rows BesselBatch0517.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0517.rows BesselBatch0517.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0517.rows BesselBatch0517.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0517.rows BesselBatch0517.accepted ⟨21,by decide⟩
]
theorem midAccepted : besselPointCheck (81433493032995917291998224830175873963/625000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (81433493032995917291998224830175873963/625000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0045.rows ScalarLogs0045.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0045.rows ScalarLogs0045.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0045.rows ScalarLogs0045.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0045.rows ScalarLogs0045.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0045.rows ScalarLogs0045.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0045.rows ScalarLogs0045.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0045.rows ScalarLogs0045.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0045.rows ScalarLogs0045.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0045.rows ScalarLogs0045.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0045.rows ScalarLogs0045.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0045.rows ScalarLogs0045.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0045.rows ScalarLogs0045.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0045.rows ScalarLogs0045.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0045.rows ScalarLogs0045.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0045.rows ScalarLogs0045.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0045.rows ScalarLogs0045.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0022.bracket0363 BracketBatch0022.bracket0364 (81433493032995917291998224830175873963/625000000000000000000000000000000000000) (217450207527853870060729866578210269/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0022.bracket0363 BracketBatch0022.bracket0364
  (81433493032995917291998224830175873963/625000000000000000000000000000000000000) (217450207527853870060729866578210269/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0363
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0364
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0056.rows BesselBatch0056.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0056.rows BesselBatch0056.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0056.rows BesselBatch0056.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0056.rows BesselBatch0056.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0056.rows BesselBatch0056.accepted ⟨60,by decide⟩
]
theorem leftAccepted : besselPointCheck (1303961521174015180855295073200830359179/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1303961521174015180855295073200830359179/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0057.rows BesselBatch0057.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0057.rows BesselBatch0057.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0057.rows BesselBatch0057.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0057.rows BesselBatch0057.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0057.rows BesselBatch0057.accepted ⟨11,by decide⟩
]
theorem rightAccepted : besselPointCheck (1306012949079287310517388535071300053731/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1306012949079287310517388535071300053731/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0517.rows BesselBatch0517.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0517.rows BesselBatch0517.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0517.rows BesselBatch0517.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0517.rows BesselBatch0517.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0517.rows BesselBatch0517.accepted ⟨26,by decide⟩
]
theorem midAccepted : besselPointCheck (260997447025330249137268360827213041291/2000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (260997447025330249137268360827213041291/2000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0045.rows ScalarLogs0045.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0045.rows ScalarLogs0045.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0045.rows ScalarLogs0045.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0045.rows ScalarLogs0045.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0045.rows ScalarLogs0045.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0045.rows ScalarLogs0045.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0045.rows ScalarLogs0045.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0045.rows ScalarLogs0045.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0045.rows ScalarLogs0045.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0045.rows ScalarLogs0045.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0045.rows ScalarLogs0045.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0045.rows ScalarLogs0045.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0045.rows ScalarLogs0045.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0045.rows ScalarLogs0045.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0045.rows ScalarLogs0045.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0045.rows ScalarLogs0045.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0022.bracket0364 BracketBatch0022.bracket0365 (260997447025330249137268360827213041291/2000000000000000000000000000000000000000) (218807988359361254405485355323389369/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0022.bracket0364 BracketBatch0022.bracket0365
  (260997447025330249137268360827213041291/2000000000000000000000000000000000000000) (218807988359361254405485355323389369/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0364
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0365
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0057.rows BesselBatch0057.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0057.rows BesselBatch0057.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0057.rows BesselBatch0057.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0057.rows BesselBatch0057.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0057.rows BesselBatch0057.accepted ⟨6,by decide⟩
]
theorem leftAccepted : besselPointCheck (40812904658727728453668391720978126679/312500000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (40812904658727728453668391720978126679/312500000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0057.rows BesselBatch0057.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0057.rows BesselBatch0057.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0057.rows BesselBatch0057.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0057.rows BesselBatch0057.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0057.rows BesselBatch0057.accepted ⟨21,by decide⟩
]
theorem rightAccepted : besselPointCheck (130806453987310161219409529216356195319/1000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (130806453987310161219409529216356195319/1000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0517.rows BesselBatch0517.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0517.rows BesselBatch0517.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0517.rows BesselBatch0517.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0517.rows BesselBatch0517.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0517.rows BesselBatch0517.accepted ⟨31,by decide⟩
]
theorem midAccepted : besselPointCheck (1307038744476194461355741913617431003459/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1307038744476194461355741913617431003459/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0045.rows ScalarLogs0045.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0045.rows ScalarLogs0045.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0045.rows ScalarLogs0045.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0045.rows ScalarLogs0045.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0045.rows ScalarLogs0045.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0045.rows ScalarLogs0045.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0045.rows ScalarLogs0045.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0045.rows ScalarLogs0045.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0045.rows ScalarLogs0045.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0045.rows ScalarLogs0045.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0045.rows ScalarLogs0045.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0045.rows ScalarLogs0045.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0045.rows ScalarLogs0045.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0045.rows ScalarLogs0045.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0045.rows ScalarLogs0045.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0045.rows ScalarLogs0045.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0022.bracket0365 BracketBatch0022.bracket0366 (1307038744476194461355741913617431003459/10000000000000000000000000000000000000000) (27521515971891350542881995384304083/1250000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0022.bracket0365 BracketBatch0022.bracket0366
  (1307038744476194461355741913617431003459/10000000000000000000000000000000000000000) (27521515971891350542881995384304083/1250000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0365
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0366
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0057.rows BesselBatch0057.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0057.rows BesselBatch0057.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0057.rows BesselBatch0057.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0057.rows BesselBatch0057.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0057.rows BesselBatch0057.accepted ⟨16,by decide⟩
]
theorem leftAccepted : besselPointCheck (1308064539873101612194095292163561953187/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1308064539873101612194095292163561953187/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0057.rows BesselBatch0057.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0057.rows BesselBatch0057.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0057.rows BesselBatch0057.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0057.rows BesselBatch0057.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0057.rows BesselBatch0057.accepted ⟨31,by decide⟩
]
theorem rightAccepted : besselPointCheck (1310116293831005023251481021060078343861/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1310116293831005023251481021060078343861/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0517.rows BesselBatch0517.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0517.rows BesselBatch0517.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0517.rows BesselBatch0517.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0517.rows BesselBatch0517.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0517.rows BesselBatch0517.accepted ⟨36,by decide⟩
]
theorem midAccepted : besselPointCheck (327272604213013329430697039152955037131/2500000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (327272604213013329430697039152955037131/2500000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0045.rows ScalarLogs0045.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0045.rows ScalarLogs0045.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0045.rows ScalarLogs0045.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0045.rows ScalarLogs0045.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0045.rows ScalarLogs0045.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0045.rows ScalarLogs0045.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0045.rows ScalarLogs0045.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0045.rows ScalarLogs0045.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0045.rows ScalarLogs0045.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0045.rows ScalarLogs0045.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0045.rows ScalarLogs0045.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0045.rows ScalarLogs0045.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0045.rows ScalarLogs0045.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0045.rows ScalarLogs0045.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0045.rows ScalarLogs0045.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0045.rows ScalarLogs0045.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0022.bracket0366 BracketBatch0022.bracket0367 (327272604213013329430697039152955037131/2500000000000000000000000000000000000000) (221542645798585650837347042940597333/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0022.bracket0366 BracketBatch0022.bracket0367
  (327272604213013329430697039152955037131/2500000000000000000000000000000000000000) (221542645798585650837347042940597333/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0366
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0367
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0057.rows BesselBatch0057.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0057.rows BesselBatch0057.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0057.rows BesselBatch0057.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0057.rows BesselBatch0057.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0057.rows BesselBatch0057.accepted ⟨26,by decide⟩
]
theorem leftAccepted : besselPointCheck (655058146915502511625740510530039171929/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (655058146915502511625740510530039171929/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0057.rows BesselBatch0057.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0057.rows BesselBatch0057.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0057.rows BesselBatch0057.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0057.rows BesselBatch0057.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0057.rows BesselBatch0057.accepted ⟨41,by decide⟩
]
theorem rightAccepted : besselPointCheck (164021026403582573387459422124340080869/1250000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (164021026403582573387459422124340080869/1250000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0517.rows BesselBatch0517.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0517.rows BesselBatch0517.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0517.rows BesselBatch0517.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0517.rows BesselBatch0517.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0517.rows BesselBatch0517.accepted ⟨41,by decide⟩
]
theorem midAccepted : besselPointCheck (262228450505966561035115639805479899081/2000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (262228450505966561035115639805479899081/2000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0045.rows ScalarLogs0045.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0045.rows ScalarLogs0045.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0045.rows ScalarLogs0045.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0045.rows ScalarLogs0045.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0045.rows ScalarLogs0045.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0045.rows ScalarLogs0045.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0045.rows ScalarLogs0045.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0045.rows ScalarLogs0045.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0045.rows ScalarLogs0045.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0045.rows ScalarLogs0045.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0045.rows ScalarLogs0045.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0045.rows ScalarLogs0045.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0045.rows ScalarLogs0045.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0045.rows ScalarLogs0045.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0045.rows ScalarLogs0045.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0045.rows ScalarLogs0045.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0022.bracket0367 BracketBatch0023.bracket0368 (262228450505966561035115639805479899081/2000000000000000000000000000000000000000) (111459781243109707044539890573131917/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0022.bracket0367 BracketBatch0023.bracket0368
  (262228450505966561035115639805479899081/2000000000000000000000000000000000000000) (111459781243109707044539890573131917/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0367
