module

public import BecknerOnofri.EntropyScalarCertificate.Bessel0071
public import BecknerOnofri.EntropyScalarCertificate.Bessel0072
public import BecknerOnofri.EntropyScalarCertificate.Bessel0524
public import BecknerOnofri.EntropyScalarCertificate.Bessel0525
public import BecknerOnofri.EntropyScalarCertificate.Brackets0028
public import BecknerOnofri.EntropyScalarCertificate.Brackets0029
public import BecknerOnofri.EntropyScalarCertificate.Logs0057
public import BecknerOnofri.ScalarElementaryComposition
public import BecknerOnofri.ScalarGammaEnclosure
public import BecknerOnofri.ScalarLogBesselEndpoints

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0456
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0071.rows BesselBatch0071.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0071.rows BesselBatch0071.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0071.rows BesselBatch0071.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0071.rows BesselBatch0071.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0071.rows BesselBatch0071.accepted ⟨20,by decide⟩
]
theorem leftAccepted : besselPointCheck (373352419611801754915855024412258641063/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (373352419611801754915855024412258641063/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0071.rows BesselBatch0071.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0071.rows BesselBatch0071.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0071.rows BesselBatch0071.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0071.rows BesselBatch0071.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0071.rows BesselBatch0071.accepted ⟨35,by decide⟩
]
theorem rightAccepted : besselPointCheck (1495477260742333380524094253794170400657/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1495477260742333380524094253794170400657/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0524.rows BesselBatch0524.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0524.rows BesselBatch0524.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0524.rows BesselBatch0524.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0524.rows BesselBatch0524.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0524.rows BesselBatch0524.accepted ⟨38,by decide⟩
]
theorem midAccepted : besselPointCheck (2988886939189540400187514351443204964909/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (2988886939189540400187514351443204964909/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0057.rows ScalarLogs0057.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0057.rows ScalarLogs0057.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0057.rows ScalarLogs0057.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0057.rows ScalarLogs0057.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0057.rows ScalarLogs0057.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0057.rows ScalarLogs0057.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0057.rows ScalarLogs0057.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0057.rows ScalarLogs0057.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0057.rows ScalarLogs0057.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0057.rows ScalarLogs0057.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0057.rows ScalarLogs0057.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0057.rows ScalarLogs0057.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0057.rows ScalarLogs0057.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0057.rows ScalarLogs0057.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0057.rows ScalarLogs0057.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0057.rows ScalarLogs0057.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0028.bracket0456 BracketBatch0028.bracket0457 (2988886939189540400187514351443204964909/20000000000000000000000000000000000000000) (93405327291878430877042109549917543/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0028.bracket0456 BracketBatch0028.bracket0457
  (2988886939189540400187514351443204964909/20000000000000000000000000000000000000000) (93405327291878430877042109549917543/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0456
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0457
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0071.rows BesselBatch0071.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0071.rows BesselBatch0071.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0071.rows BesselBatch0071.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0071.rows BesselBatch0071.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0071.rows BesselBatch0071.accepted ⟨30,by decide⟩
]
theorem leftAccepted : besselPointCheck (747738630371166690262047126897085200327/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (747738630371166690262047126897085200327/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0071.rows BesselBatch0071.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0071.rows BesselBatch0071.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0071.rows BesselBatch0071.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0071.rows BesselBatch0071.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0071.rows BesselBatch0071.accepted ⟨45,by decide⟩
]
theorem rightAccepted : besselPointCheck (1497545031790506666918273436683272277103/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1497545031790506666918273436683272277103/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0524.rows BesselBatch0524.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0524.rows BesselBatch0524.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0524.rows BesselBatch0524.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0524.rows BesselBatch0524.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0524.rows BesselBatch0524.accepted ⟨43,by decide⟩
]
theorem midAccepted : besselPointCheck (2993022292532840047442367690477442677757/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (2993022292532840047442367690477442677757/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0057.rows ScalarLogs0057.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0057.rows ScalarLogs0057.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0057.rows ScalarLogs0057.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0057.rows ScalarLogs0057.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0057.rows ScalarLogs0057.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0057.rows ScalarLogs0057.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0057.rows ScalarLogs0057.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0057.rows ScalarLogs0057.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0057.rows ScalarLogs0057.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0057.rows ScalarLogs0057.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0057.rows ScalarLogs0057.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0057.rows ScalarLogs0057.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0057.rows ScalarLogs0057.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0057.rows ScalarLogs0057.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0057.rows ScalarLogs0057.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0057.rows ScalarLogs0057.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0028.bracket0457 BracketBatch0028.bracket0458 (2993022292532840047442367690477442677757/20000000000000000000000000000000000000000) (23478776294650016573999362857168747/625000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0028.bracket0457 BracketBatch0028.bracket0458
  (2993022292532840047442367690477442677757/20000000000000000000000000000000000000000) (23478776294650016573999362857168747/625000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0457
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0458
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0071.rows BesselBatch0071.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0071.rows BesselBatch0071.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0071.rows BesselBatch0071.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0071.rows BesselBatch0071.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0071.rows BesselBatch0071.accepted ⟨40,by decide⟩
]
theorem leftAccepted : besselPointCheck (14975450317905066669182734366832722771/100000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (14975450317905066669182734366832722771/100000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0071.rows BesselBatch0071.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0071.rows BesselBatch0071.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0071.rows BesselBatch0071.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0071.rows BesselBatch0071.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0071.rows BesselBatch0071.accepted ⟨55,by decide⟩
]
theorem rightAccepted : besselPointCheck (749806495939450784600413008533399867919/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (749806495939450784600413008533399867919/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0524.rows BesselBatch0524.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0524.rows BesselBatch0524.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0524.rows BesselBatch0524.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0524.rows BesselBatch0524.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0524.rows BesselBatch0524.accepted ⟨48,by decide⟩
]
theorem midAccepted : besselPointCheck (1498579011834704118059549726875036006469/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1498579011834704118059549726875036006469/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0057.rows ScalarLogs0057.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0057.rows ScalarLogs0057.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0057.rows ScalarLogs0057.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0057.rows ScalarLogs0057.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0057.rows ScalarLogs0057.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0057.rows ScalarLogs0057.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0057.rows ScalarLogs0057.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0057.rows ScalarLogs0057.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0057.rows ScalarLogs0057.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0057.rows ScalarLogs0057.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0057.rows ScalarLogs0057.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0057.rows ScalarLogs0057.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0057.rows ScalarLogs0057.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0057.rows ScalarLogs0057.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0057.rows ScalarLogs0057.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0057.rows ScalarLogs0057.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0028.bracket0458 BracketBatch0028.bracket0459 (1498579011834704118059549726875036006469/10000000000000000000000000000000000000000) (377707895877763081504921365977693931/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0028.bracket0458 BracketBatch0028.bracket0459
  (1498579011834704118059549726875036006469/10000000000000000000000000000000000000000) (377707895877763081504921365977693931/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0458
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0459
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0071.rows BesselBatch0071.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0071.rows BesselBatch0071.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0071.rows BesselBatch0071.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0071.rows BesselBatch0071.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0071.rows BesselBatch0071.accepted ⟨50,by decide⟩
]
theorem leftAccepted : besselPointCheck (299922598375780313840165203413359947167/2000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (299922598375780313840165203413359947167/2000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0071.rows BesselBatch0071.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0071.rows BesselBatch0071.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0071.rows BesselBatch0071.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0072.rows BesselBatch0072.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0072.rows BesselBatch0072.accepted ⟨1,by decide⟩
]
theorem rightAccepted : besselPointCheck (300336228258965998745089752810032508921/2000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (300336228258965998745089752810032508921/2000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0524.rows BesselBatch0524.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0524.rows BesselBatch0524.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0524.rows BesselBatch0524.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0524.rows BesselBatch0524.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0524.rows BesselBatch0524.accepted ⟨53,by decide⟩
]
theorem midAccepted : besselPointCheck (75032353329343289073156869527924057011/500000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (75032353329343289073156869527924057011/500000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0057.rows ScalarLogs0057.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0057.rows ScalarLogs0057.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0057.rows ScalarLogs0057.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0057.rows ScalarLogs0057.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0057.rows ScalarLogs0057.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0057.rows ScalarLogs0057.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0057.rows ScalarLogs0057.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0057.rows ScalarLogs0057.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0057.rows ScalarLogs0057.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0057.rows ScalarLogs0057.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0057.rows ScalarLogs0057.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0057.rows ScalarLogs0057.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0057.rows ScalarLogs0057.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0057.rows ScalarLogs0057.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0057.rows ScalarLogs0057.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0057.rows ScalarLogs0057.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0028.bracket0459 BracketBatch0028.bracket0460 (75032353329343289073156869527924057011/500000000000000000000000000000000000000) (94940939450665837754752697243620519/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0028.bracket0459 BracketBatch0028.bracket0460
  (75032353329343289073156869527924057011/500000000000000000000000000000000000000) (94940939450665837754752697243620519/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0459
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0460
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0071.rows BesselBatch0071.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0071.rows BesselBatch0071.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0071.rows BesselBatch0071.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0071.rows BesselBatch0071.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0071.rows BesselBatch0071.accepted ⟨60,by decide⟩
]
theorem leftAccepted : besselPointCheck (750840570647414996862724382025081272301/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (750840570647414996862724382025081272301/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0072.rows BesselBatch0072.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0072.rows BesselBatch0072.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0072.rows BesselBatch0072.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0072.rows BesselBatch0072.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0072.rows BesselBatch0072.accepted ⟨11,by decide⟩
]
theorem rightAccepted : besselPointCheck (375937370081435325761036832630095652893/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (375937370081435325761036832630095652893/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0524.rows BesselBatch0524.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0524.rows BesselBatch0524.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0524.rows BesselBatch0524.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0524.rows BesselBatch0524.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0524.rows BesselBatch0524.accepted ⟨58,by decide⟩
]
theorem midAccepted : besselPointCheck (1502715310810285648384798047285272578087/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1502715310810285648384798047285272578087/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0057.rows ScalarLogs0057.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0057.rows ScalarLogs0057.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0057.rows ScalarLogs0057.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0057.rows ScalarLogs0057.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0057.rows ScalarLogs0057.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0057.rows ScalarLogs0057.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0057.rows ScalarLogs0057.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0057.rows ScalarLogs0057.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0057.rows ScalarLogs0057.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0057.rows ScalarLogs0057.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0057.rows ScalarLogs0057.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0057.rows ScalarLogs0057.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0057.rows ScalarLogs0057.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0057.rows ScalarLogs0057.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0057.rows ScalarLogs0057.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0057.rows ScalarLogs0057.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0028.bracket0460 BracketBatch0028.bracket0461 (1502715310810285648384798047285272578087/10000000000000000000000000000000000000000) (381828029443357011808298716751335339/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0028.bracket0460 BracketBatch0028.bracket0461
  (1502715310810285648384798047285272578087/10000000000000000000000000000000000000000) (381828029443357011808298716751335339/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0460
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0461
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0072.rows BesselBatch0072.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0072.rows BesselBatch0072.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0072.rows BesselBatch0072.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0072.rows BesselBatch0072.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0072.rows BesselBatch0072.accepted ⟨6,by decide⟩
]
theorem leftAccepted : besselPointCheck (1503749480325741303044147330520382611569/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1503749480325741303044147330520382611569/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0072.rows BesselBatch0072.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0072.rows BesselBatch0072.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0072.rows BesselBatch0072.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0072.rows BesselBatch0072.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0072.rows BesselBatch0072.accepted ⟨21,by decide⟩
]
theorem rightAccepted : besselPointCheck (752909004629611278176519584967619994467/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (752909004629611278176519584967619994467/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0524.rows BesselBatch0524.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0524.rows BesselBatch0524.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0524.rows BesselBatch0524.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0524.rows BesselBatch0524.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0524.rows BesselBatch0524.accepted ⟨63,by decide⟩
]
theorem midAccepted : besselPointCheck (3009567489584963859397186500455622600503/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (3009567489584963859397186500455622600503/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0057.rows ScalarLogs0057.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0057.rows ScalarLogs0057.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0057.rows ScalarLogs0057.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0057.rows ScalarLogs0057.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0057.rows ScalarLogs0057.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0057.rows ScalarLogs0057.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0057.rows ScalarLogs0057.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0057.rows ScalarLogs0057.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0057.rows ScalarLogs0057.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0057.rows ScalarLogs0057.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0057.rows ScalarLogs0057.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0057.rows ScalarLogs0057.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0057.rows ScalarLogs0057.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0057.rows ScalarLogs0057.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0057.rows ScalarLogs0057.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0057.rows ScalarLogs0057.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0028.bracket0461 BracketBatch0028.bracket0462 (3009567489584963859397186500455622600503/20000000000000000000000000000000000000000) (383900703282644033347884314080119511/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0028.bracket0461 BracketBatch0028.bracket0462
  (3009567489584963859397186500455622600503/20000000000000000000000000000000000000000) (383900703282644033347884314080119511/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0461
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0462
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0072.rows BesselBatch0072.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0072.rows BesselBatch0072.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0072.rows BesselBatch0072.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0072.rows BesselBatch0072.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0072.rows BesselBatch0072.accepted ⟨16,by decide⟩
]
theorem leftAccepted : besselPointCheck (1505818009259222556353039169935239988931/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1505818009259222556353039169935239988931/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0072.rows BesselBatch0072.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0072.rows BesselBatch0072.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0072.rows BesselBatch0072.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0072.rows BesselBatch0072.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0072.rows BesselBatch0072.accepted ⟨31,by decide⟩
]
theorem rightAccepted : besselPointCheck (753943364191499375092492610554794737991/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (753943364191499375092492610554794737991/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0525.rows BesselBatch0525.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0525.rows BesselBatch0525.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0525.rows BesselBatch0525.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0525.rows BesselBatch0525.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0525.rows BesselBatch0525.accepted ⟨4,by decide⟩
]
theorem midAccepted : besselPointCheck (3013704737642221306538024391044829464913/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (3013704737642221306538024391044829464913/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0057.rows ScalarLogs0057.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0057.rows ScalarLogs0057.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0057.rows ScalarLogs0057.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0057.rows ScalarLogs0057.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0057.rows ScalarLogs0057.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0057.rows ScalarLogs0057.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0057.rows ScalarLogs0057.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0057.rows ScalarLogs0057.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0057.rows ScalarLogs0057.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0057.rows ScalarLogs0057.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0057.rows ScalarLogs0057.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0057.rows ScalarLogs0057.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0057.rows ScalarLogs0057.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0057.rows ScalarLogs0057.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0057.rows ScalarLogs0057.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0057.rows ScalarLogs0057.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0028.bracket0462 BracketBatch0028.bracket0463 (3013704737642221306538024391044829464913/20000000000000000000000000000000000000000) (385981833244009386193875375219788569/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0028.bracket0462 BracketBatch0028.bracket0463
  (3013704737642221306538024391044829464913/20000000000000000000000000000000000000000) (385981833244009386193875375219788569/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0462
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0463
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0072.rows BesselBatch0072.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0072.rows BesselBatch0072.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0072.rows BesselBatch0072.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0072.rows BesselBatch0072.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0072.rows BesselBatch0072.accepted ⟨26,by decide⟩
]
theorem leftAccepted : besselPointCheck (1507886728382998750184985221109589475979/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1507886728382998750184985221109589475979/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0072.rows BesselBatch0072.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0072.rows BesselBatch0072.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0072.rows BesselBatch0072.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0072.rows BesselBatch0072.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0072.rows BesselBatch0072.accepted ⟨41,by decide⟩
]
theorem rightAccepted : besselPointCheck (1509955637984933059349557520272448810371/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1509955637984933059349557520272448810371/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0525.rows BesselBatch0525.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0525.rows BesselBatch0525.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0525.rows BesselBatch0525.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0525.rows BesselBatch0525.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0525.rows BesselBatch0525.accepted ⟨9,by decide⟩
]
theorem midAccepted : besselPointCheck (60356847327358636190690854827640765727/400000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (60356847327358636190690854827640765727/400000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0057.rows ScalarLogs0057.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0057.rows ScalarLogs0057.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0057.rows ScalarLogs0057.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0057.rows ScalarLogs0057.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0057.rows ScalarLogs0057.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0057.rows ScalarLogs0057.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0057.rows ScalarLogs0057.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0057.rows ScalarLogs0057.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0057.rows ScalarLogs0057.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0057.rows ScalarLogs0057.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0057.rows ScalarLogs0057.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0057.rows ScalarLogs0057.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0057.rows ScalarLogs0057.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0057.rows ScalarLogs0057.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0057.rows ScalarLogs0057.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0057.rows ScalarLogs0057.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0028.bracket0463 BracketBatch0029.bracket0464 (60356847327358636190690854827640765727/400000000000000000000000000000000000000) (19403572130384112366281132665928123/500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0028.bracket0463 BracketBatch0029.bracket0464
  (60356847327358636190690854827640765727/400000000000000000000000000000000000000) (19403572130384112366281132665928123/500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0463
