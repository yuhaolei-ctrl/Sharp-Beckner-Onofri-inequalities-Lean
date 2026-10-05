module

public import BecknerOnofri.EntropyScalarCertificate.Bessel0043
public import BecknerOnofri.EntropyScalarCertificate.Bessel0044
public import BecknerOnofri.EntropyScalarCertificate.Bessel0045
public import BecknerOnofri.EntropyScalarCertificate.Bessel0510
public import BecknerOnofri.EntropyScalarCertificate.Bessel0511
public import BecknerOnofri.EntropyScalarCertificate.Brackets0017
public import BecknerOnofri.EntropyScalarCertificate.Brackets0018
public import BecknerOnofri.EntropyScalarCertificate.Logs0035
public import BecknerOnofri.ScalarElementaryComposition
public import BecknerOnofri.ScalarGammaEnclosure
public import BecknerOnofri.ScalarLogBesselEndpoints

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0280
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0043.rows BesselBatch0043.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0043.rows BesselBatch0043.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0043.rows BesselBatch0043.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0043.rows BesselBatch0043.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0043.rows BesselBatch0043.accepted ⟨52,by decide⟩
]
theorem leftAccepted : besselPointCheck (283048784926190953257105189466583195001/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (283048784926190953257105189466583195001/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0043.rows BesselBatch0043.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0044.rows BesselBatch0044.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0044.rows BesselBatch0044.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0044.rows BesselBatch0044.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0044.rows BesselBatch0044.accepted ⟨3,by decide⟩
]
theorem rightAccepted : besselPointCheck (1134233857273870511866496724195384568947/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1134233857273870511866496724195384568947/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0510.rows BesselBatch0510.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0510.rows BesselBatch0510.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0510.rows BesselBatch0510.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0510.rows BesselBatch0510.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0510.rows BesselBatch0510.accepted ⟨54,by decide⟩
]
theorem midAccepted : besselPointCheck (2266428996978634324894917482061717348951/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (2266428996978634324894917482061717348951/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0035.rows ScalarLogs0035.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0035.rows ScalarLogs0035.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0035.rows ScalarLogs0035.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0035.rows ScalarLogs0035.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0035.rows ScalarLogs0035.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0035.rows ScalarLogs0035.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0035.rows ScalarLogs0035.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0035.rows ScalarLogs0035.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0035.rows ScalarLogs0035.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0035.rows ScalarLogs0035.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0035.rows ScalarLogs0035.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0035.rows ScalarLogs0035.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0035.rows ScalarLogs0035.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0035.rows ScalarLogs0035.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0035.rows ScalarLogs0035.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0035.rows ScalarLogs0035.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0017.bracket0280 BracketBatch0017.bracket0281 (2266428996978634324894917482061717348951/20000000000000000000000000000000000000000) (31253142508694463303436352736281667/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0017.bracket0280 BracketBatch0017.bracket0281
  (2266428996978634324894917482061717348951/20000000000000000000000000000000000000000) (31253142508694463303436352736281667/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0280
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0281
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0043.rows BesselBatch0043.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0043.rows BesselBatch0043.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0043.rows BesselBatch0043.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0043.rows BesselBatch0043.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0043.rows BesselBatch0043.accepted ⟨62,by decide⟩
]
theorem leftAccepted : besselPointCheck (70889616079616906991656045262211535559/625000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (70889616079616906991656045262211535559/625000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0044.rows BesselBatch0044.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0044.rows BesselBatch0044.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0044.rows BesselBatch0044.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0044.rows BesselBatch0044.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0044.rows BesselBatch0044.accepted ⟨13,by decide⟩
]
theorem rightAccepted : besselPointCheck (45450908599121457596070630714288168689/400000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (45450908599121457596070630714288168689/400000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0510.rows BesselBatch0510.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0510.rows BesselBatch0510.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0510.rows BesselBatch0510.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0510.rows BesselBatch0510.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0510.rows BesselBatch0510.accepted ⟨59,by decide⟩
]
theorem midAccepted : besselPointCheck (2270506572251906951768262492052588786169/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (2270506572251906951768262492052588786169/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0035.rows ScalarLogs0035.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0035.rows ScalarLogs0035.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0035.rows ScalarLogs0035.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0035.rows ScalarLogs0035.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0035.rows ScalarLogs0035.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0035.rows ScalarLogs0035.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0035.rows ScalarLogs0035.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0035.rows ScalarLogs0035.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0035.rows ScalarLogs0035.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0035.rows ScalarLogs0035.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0035.rows ScalarLogs0035.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0035.rows ScalarLogs0035.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0035.rows ScalarLogs0035.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0035.rows ScalarLogs0035.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0035.rows ScalarLogs0035.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0035.rows ScalarLogs0035.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0017.bracket0281 BracketBatch0017.bracket0282 (2270506572251906951768262492052588786169/20000000000000000000000000000000000000000) (12590914462273905021592290386127191/1000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0017.bracket0281 BracketBatch0017.bracket0282
  (2270506572251906951768262492052588786169/20000000000000000000000000000000000000000) (12590914462273905021592290386127191/1000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0281
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0282
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0044.rows BesselBatch0044.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0044.rows BesselBatch0044.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0044.rows BesselBatch0044.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0044.rows BesselBatch0044.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0044.rows BesselBatch0044.accepted ⟨8,by decide⟩
]
theorem leftAccepted : besselPointCheck (568136357489018219950882883928602108611/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (568136357489018219950882883928602108611/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0044.rows BesselBatch0044.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0044.rows BesselBatch0044.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0044.rows BesselBatch0044.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0044.rows BesselBatch0044.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0044.rows BesselBatch0044.accepted ⟨23,by decide⟩
]
theorem rightAccepted : besselPointCheck (1138311713083819773780657145154299162701/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1138311713083819773780657145154299162701/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0510.rows BesselBatch0510.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0510.rows BesselBatch0510.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0510.rows BesselBatch0510.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0510.rows BesselBatch0510.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0511.rows BesselBatch0511.accepted ⟨0,by decide⟩
]
theorem midAccepted : besselPointCheck (2274584428061856213682422913011503379923/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (2274584428061856213682422913011503379923/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0035.rows ScalarLogs0035.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0035.rows ScalarLogs0035.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0035.rows ScalarLogs0035.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0035.rows ScalarLogs0035.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0035.rows ScalarLogs0035.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0035.rows ScalarLogs0035.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0035.rows ScalarLogs0035.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0035.rows ScalarLogs0035.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0035.rows ScalarLogs0035.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0035.rows ScalarLogs0035.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0035.rows ScalarLogs0035.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0035.rows ScalarLogs0035.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0035.rows ScalarLogs0035.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0035.rows ScalarLogs0035.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0035.rows ScalarLogs0035.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0035.rows ScalarLogs0035.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0017.bracket0282 BracketBatch0017.bracket0283 (2274584428061856213682422913011503379923/20000000000000000000000000000000000000000) (3962829067707413718809185265192943/312500000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0017.bracket0282 BracketBatch0017.bracket0283
  (2274584428061856213682422913011503379923/20000000000000000000000000000000000000000) (3962829067707413718809185265192943/312500000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0282
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0283
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0044.rows BesselBatch0044.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0044.rows BesselBatch0044.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0044.rows BesselBatch0044.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0044.rows BesselBatch0044.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0044.rows BesselBatch0044.accepted ⟨18,by decide⟩
]
theorem leftAccepted : besselPointCheck (569155856541909886890328572577149581349/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (569155856541909886890328572577149581349/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0044.rows BesselBatch0044.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0044.rows BesselBatch0044.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0044.rows BesselBatch0044.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0044.rows BesselBatch0044.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0044.rows BesselBatch0044.accepted ⟨33,by decide⟩
]
theorem rightAccepted : besselPointCheck (142543856482234628882173628329438947119/1250000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (142543856482234628882173628329438947119/1250000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0511.rows BesselBatch0511.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0511.rows BesselBatch0511.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0511.rows BesselBatch0511.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0511.rows BesselBatch0511.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0511.rows BesselBatch0511.accepted ⟨5,by decide⟩
]
theorem midAccepted : besselPointCheck (45573251298833936096760923435796214793/400000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (45573251298833936096760923435796214793/400000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0035.rows ScalarLogs0035.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0035.rows ScalarLogs0035.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0035.rows ScalarLogs0035.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0035.rows ScalarLogs0035.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0035.rows ScalarLogs0035.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0035.rows ScalarLogs0035.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0035.rows ScalarLogs0035.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0035.rows ScalarLogs0035.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0035.rows ScalarLogs0035.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0035.rows ScalarLogs0035.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0035.rows ScalarLogs0035.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0035.rows ScalarLogs0035.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0035.rows ScalarLogs0035.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0035.rows ScalarLogs0035.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0035.rows ScalarLogs0035.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0035.rows ScalarLogs0035.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0017.bracket0283 BracketBatch0017.bracket0284 (45573251298833936096760923435796214793/400000000000000000000000000000000000000) (127716743978774226119163619617356271/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0017.bracket0283 BracketBatch0017.bracket0284
  (45573251298833936096760923435796214793/400000000000000000000000000000000000000) (127716743978774226119163619617356271/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0283
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0284
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0044.rows BesselBatch0044.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0044.rows BesselBatch0044.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0044.rows BesselBatch0044.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0044.rows BesselBatch0044.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0044.rows BesselBatch0044.accepted ⟨28,by decide⟩
]
theorem leftAccepted : besselPointCheck (1140350851857877031057389026635511576949/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1140350851857877031057389026635511576949/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0044.rows BesselBatch0044.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0044.rows BesselBatch0044.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0044.rows BesselBatch0044.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0044.rows BesselBatch0044.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0044.rows BesselBatch0044.accepted ⟨43,by decide⟩
]
theorem rightAccepted : besselPointCheck (1142390131566963274243389203051747449961/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1142390131566963274243389203051747449961/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0511.rows BesselBatch0511.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0511.rows BesselBatch0511.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0511.rows BesselBatch0511.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0511.rows BesselBatch0511.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0511.rows BesselBatch0511.accepted ⟨10,by decide⟩
]
theorem midAccepted : besselPointCheck (228274098342484030530077822968725902691/2000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (228274098342484030530077822968725902691/2000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0035.rows ScalarLogs0035.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0035.rows ScalarLogs0035.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0035.rows ScalarLogs0035.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0035.rows ScalarLogs0035.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0035.rows ScalarLogs0035.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0035.rows ScalarLogs0035.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0035.rows ScalarLogs0035.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0035.rows ScalarLogs0035.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0035.rows ScalarLogs0035.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0035.rows ScalarLogs0035.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0035.rows ScalarLogs0035.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0035.rows ScalarLogs0035.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0035.rows ScalarLogs0035.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0035.rows ScalarLogs0035.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0035.rows ScalarLogs0035.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0035.rows ScalarLogs0035.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0017.bracket0284 BracketBatch0017.bracket0285 (228274098342484030530077822968725902691/2000000000000000000000000000000000000000) (64313901701869862434100563429950583/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0017.bracket0284 BracketBatch0017.bracket0285
  (228274098342484030530077822968725902691/2000000000000000000000000000000000000000) (64313901701869862434100563429950583/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0284
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0285
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0044.rows BesselBatch0044.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0044.rows BesselBatch0044.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0044.rows BesselBatch0044.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0044.rows BesselBatch0044.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0044.rows BesselBatch0044.accepted ⟨38,by decide⟩
]
theorem leftAccepted : besselPointCheck (571195065783481637121694601525873724979/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (571195065783481637121694601525873724979/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0044.rows BesselBatch0044.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0044.rows BesselBatch0044.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0044.rows BesselBatch0044.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0044.rows BesselBatch0044.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0044.rows BesselBatch0044.accepted ⟨53,by decide⟩
]
theorem rightAccepted : besselPointCheck (286107388119483078756265667601390469819/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (286107388119483078756265667601390469819/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0511.rows BesselBatch0511.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0511.rows BesselBatch0511.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0511.rows BesselBatch0511.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0511.rows BesselBatch0511.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0511.rows BesselBatch0511.accepted ⟨15,by decide⟩
]
theorem midAccepted : besselPointCheck (1143409842022447794634225936728654664617/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1143409842022447794634225936728654664617/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0035.rows ScalarLogs0035.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0035.rows ScalarLogs0035.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0035.rows ScalarLogs0035.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0035.rows ScalarLogs0035.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0035.rows ScalarLogs0035.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0035.rows ScalarLogs0035.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0035.rows ScalarLogs0035.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0035.rows ScalarLogs0035.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0035.rows ScalarLogs0035.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0035.rows ScalarLogs0035.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0035.rows ScalarLogs0035.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0035.rows ScalarLogs0035.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0035.rows ScalarLogs0035.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0035.rows ScalarLogs0035.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0035.rows ScalarLogs0035.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0035.rows ScalarLogs0035.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0017.bracket0285 BracketBatch0017.bracket0286 (1143409842022447794634225936728654664617/10000000000000000000000000000000000000000) (129543725818420050446464967757147943/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0017.bracket0285 BracketBatch0017.bracket0286
  (1143409842022447794634225936728654664617/10000000000000000000000000000000000000000) (129543725818420050446464967757147943/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0285
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0286
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0044.rows BesselBatch0044.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0044.rows BesselBatch0044.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0044.rows BesselBatch0044.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0044.rows BesselBatch0044.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0044.rows BesselBatch0044.accepted ⟨48,by decide⟩
]
theorem leftAccepted : besselPointCheck (1144429552477932315025062670405561879273/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1144429552477932315025062670405561879273/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0044.rows BesselBatch0044.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0044.rows BesselBatch0044.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0044.rows BesselBatch0044.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0044.rows BesselBatch0044.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0044.rows BesselBatch0044.accepted ⟨63,by decide⟩
]
theorem rightAccepted : besselPointCheck (1146469114857736918650295032912155487349/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1146469114857736918650295032912155487349/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0511.rows BesselBatch0511.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0511.rows BesselBatch0511.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0511.rows BesselBatch0511.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0511.rows BesselBatch0511.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0511.rows BesselBatch0511.accepted ⟨20,by decide⟩
]
theorem midAccepted : besselPointCheck (1145449333667834616837678851658858683311/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1145449333667834616837678851658858683311/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0035.rows ScalarLogs0035.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0035.rows ScalarLogs0035.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0035.rows ScalarLogs0035.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0035.rows ScalarLogs0035.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0035.rows ScalarLogs0035.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0035.rows ScalarLogs0035.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0035.rows ScalarLogs0035.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0035.rows ScalarLogs0035.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0035.rows ScalarLogs0035.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0035.rows ScalarLogs0035.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0035.rows ScalarLogs0035.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0035.rows ScalarLogs0035.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0035.rows ScalarLogs0035.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0035.rows ScalarLogs0035.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0035.rows ScalarLogs0035.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0035.rows ScalarLogs0035.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0017.bracket0286 BracketBatch0017.bracket0287 (1145449333667834616837678851658858683311/10000000000000000000000000000000000000000) (130464528632006832640126668745471619/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0017.bracket0286 BracketBatch0017.bracket0287
  (1145449333667834616837678851658858683311/10000000000000000000000000000000000000000) (130464528632006832640126668745471619/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0286
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0287
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0044.rows BesselBatch0044.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0044.rows BesselBatch0044.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0044.rows BesselBatch0044.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0044.rows BesselBatch0044.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0044.rows BesselBatch0044.accepted ⟨58,by decide⟩
]
theorem leftAccepted : besselPointCheck (573234557428868459325147516456077743673/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (573234557428868459325147516456077743673/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0045.rows BesselBatch0045.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0045.rows BesselBatch0045.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0045.rows BesselBatch0045.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0045.rows BesselBatch0045.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0045.rows BesselBatch0045.accepted ⟨9,by decide⟩
]
theorem rightAccepted : besselPointCheck (71781801185839313030255074598772838343/625000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (71781801185839313030255074598772838343/625000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0511.rows BesselBatch0511.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0511.rows BesselBatch0511.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0511.rows BesselBatch0511.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0511.rows BesselBatch0511.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0511.rows BesselBatch0511.accepted ⟨25,by decide⟩
]
theorem midAccepted : besselPointCheck (1147488966915582963567188113246260450417/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1147488966915582963567188113246260450417/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0035.rows ScalarLogs0035.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0035.rows ScalarLogs0035.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0035.rows ScalarLogs0035.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0035.rows ScalarLogs0035.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0035.rows ScalarLogs0035.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0035.rows ScalarLogs0035.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0035.rows ScalarLogs0035.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0035.rows ScalarLogs0035.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0035.rows ScalarLogs0035.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0035.rows ScalarLogs0035.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0035.rows ScalarLogs0035.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0035.rows ScalarLogs0035.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0035.rows ScalarLogs0035.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0035.rows ScalarLogs0035.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0035.rows ScalarLogs0035.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0035.rows ScalarLogs0035.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0017.bracket0287 BracketBatch0018.bracket0288 (1147488966915582963567188113246260450417/10000000000000000000000000000000000000000) (131390229286005746075659005951637521/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0017.bracket0287 BracketBatch0018.bracket0288
  (1147488966915582963567188113246260450417/10000000000000000000000000000000000000000) (131390229286005746075659005951637521/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0287
