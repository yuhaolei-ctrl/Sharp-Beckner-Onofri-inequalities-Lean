import BecknerOnofri.EntropyScalarCertificate.Bessel0302
import BecknerOnofri.EntropyScalarCertificate.Bessel0303
import BecknerOnofri.EntropyScalarCertificate.Bessel0640
import BecknerOnofri.EntropyScalarCertificate.Brackets0121
import BecknerOnofri.EntropyScalarCertificate.Logs0242
import BecknerOnofri.ScalarElementaryComposition
import BecknerOnofri.ScalarGammaEnclosure
import BecknerOnofri.ScalarLogBesselEndpoints
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1936
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0302.rows BesselBatch0302.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0302.rows BesselBatch0302.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0302.rows BesselBatch0302.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0302.rows BesselBatch0302.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0302.rows BesselBatch0302.accepted ⟨36,by decide⟩
]
theorem leftAccepted : besselPointCheck (36628679054752337226654889755213737195281/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (36628679054752337226654889755213737195281/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0302.rows BesselBatch0302.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0302.rows BesselBatch0302.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0302.rows BesselBatch0302.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0302.rows BesselBatch0302.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0302.rows BesselBatch0302.accepted ⟨51,by decide⟩
]
theorem rightAccepted : besselPointCheck (36876849367050879391016471654876667360393/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (36876849367050879391016471654876667360393/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0640.rows BesselBatch0640.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0640.rows BesselBatch0640.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0640.rows BesselBatch0640.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0640.rows BesselBatch0640.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0640.rows BesselBatch0640.accepted ⟨14,by decide⟩
]
theorem midAccepted : besselPointCheck (36752764210901608308835680705045202277837/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (36752764210901608308835680705045202277837/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0242.rows ScalarLogs0242.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0242.rows ScalarLogs0242.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0242.rows ScalarLogs0242.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0242.rows ScalarLogs0242.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0242.rows ScalarLogs0242.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0242.rows ScalarLogs0242.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0242.rows ScalarLogs0242.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0242.rows ScalarLogs0242.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0242.rows ScalarLogs0242.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0242.rows ScalarLogs0242.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0242.rows ScalarLogs0242.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0242.rows ScalarLogs0242.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0242.rows ScalarLogs0242.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0242.rows ScalarLogs0242.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0242.rows ScalarLogs0242.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0242.rows ScalarLogs0242.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0121.bracket1936 BracketBatch0121.bracket1937 (36752764210901608308835680705045202277837/10000000000000000000000000000000000000000) (1479118518288397040473498930603722159327/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0121.bracket1936 BracketBatch0121.bracket1937
  (36752764210901608308835680705045202277837/10000000000000000000000000000000000000000) (1479118518288397040473498930603722159327/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1936
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1937
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0302.rows BesselBatch0302.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0302.rows BesselBatch0302.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0302.rows BesselBatch0302.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0302.rows BesselBatch0302.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0302.rows BesselBatch0302.accepted ⟨46,by decide⟩
]
theorem leftAccepted : besselPointCheck (3687684936705087939101647165487666736039/1000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (3687684936705087939101647165487666736039/1000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0302.rows BesselBatch0302.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0302.rows BesselBatch0302.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0302.rows BesselBatch0302.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0302.rows BesselBatch0302.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0302.rows BesselBatch0302.accepted ⟨61,by decide⟩
]
theorem rightAccepted : besselPointCheck (37128595738869822277565299441204635048501/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (37128595738869822277565299441204635048501/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0640.rows BesselBatch0640.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0640.rows BesselBatch0640.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0640.rows BesselBatch0640.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0640.rows BesselBatch0640.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0640.rows BesselBatch0640.accepted ⟨19,by decide⟩
]
theorem midAccepted : besselPointCheck (74005445105920701668581771096081302408891/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (74005445105920701668581771096081302408891/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0242.rows ScalarLogs0242.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0242.rows ScalarLogs0242.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0242.rows ScalarLogs0242.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0242.rows ScalarLogs0242.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0242.rows ScalarLogs0242.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0242.rows ScalarLogs0242.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0242.rows ScalarLogs0242.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0242.rows ScalarLogs0242.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0242.rows ScalarLogs0242.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0242.rows ScalarLogs0242.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0242.rows ScalarLogs0242.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0242.rows ScalarLogs0242.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0242.rows ScalarLogs0242.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0242.rows ScalarLogs0242.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0242.rows ScalarLogs0242.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0242.rows ScalarLogs0242.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0121.bracket1937 BracketBatch0121.bracket1938 (74005445105920701668581771096081302408891/20000000000000000000000000000000000000000) (1487194359938855006300744422534777348939/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0121.bracket1937 BracketBatch0121.bracket1938
  (74005445105920701668581771096081302408891/20000000000000000000000000000000000000000) (1487194359938855006300744422534777348939/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1937
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1938
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0302.rows BesselBatch0302.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0302.rows BesselBatch0302.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0302.rows BesselBatch0302.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0302.rows BesselBatch0302.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0302.rows BesselBatch0302.accepted ⟨56,by decide⟩
]
theorem leftAccepted : besselPointCheck (18564297869434911138782649720602317524249/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (18564297869434911138782649720602317524249/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0303.rows BesselBatch0303.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0303.rows BesselBatch0303.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0303.rows BesselBatch0303.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0303.rows BesselBatch0303.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0303.rows BesselBatch0303.accepted ⟨7,by decide⟩
]
theorem rightAccepted : besselPointCheck (18691997541874343318834663256207621967009/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (18691997541874343318834663256207621967009/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0640.rows BesselBatch0640.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0640.rows BesselBatch0640.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0640.rows BesselBatch0640.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0640.rows BesselBatch0640.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0640.rows BesselBatch0640.accepted ⟨24,by decide⟩
]
theorem midAccepted : besselPointCheck (18628147705654627228808656488404969745629/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (18628147705654627228808656488404969745629/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0242.rows ScalarLogs0242.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0242.rows ScalarLogs0242.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0242.rows ScalarLogs0242.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0242.rows ScalarLogs0242.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0242.rows ScalarLogs0242.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0242.rows ScalarLogs0242.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0242.rows ScalarLogs0242.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0242.rows ScalarLogs0242.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0242.rows ScalarLogs0242.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0242.rows ScalarLogs0242.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0242.rows ScalarLogs0242.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0242.rows ScalarLogs0242.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0242.rows ScalarLogs0242.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0242.rows ScalarLogs0242.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0242.rows ScalarLogs0242.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0242.rows ScalarLogs0242.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0121.bracket1938 BracketBatch0121.bracket1939 (18628147705654627228808656488404969745629/5000000000000000000000000000000000000000) (1495337676080299383904776459257514334887/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0121.bracket1938 BracketBatch0121.bracket1939
  (18628147705654627228808656488404969745629/5000000000000000000000000000000000000000) (1495337676080299383904776459257514334887/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1938
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1939
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0302.rows BesselBatch0302.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0302.rows BesselBatch0302.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0303.rows BesselBatch0303.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0303.rows BesselBatch0303.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0303.rows BesselBatch0303.accepted ⟨2,by decide⟩
]
theorem leftAccepted : besselPointCheck (7476799016749737327533865302483048786803/2000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (7476799016749737327533865302483048786803/2000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0303.rows BesselBatch0303.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0303.rows BesselBatch0303.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0303.rows BesselBatch0303.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0303.rows BesselBatch0303.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0303.rows BesselBatch0303.accepted ⟨17,by decide⟩
]
theorem rightAccepted : besselPointCheck (301145012362805294387344360879290685103/80000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (301145012362805294387344360879290685103/80000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0640.rows BesselBatch0640.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0640.rows BesselBatch0640.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0640.rows BesselBatch0640.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0640.rows BesselBatch0640.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0640.rows BesselBatch0640.accepted ⟨29,by decide⟩
]
theorem midAccepted : besselPointCheck (7502712162909934843608737162232657957189/2000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (7502712162909934843608737162232657957189/2000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0242.rows ScalarLogs0242.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0242.rows ScalarLogs0242.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0242.rows ScalarLogs0242.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0242.rows ScalarLogs0242.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0242.rows ScalarLogs0242.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0242.rows ScalarLogs0242.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0242.rows ScalarLogs0242.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0242.rows ScalarLogs0242.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0242.rows ScalarLogs0242.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0242.rows ScalarLogs0242.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0242.rows ScalarLogs0242.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0242.rows ScalarLogs0242.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0242.rows ScalarLogs0242.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0242.rows ScalarLogs0242.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0242.rows ScalarLogs0242.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0242.rows ScalarLogs0242.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0121.bracket1939 BracketBatch0121.bracket1940 (7502712162909934843608737162232657957189/2000000000000000000000000000000000000000) (75177467445428943213954389254991394027/500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0121.bracket1939 BracketBatch0121.bracket1940
  (7502712162909934843608737162232657957189/2000000000000000000000000000000000000000) (75177467445428943213954389254991394027/500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1939
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1940
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0303.rows BesselBatch0303.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0303.rows BesselBatch0303.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0303.rows BesselBatch0303.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0303.rows BesselBatch0303.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0303.rows BesselBatch0303.accepted ⟨12,by decide⟩
]
theorem leftAccepted : besselPointCheck (2352695409084416362401127819369458477367/625000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (2352695409084416362401127819369458477367/625000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0303.rows BesselBatch0303.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0303.rows BesselBatch0303.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0303.rows BesselBatch0303.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0303.rows BesselBatch0303.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0303.rows BesselBatch0303.accepted ⟨27,by decide⟩
]
theorem rightAccepted : besselPointCheck (9476517894764758172345661872230279183703/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (9476517894764758172345661872230279183703/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0640.rows BesselBatch0640.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0640.rows BesselBatch0640.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0640.rows BesselBatch0640.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0640.rows BesselBatch0640.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0640.rows BesselBatch0640.accepted ⟨34,by decide⟩
]
theorem midAccepted : besselPointCheck (18887299531102423621950173149708113093171/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (18887299531102423621950173149708113093171/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0242.rows ScalarLogs0242.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0242.rows ScalarLogs0242.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0242.rows ScalarLogs0242.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0242.rows ScalarLogs0242.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0242.rows ScalarLogs0242.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0242.rows ScalarLogs0242.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0242.rows ScalarLogs0242.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0242.rows ScalarLogs0242.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0242.rows ScalarLogs0242.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0242.rows ScalarLogs0242.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0242.rows ScalarLogs0242.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0242.rows ScalarLogs0242.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0242.rows ScalarLogs0242.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0242.rows ScalarLogs0242.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0242.rows ScalarLogs0242.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0242.rows ScalarLogs0242.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0121.bracket1940 BracketBatch0121.bracket1941 (18887299531102423621950173149708113093171/5000000000000000000000000000000000000000) (755915139378257603256802266936098349279/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0121.bracket1940 BracketBatch0121.bracket1941
  (18887299531102423621950173149708113093171/5000000000000000000000000000000000000000) (755915139378257603256802266936098349279/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1940
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1941
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0303.rows BesselBatch0303.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0303.rows BesselBatch0303.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0303.rows BesselBatch0303.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0303.rows BesselBatch0303.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0303.rows BesselBatch0303.accepted ⟨22,by decide⟩
]
theorem leftAccepted : besselPointCheck (37906071579059032689382647488921116734809/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (37906071579059032689382647488921116734809/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0303.rows BesselBatch0303.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0303.rows BesselBatch0303.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0303.rows BesselBatch0303.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0303.rows BesselBatch0303.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0303.rows BesselBatch0303.accepted ⟨37,by decide⟩
]
theorem rightAccepted : besselPointCheck (19086457018583530844921356387479106856103/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (19086457018583530844921356387479106856103/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0640.rows BesselBatch0640.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0640.rows BesselBatch0640.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0640.rows BesselBatch0640.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0640.rows BesselBatch0640.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0640.rows BesselBatch0640.accepted ⟨39,by decide⟩
]
theorem midAccepted : besselPointCheck (15215797123245218875845072052775866089403/4000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (15215797123245218875845072052775866089403/4000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0242.rows ScalarLogs0242.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0242.rows ScalarLogs0242.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0242.rows ScalarLogs0242.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0242.rows ScalarLogs0242.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0242.rows ScalarLogs0242.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0242.rows ScalarLogs0242.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0242.rows ScalarLogs0242.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0242.rows ScalarLogs0242.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0242.rows ScalarLogs0242.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0242.rows ScalarLogs0242.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0242.rows ScalarLogs0242.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0242.rows ScalarLogs0242.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0242.rows ScalarLogs0242.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0242.rows ScalarLogs0242.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0242.rows ScalarLogs0242.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0242.rows ScalarLogs0242.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0121.bracket1941 BracketBatch0121.bracket1942 (15215797123245218875845072052775866089403/4000000000000000000000000000000000000000) (760090692296495811225654710613259864589/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0121.bracket1941 BracketBatch0121.bracket1942
  (15215797123245218875845072052775866089403/4000000000000000000000000000000000000000) (760090692296495811225654710613259864589/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1941
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1942
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0303.rows BesselBatch0303.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0303.rows BesselBatch0303.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0303.rows BesselBatch0303.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0303.rows BesselBatch0303.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0303.rows BesselBatch0303.accepted ⟨32,by decide⟩
]
theorem leftAccepted : besselPointCheck (38172914037167061689842712774958213712203/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (38172914037167061689842712774958213712203/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0303.rows BesselBatch0303.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0303.rows BesselBatch0303.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0303.rows BesselBatch0303.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0303.rows BesselBatch0303.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0303.rows BesselBatch0303.accepted ⟨47,by decide⟩
]
theorem rightAccepted : besselPointCheck (38443740257847313672911677144380035799953/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (38443740257847313672911677144380035799953/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0640.rows BesselBatch0640.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0640.rows BesselBatch0640.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0640.rows BesselBatch0640.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0640.rows BesselBatch0640.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0640.rows BesselBatch0640.accepted ⟨44,by decide⟩
]
theorem midAccepted : besselPointCheck (19154163573753593840688597479834562378039/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (19154163573753593840688597479834562378039/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0242.rows ScalarLogs0242.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0242.rows ScalarLogs0242.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0242.rows ScalarLogs0242.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0242.rows ScalarLogs0242.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0242.rows ScalarLogs0242.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0242.rows ScalarLogs0242.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0242.rows ScalarLogs0242.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0242.rows ScalarLogs0242.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0242.rows ScalarLogs0242.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0242.rows ScalarLogs0242.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0242.rows ScalarLogs0242.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0242.rows ScalarLogs0242.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0242.rows ScalarLogs0242.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0242.rows ScalarLogs0242.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0242.rows ScalarLogs0242.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0242.rows ScalarLogs0242.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0121.bracket1942 BracketBatch0121.bracket1943 (19154163573753593840688597479834562378039/5000000000000000000000000000000000000000) (191075450567181164221676816921399734923/1250000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0121.bracket1942 BracketBatch0121.bracket1943
  (19154163573753593840688597479834562378039/5000000000000000000000000000000000000000) (191075450567181164221676816921399734923/1250000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1942
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1943
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0303.rows BesselBatch0303.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0303.rows BesselBatch0303.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0303.rows BesselBatch0303.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0303.rows BesselBatch0303.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0303.rows BesselBatch0303.accepted ⟨42,by decide⟩
]
theorem leftAccepted : besselPointCheck (768874805156946273458233542887600715999/200000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (768874805156946273458233542887600715999/200000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0303.rows BesselBatch0303.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0303.rows BesselBatch0303.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0303.rows BesselBatch0303.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0303.rows BesselBatch0303.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0303.rows BesselBatch0303.accepted ⟨57,by decide⟩
]
theorem rightAccepted : besselPointCheck (38718639158097534877413117858833678247633/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (38718639158097534877413117858833678247633/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0640.rows BesselBatch0640.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0640.rows BesselBatch0640.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0640.rows BesselBatch0640.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0640.rows BesselBatch0640.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0640.rows BesselBatch0640.accepted ⟨49,by decide⟩
]
theorem midAccepted : besselPointCheck (77162379415944848550324795003213714047583/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (77162379415944848550324795003213714047583/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0242.rows ScalarLogs0242.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0242.rows ScalarLogs0242.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0242.rows ScalarLogs0242.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0242.rows ScalarLogs0242.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0242.rows ScalarLogs0242.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0242.rows ScalarLogs0242.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0242.rows ScalarLogs0242.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0242.rows ScalarLogs0242.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0242.rows ScalarLogs0242.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0242.rows ScalarLogs0242.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0242.rows ScalarLogs0242.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0242.rows ScalarLogs0242.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0242.rows ScalarLogs0242.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0242.rows ScalarLogs0242.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0242.rows ScalarLogs0242.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0242.rows ScalarLogs0242.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0121.bracket1943 BracketBatch0121.bracket1944 (77162379415944848550324795003213714047583/20000000000000000000000000000000000000000) (153709789639030522514939717477515027781/1000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0121.bracket1943 BracketBatch0121.bracket1944
  (77162379415944848550324795003213714047583/20000000000000000000000000000000000000000) (153709789639030522514939717477515027781/1000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1943
