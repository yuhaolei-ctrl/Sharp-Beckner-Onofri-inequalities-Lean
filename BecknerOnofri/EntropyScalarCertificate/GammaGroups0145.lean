import BecknerOnofri.EntropyScalarCertificate.Bessel0181
import BecknerOnofri.EntropyScalarCertificate.Bessel0182
import BecknerOnofri.EntropyScalarCertificate.Bessel0579
import BecknerOnofri.EntropyScalarCertificate.Bessel0580
import BecknerOnofri.EntropyScalarCertificate.Brackets0072
import BecknerOnofri.EntropyScalarCertificate.Brackets0073
import BecknerOnofri.EntropyScalarCertificate.Logs0145
import BecknerOnofri.ScalarElementaryComposition
import BecknerOnofri.ScalarGammaEnclosure
import BecknerOnofri.ScalarLogBesselEndpoints
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1160
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0181.rows BesselBatch0181.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0181.rows BesselBatch0181.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0181.rows BesselBatch0181.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0181.rows BesselBatch0181.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0181.rows BesselBatch0181.accepted ⟨20,by decide⟩
]
theorem leftAccepted : besselPointCheck (1700813100597661898920284272364652948197/2000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1700813100597661898920284272364652948197/2000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0181.rows BesselBatch0181.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0181.rows BesselBatch0181.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0181.rows BesselBatch0181.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0181.rows BesselBatch0181.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0181.rows BesselBatch0181.accepted ⟨35,by decide⟩
]
theorem rightAccepted : besselPointCheck (4263939745240534052517582025185958610171/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (4263939745240534052517582025185958610171/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0579.rows BesselBatch0579.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0579.rows BesselBatch0579.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0579.rows BesselBatch0579.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0579.rows BesselBatch0579.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0579.rows BesselBatch0579.accepted ⟨38,by decide⟩
]
theorem midAccepted : besselPointCheck (17031944993469377599636585412195181961327/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (17031944993469377599636585412195181961327/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0145.rows ScalarLogs0145.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0145.rows ScalarLogs0145.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0145.rows ScalarLogs0145.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0145.rows ScalarLogs0145.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0145.rows ScalarLogs0145.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0145.rows ScalarLogs0145.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0145.rows ScalarLogs0145.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0145.rows ScalarLogs0145.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0145.rows ScalarLogs0145.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0145.rows ScalarLogs0145.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0145.rows ScalarLogs0145.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0145.rows ScalarLogs0145.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0145.rows ScalarLogs0145.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0145.rows ScalarLogs0145.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0145.rows ScalarLogs0145.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0145.rows ScalarLogs0145.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0072.bracket1160 BracketBatch0072.bracket1161 (17031944993469377599636585412195181961327/20000000000000000000000000000000000000000) (163511833988512429181902399389351203949/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0072.bracket1160 BracketBatch0072.bracket1161
  (17031944993469377599636585412195181961327/20000000000000000000000000000000000000000) (163511833988512429181902399389351203949/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1160
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1161
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0181.rows BesselBatch0181.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0181.rows BesselBatch0181.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0181.rows BesselBatch0181.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0181.rows BesselBatch0181.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0181.rows BesselBatch0181.accepted ⟨30,by decide⟩
]
theorem leftAccepted : besselPointCheck (8527879490481068105035164050371917220339/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (8527879490481068105035164050371917220339/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0181.rows BesselBatch0181.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0181.rows BesselBatch0181.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0181.rows BesselBatch0181.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0181.rows BesselBatch0181.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0181.rows BesselBatch0181.accepted ⟨45,by decide⟩
]
theorem rightAccepted : besselPointCheck (8551786561936146054946795275275307357457/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (8551786561936146054946795275275307357457/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0579.rows BesselBatch0579.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0579.rows BesselBatch0579.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0579.rows BesselBatch0579.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0579.rows BesselBatch0579.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0579.rows BesselBatch0579.accepted ⟨43,by decide⟩
]
theorem midAccepted : besselPointCheck (4269916513104303539995489831411806144449/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (4269916513104303539995489831411806144449/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0145.rows ScalarLogs0145.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0145.rows ScalarLogs0145.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0145.rows ScalarLogs0145.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0145.rows ScalarLogs0145.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0145.rows ScalarLogs0145.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0145.rows ScalarLogs0145.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0145.rows ScalarLogs0145.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0145.rows ScalarLogs0145.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0145.rows ScalarLogs0145.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0145.rows ScalarLogs0145.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0145.rows ScalarLogs0145.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0145.rows ScalarLogs0145.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0145.rows ScalarLogs0145.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0145.rows ScalarLogs0145.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0145.rows ScalarLogs0145.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0145.rows ScalarLogs0145.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0072.bracket1161 BracketBatch0072.bracket1162 (4269916513104303539995489831411806144449/5000000000000000000000000000000000000000) (82340269730179295486023183412780642449/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0072.bracket1161 BracketBatch0072.bracket1162
  (4269916513104303539995489831411806144449/5000000000000000000000000000000000000000) (82340269730179295486023183412780642449/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1161
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1162
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0181.rows BesselBatch0181.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0181.rows BesselBatch0181.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0181.rows BesselBatch0181.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0181.rows BesselBatch0181.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0181.rows BesselBatch0181.accepted ⟨40,by decide⟩
]
theorem leftAccepted : besselPointCheck (4275893280968073027473397637637653678727/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (4275893280968073027473397637637653678727/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0181.rows BesselBatch0181.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0181.rows BesselBatch0181.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0181.rows BesselBatch0181.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0181.rows BesselBatch0181.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0181.rows BesselBatch0181.accepted ⟨55,by decide⟩
]
theorem rightAccepted : besselPointCheck (8575787505883111932961312294344305265983/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (8575787505883111932961312294344305265983/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0579.rows BesselBatch0579.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0579.rows BesselBatch0579.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0579.rows BesselBatch0579.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0579.rows BesselBatch0579.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0579.rows BesselBatch0579.accepted ⟨48,by decide⟩
]
theorem midAccepted : besselPointCheck (17127574067819257987908107569619612623437/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (17127574067819257987908107569619612623437/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0145.rows ScalarLogs0145.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0145.rows ScalarLogs0145.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0145.rows ScalarLogs0145.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0145.rows ScalarLogs0145.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0145.rows ScalarLogs0145.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0145.rows ScalarLogs0145.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0145.rows ScalarLogs0145.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0145.rows ScalarLogs0145.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0145.rows ScalarLogs0145.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0145.rows ScalarLogs0145.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0145.rows ScalarLogs0145.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0145.rows ScalarLogs0145.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0145.rows ScalarLogs0145.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0145.rows ScalarLogs0145.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0145.rows ScalarLogs0145.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0145.rows ScalarLogs0145.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0072.bracket1162 BracketBatch0072.bracket1163 (17127574067819257987908107569619612623437/20000000000000000000000000000000000000000) (165856619110294349018060073922713383651/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0072.bracket1162 BracketBatch0072.bracket1163
  (17127574067819257987908107569619612623437/20000000000000000000000000000000000000000) (165856619110294349018060073922713383651/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1162
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1163
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0181.rows BesselBatch0181.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0181.rows BesselBatch0181.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0181.rows BesselBatch0181.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0181.rows BesselBatch0181.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0181.rows BesselBatch0181.accepted ⟨50,by decide⟩
]
theorem leftAccepted : besselPointCheck (428789375294155596648065614717215263299/500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (428789375294155596648065614717215263299/500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0181.rows BesselBatch0181.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0181.rows BesselBatch0181.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0181.rows BesselBatch0181.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0182.rows BesselBatch0182.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0182.rows BesselBatch0182.accepted ⟨1,by decide⟩
]
theorem rightAccepted : besselPointCheck (4299941560032971927293044695231606930393/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (4299941560032971927293044695231606930393/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0579.rows BesselBatch0579.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0579.rows BesselBatch0579.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0579.rows BesselBatch0579.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0579.rows BesselBatch0579.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0579.rows BesselBatch0579.accepted ⟨53,by decide⟩
]
theorem midAccepted : besselPointCheck (8587835312974527893773700842403759563383/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (8587835312974527893773700842403759563383/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0145.rows ScalarLogs0145.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0145.rows ScalarLogs0145.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0145.rows ScalarLogs0145.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0145.rows ScalarLogs0145.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0145.rows ScalarLogs0145.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0145.rows ScalarLogs0145.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0145.rows ScalarLogs0145.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0145.rows ScalarLogs0145.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0145.rows ScalarLogs0145.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0145.rows ScalarLogs0145.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0145.rows ScalarLogs0145.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0145.rows ScalarLogs0145.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0145.rows ScalarLogs0145.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0145.rows ScalarLogs0145.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0145.rows ScalarLogs0145.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0145.rows ScalarLogs0145.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0072.bracket1163 BracketBatch0072.bracket1164 (8587835312974527893773700842403759563383/10000000000000000000000000000000000000000) (83520060463990447775648660899424419581/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0072.bracket1163 BracketBatch0072.bracket1164
  (8587835312974527893773700842403759563383/10000000000000000000000000000000000000000) (83520060463990447775648660899424419581/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1163
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1164
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0181.rows BesselBatch0181.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0181.rows BesselBatch0181.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0181.rows BesselBatch0181.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0181.rows BesselBatch0181.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0181.rows BesselBatch0181.accepted ⟨60,by decide⟩
]
theorem leftAccepted : besselPointCheck (8599883120065943854586089390463213860783/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (8599883120065943854586089390463213860783/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0182.rows BesselBatch0182.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0182.rows BesselBatch0182.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0182.rows BesselBatch0182.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0182.rows BesselBatch0182.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0182.rows BesselBatch0182.accepted ⟨11,by decide⟩
]
theorem rightAccepted : besselPointCheck (2156018552895346527157504969290344372771/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (2156018552895346527157504969290344372771/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0579.rows BesselBatch0579.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0579.rows BesselBatch0579.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0579.rows BesselBatch0579.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0579.rows BesselBatch0579.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0579.rows BesselBatch0579.accepted ⟨58,by decide⟩
]
theorem midAccepted : besselPointCheck (17223957331647329963216109267624591351867/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (17223957331647329963216109267624591351867/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0145.rows ScalarLogs0145.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0145.rows ScalarLogs0145.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0145.rows ScalarLogs0145.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0145.rows ScalarLogs0145.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0145.rows ScalarLogs0145.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0145.rows ScalarLogs0145.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0145.rows ScalarLogs0145.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0145.rows ScalarLogs0145.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0145.rows ScalarLogs0145.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0145.rows ScalarLogs0145.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0145.rows ScalarLogs0145.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0145.rows ScalarLogs0145.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0145.rows ScalarLogs0145.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0145.rows ScalarLogs0145.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0145.rows ScalarLogs0145.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0145.rows ScalarLogs0145.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0072.bracket1164 BracketBatch0072.bracket1165 (17223957331647329963216109267624591351867/20000000000000000000000000000000000000000) (42057773333226176886567691456056678087/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0072.bracket1164 BracketBatch0072.bracket1165
  (17223957331647329963216109267624591351867/20000000000000000000000000000000000000000) (42057773333226176886567691456056678087/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1164
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1165
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0182.rows BesselBatch0182.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0182.rows BesselBatch0182.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0182.rows BesselBatch0182.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0182.rows BesselBatch0182.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0182.rows BesselBatch0182.accepted ⟨6,by decide⟩
]
theorem leftAccepted : besselPointCheck (8624074211581386108630019877161377491081/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (8624074211581386108630019877161377491081/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0182.rows BesselBatch0182.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0182.rows BesselBatch0182.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0182.rows BesselBatch0182.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0182.rows BesselBatch0182.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0182.rows BesselBatch0182.accepted ⟨21,by decide⟩
]
theorem rightAccepted : besselPointCheck (8648361597019812954035174007981450953599/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (8648361597019812954035174007981450953599/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0579.rows BesselBatch0579.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0579.rows BesselBatch0579.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0579.rows BesselBatch0579.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0579.rows BesselBatch0579.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0579.rows BesselBatch0579.accepted ⟨63,by decide⟩
]
theorem midAccepted : besselPointCheck (431810895215029976566629847128570711117/500000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (431810895215029976566629847128570711117/500000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0145.rows ScalarLogs0145.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0145.rows ScalarLogs0145.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0145.rows ScalarLogs0145.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0145.rows ScalarLogs0145.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0145.rows ScalarLogs0145.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0145.rows ScalarLogs0145.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0145.rows ScalarLogs0145.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0145.rows ScalarLogs0145.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0145.rows ScalarLogs0145.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0145.rows ScalarLogs0145.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0145.rows ScalarLogs0145.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0145.rows ScalarLogs0145.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0145.rows ScalarLogs0145.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0145.rows ScalarLogs0145.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0145.rows ScalarLogs0145.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0145.rows ScalarLogs0145.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0072.bracket1165 BracketBatch0072.bracket1166 (431810895215029976566629847128570711117/500000000000000000000000000000000000000) (8471479259005133904131222719510961417/500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0072.bracket1165 BracketBatch0072.bracket1166
  (431810895215029976566629847128570711117/500000000000000000000000000000000000000) (8471479259005133904131222719510961417/500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1165
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1166
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0182.rows BesselBatch0182.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0182.rows BesselBatch0182.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0182.rows BesselBatch0182.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0182.rows BesselBatch0182.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0182.rows BesselBatch0182.accepted ⟨16,by decide⟩
]
theorem leftAccepted : besselPointCheck (2162090399254953238508793501995362738399/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (2162090399254953238508793501995362738399/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0182.rows BesselBatch0182.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0182.rows BesselBatch0182.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0182.rows BesselBatch0182.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0182.rows BesselBatch0182.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0182.rows BesselBatch0182.accepted ⟨31,by decide⟩
]
theorem rightAccepted : besselPointCheck (4336373051304326238792532563061226626091/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (4336373051304326238792532563061226626091/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0580.rows BesselBatch0580.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0580.rows BesselBatch0580.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0580.rows BesselBatch0580.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0580.rows BesselBatch0580.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0580.rows BesselBatch0580.accepted ⟨4,by decide⟩
]
theorem midAccepted : besselPointCheck (8660553849814232715810119567051952102889/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (8660553849814232715810119567051952102889/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0145.rows ScalarLogs0145.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0145.rows ScalarLogs0145.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0145.rows ScalarLogs0145.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0145.rows ScalarLogs0145.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0145.rows ScalarLogs0145.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0145.rows ScalarLogs0145.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0145.rows ScalarLogs0145.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0145.rows ScalarLogs0145.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0145.rows ScalarLogs0145.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0145.rows ScalarLogs0145.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0145.rows ScalarLogs0145.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0145.rows ScalarLogs0145.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0145.rows ScalarLogs0145.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0145.rows ScalarLogs0145.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0145.rows ScalarLogs0145.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0145.rows ScalarLogs0145.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0072.bracket1166 BracketBatch0072.bracket1167 (8660553849814232715810119567051952102889/10000000000000000000000000000000000000000) (170635645765983725741104315133383788241/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0072.bracket1166 BracketBatch0072.bracket1167
  (8660553849814232715810119567051952102889/10000000000000000000000000000000000000000) (170635645765983725741104315133383788241/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1166
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1167
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0182.rows BesselBatch0182.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0182.rows BesselBatch0182.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0182.rows BesselBatch0182.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0182.rows BesselBatch0182.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0182.rows BesselBatch0182.accepted ⟨26,by decide⟩
]
theorem leftAccepted : besselPointCheck (8672746102608652477585065126122453252179/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (8672746102608652477585065126122453252179/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0182.rows BesselBatch0182.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0182.rows BesselBatch0182.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0182.rows BesselBatch0182.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0182.rows BesselBatch0182.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0182.rows BesselBatch0182.accepted ⟨41,by decide⟩
]
theorem rightAccepted : besselPointCheck (8697228564358424690136654216299888208269/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (8697228564358424690136654216299888208269/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0580.rows BesselBatch0580.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0580.rows BesselBatch0580.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0580.rows BesselBatch0580.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0580.rows BesselBatch0580.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0580.rows BesselBatch0580.accepted ⟨9,by decide⟩
]
theorem midAccepted : besselPointCheck (542811708342721161491303729450698170639/625000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (542811708342721161491303729450698170639/625000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0145.rows ScalarLogs0145.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0145.rows ScalarLogs0145.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0145.rows ScalarLogs0145.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0145.rows ScalarLogs0145.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0145.rows ScalarLogs0145.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0145.rows ScalarLogs0145.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0145.rows ScalarLogs0145.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0145.rows ScalarLogs0145.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0145.rows ScalarLogs0145.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0145.rows ScalarLogs0145.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0145.rows ScalarLogs0145.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0145.rows ScalarLogs0145.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0145.rows ScalarLogs0145.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0145.rows ScalarLogs0145.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0145.rows ScalarLogs0145.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0145.rows ScalarLogs0145.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0072.bracket1167 BracketBatch0073.bracket1168 (542811708342721161491303729450698170639/625000000000000000000000000000000000000) (34369864966849748899136241775975565399/2000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0072.bracket1167 BracketBatch0073.bracket1168
  (542811708342721161491303729450698170639/625000000000000000000000000000000000000) (34369864966849748899136241775975565399/2000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1167
