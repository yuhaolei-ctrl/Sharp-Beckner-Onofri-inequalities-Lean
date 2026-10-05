import BecknerOnofri.EntropyScalarCertificate.Bessel0285
import BecknerOnofri.EntropyScalarCertificate.Bessel0286
import BecknerOnofri.EntropyScalarCertificate.Bessel0631
import BecknerOnofri.EntropyScalarCertificate.Bessel0632
import BecknerOnofri.EntropyScalarCertificate.Brackets0114
import BecknerOnofri.EntropyScalarCertificate.Logs0228
import BecknerOnofri.ScalarElementaryComposition
import BecknerOnofri.ScalarGammaEnclosure
import BecknerOnofri.ScalarLogBesselEndpoints
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1824
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0285.rows BesselBatch0285.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0285.rows BesselBatch0285.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0285.rows BesselBatch0285.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0285.rows BesselBatch0285.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0285.rows BesselBatch0285.accepted ⟨4,by decide⟩
]
theorem leftAccepted : besselPointCheck (862820818386127190057889566701231289899/400000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (862820818386127190057889566701231289899/400000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0285.rows BesselBatch0285.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0285.rows BesselBatch0285.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0285.rows BesselBatch0285.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0285.rows BesselBatch0285.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0285.rows BesselBatch0285.accepted ⟨19,by decide⟩
]
theorem rightAccepted : besselPointCheck (21585991692561846348056722434396557244623/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (21585991692561846348056722434396557244623/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0631.rows BesselBatch0631.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0631.rows BesselBatch0631.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0631.rows BesselBatch0631.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0631.rows BesselBatch0631.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0631.rows BesselBatch0631.accepted ⟨30,by decide⟩
]
theorem midAccepted : besselPointCheck (21578256076107513049751980800963669746049/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (21578256076107513049751980800963669746049/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0228.rows ScalarLogs0228.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0228.rows ScalarLogs0228.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0228.rows ScalarLogs0228.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0228.rows ScalarLogs0228.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0228.rows ScalarLogs0228.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0228.rows ScalarLogs0228.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0228.rows ScalarLogs0228.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0228.rows ScalarLogs0228.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0228.rows ScalarLogs0228.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0228.rows ScalarLogs0228.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0228.rows ScalarLogs0228.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0228.rows ScalarLogs0228.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0228.rows ScalarLogs0228.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0228.rows ScalarLogs0228.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0228.rows ScalarLogs0228.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0228.rows ScalarLogs0228.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0114.bracket1824 BracketBatch0114.bracket1825 (21578256076107513049751980800963669746049/10000000000000000000000000000000000000000) (176021548848348477943694132263001359839/2000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0114.bracket1824 BracketBatch0114.bracket1825
  (21578256076107513049751980800963669746049/10000000000000000000000000000000000000000) (176021548848348477943694132263001359839/2000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1824
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1825
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0285.rows BesselBatch0285.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0285.rows BesselBatch0285.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0285.rows BesselBatch0285.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0285.rows BesselBatch0285.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0285.rows BesselBatch0285.accepted ⟨14,by decide⟩
]
theorem leftAccepted : besselPointCheck (1079299584628092317402836121719827862231/500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1079299584628092317402836121719827862231/500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0285.rows BesselBatch0285.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0285.rows BesselBatch0285.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0285.rows BesselBatch0285.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0285.rows BesselBatch0285.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0285.rows BesselBatch0285.accepted ⟨29,by decide⟩
]
theorem rightAccepted : besselPointCheck (4320297645747773072087941868526872323777/2000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (4320297645747773072087941868526872323777/2000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0631.rows BesselBatch0631.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0631.rows BesselBatch0631.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0631.rows BesselBatch0631.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0631.rows BesselBatch0631.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0631.rows BesselBatch0631.accepted ⟨35,by decide⟩
]
theorem midAccepted : besselPointCheck (8637495984260142341699286355406183772701/4000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (8637495984260142341699286355406183772701/4000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0228.rows ScalarLogs0228.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0228.rows ScalarLogs0228.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0228.rows ScalarLogs0228.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0228.rows ScalarLogs0228.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0228.rows ScalarLogs0228.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0228.rows ScalarLogs0228.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0228.rows ScalarLogs0228.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0228.rows ScalarLogs0228.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0228.rows ScalarLogs0228.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0228.rows ScalarLogs0228.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0228.rows ScalarLogs0228.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0228.rows ScalarLogs0228.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0228.rows ScalarLogs0228.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0228.rows ScalarLogs0228.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0228.rows ScalarLogs0228.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0228.rows ScalarLogs0228.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0114.bracket1825 BracketBatch0114.bracket1826 (8637495984260142341699286355406183772701/4000000000000000000000000000000000000000) (22021649730147245301417189470410612877/250000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0114.bracket1825 BracketBatch0114.bracket1826
  (8637495984260142341699286355406183772701/4000000000000000000000000000000000000000) (22021649730147245301417189470410612877/250000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1825
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1826
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0285.rows BesselBatch0285.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0285.rows BesselBatch0285.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0285.rows BesselBatch0285.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0285.rows BesselBatch0285.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0285.rows BesselBatch0285.accepted ⟨24,by decide⟩
]
theorem leftAccepted : besselPointCheck (10800744114369432680219854671317180809441/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (10800744114369432680219854671317180809441/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0285.rows BesselBatch0285.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0285.rows BesselBatch0285.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0285.rows BesselBatch0285.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0285.rows BesselBatch0285.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0285.rows BesselBatch0285.accepted ⟨39,by decide⟩
]
theorem rightAccepted : besselPointCheck (5404252532683046210711641862250533689683/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (5404252532683046210711641862250533689683/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0631.rows BesselBatch0631.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0631.rows BesselBatch0631.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0631.rows BesselBatch0631.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0631.rows BesselBatch0631.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0631.rows BesselBatch0631.accepted ⟨40,by decide⟩
]
theorem midAccepted : besselPointCheck (21609249179735525101643138395818248188807/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (21609249179735525101643138395818248188807/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0228.rows ScalarLogs0228.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0228.rows ScalarLogs0228.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0228.rows ScalarLogs0228.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0228.rows ScalarLogs0228.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0228.rows ScalarLogs0228.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0228.rows ScalarLogs0228.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0228.rows ScalarLogs0228.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0228.rows ScalarLogs0228.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0228.rows ScalarLogs0228.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0228.rows ScalarLogs0228.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0228.rows ScalarLogs0228.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0228.rows ScalarLogs0228.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0228.rows ScalarLogs0228.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0228.rows ScalarLogs0228.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0228.rows ScalarLogs0228.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0228.rows ScalarLogs0228.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0114.bracket1826 BracketBatch0114.bracket1827 (21609249179735525101643138395818248188807/10000000000000000000000000000000000000000) (881625151136693992092082133833063674553/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0114.bracket1826 BracketBatch0114.bracket1827
  (21609249179735525101643138395818248188807/10000000000000000000000000000000000000000) (881625151136693992092082133833063674553/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1826
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1827
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0285.rows BesselBatch0285.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0285.rows BesselBatch0285.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0285.rows BesselBatch0285.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0285.rows BesselBatch0285.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0285.rows BesselBatch0285.accepted ⟨34,by decide⟩
]
theorem leftAccepted : besselPointCheck (21617010130732184842846567449002134758729/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (21617010130732184842846567449002134758729/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0285.rows BesselBatch0285.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0285.rows BesselBatch0285.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0285.rows BesselBatch0285.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0285.rows BesselBatch0285.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0285.rows BesselBatch0285.accepted ⟨49,by decide⟩
]
theorem rightAccepted : besselPointCheck (10816278730643276501033006834597660567083/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (10816278730643276501033006834597660567083/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0631.rows BesselBatch0631.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0631.rows BesselBatch0631.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0631.rows BesselBatch0631.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0631.rows BesselBatch0631.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0631.rows BesselBatch0631.accepted ⟨45,by decide⟩
]
theorem midAccepted : besselPointCheck (8649913518403747568982516223639491178579/4000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (8649913518403747568982516223639491178579/4000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0228.rows ScalarLogs0228.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0228.rows ScalarLogs0228.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0228.rows ScalarLogs0228.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0228.rows ScalarLogs0228.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0228.rows ScalarLogs0228.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0228.rows ScalarLogs0228.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0228.rows ScalarLogs0228.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0228.rows ScalarLogs0228.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0228.rows ScalarLogs0228.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0228.rows ScalarLogs0228.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0228.rows ScalarLogs0228.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0228.rows ScalarLogs0228.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0228.rows ScalarLogs0228.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0228.rows ScalarLogs0228.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0228.rows ScalarLogs0228.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0228.rows ScalarLogs0228.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0114.bracket1827 BracketBatch0114.bracket1828 (8649913518403747568982516223639491178579/4000000000000000000000000000000000000000) (441192615788679652367186018417827220463/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0114.bracket1827 BracketBatch0114.bracket1828
  (8649913518403747568982516223639491178579/4000000000000000000000000000000000000000) (441192615788679652367186018417827220463/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1827
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1828
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0285.rows BesselBatch0285.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0285.rows BesselBatch0285.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0285.rows BesselBatch0285.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0285.rows BesselBatch0285.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0285.rows BesselBatch0285.accepted ⟨44,by decide⟩
]
theorem leftAccepted : besselPointCheck (21632557461286553002066013669195321134163/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (21632557461286553002066013669195321134163/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0285.rows BesselBatch0285.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0285.rows BesselBatch0285.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0285.rows BesselBatch0285.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0285.rows BesselBatch0285.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0285.rows BesselBatch0285.accepted ⟨59,by decide⟩
]
theorem rightAccepted : besselPointCheck (5427669438103177206193424025148086941761/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (5427669438103177206193424025148086941761/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0631.rows BesselBatch0631.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0631.rows BesselBatch0631.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0631.rows BesselBatch0631.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0631.rows BesselBatch0631.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0631.rows BesselBatch0631.accepted ⟨50,by decide⟩
]
theorem midAccepted : besselPointCheck (43343235213699261826839709769787668901207/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (43343235213699261826839709769787668901207/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0228.rows ScalarLogs0228.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0228.rows ScalarLogs0228.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0228.rows ScalarLogs0228.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0228.rows ScalarLogs0228.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0228.rows ScalarLogs0228.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0228.rows ScalarLogs0228.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0228.rows ScalarLogs0228.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0228.rows ScalarLogs0228.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0228.rows ScalarLogs0228.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0228.rows ScalarLogs0228.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0228.rows ScalarLogs0228.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0228.rows ScalarLogs0228.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0228.rows ScalarLogs0228.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0228.rows ScalarLogs0228.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0228.rows ScalarLogs0228.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0228.rows ScalarLogs0228.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0114.bracket1828 BracketBatch0114.bracket1829 (43343235213699261826839709769787668901207/20000000000000000000000000000000000000000) (220104960828490918920185302159480334241/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0114.bracket1828 BracketBatch0114.bracket1829
  (43343235213699261826839709769787668901207/20000000000000000000000000000000000000000) (220104960828490918920185302159480334241/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1828
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1829
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0285.rows BesselBatch0285.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0285.rows BesselBatch0285.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0285.rows BesselBatch0285.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0285.rows BesselBatch0285.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0285.rows BesselBatch0285.accepted ⟨54,by decide⟩
]
theorem leftAccepted : besselPointCheck (21710677752412708824773696100592347767041/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (21710677752412708824773696100592347767041/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0286.rows BesselBatch0286.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0286.rows BesselBatch0286.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0286.rows BesselBatch0286.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0286.rows BesselBatch0286.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0286.rows BesselBatch0286.accepted ⟨5,by decide⟩
]
theorem rightAccepted : besselPointCheck (5447360820945559291004101079811790719223/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (5447360820945559291004101079811790719223/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0631.rows BesselBatch0631.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0631.rows BesselBatch0631.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0631.rows BesselBatch0631.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0631.rows BesselBatch0631.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0631.rows BesselBatch0631.accepted ⟨55,by decide⟩
]
theorem midAccepted : besselPointCheck (43500121036194945988790100419839510643933/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (43500121036194945988790100419839510643933/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0228.rows ScalarLogs0228.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0228.rows ScalarLogs0228.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0228.rows ScalarLogs0228.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0228.rows ScalarLogs0228.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0228.rows ScalarLogs0228.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0228.rows ScalarLogs0228.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0228.rows ScalarLogs0228.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0228.rows ScalarLogs0228.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0228.rows ScalarLogs0228.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0228.rows ScalarLogs0228.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0228.rows ScalarLogs0228.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0228.rows ScalarLogs0228.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0228.rows ScalarLogs0228.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0228.rows ScalarLogs0228.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0228.rows ScalarLogs0228.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0228.rows ScalarLogs0228.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0114.bracket1829 BracketBatch0114.bracket1830 (43500121036194945988790100419839510643933/20000000000000000000000000000000000000000) (884219232649927696777401105689881017513/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0114.bracket1829 BracketBatch0114.bracket1830
  (43500121036194945988790100419839510643933/20000000000000000000000000000000000000000) (884219232649927696777401105689881017513/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1829
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1830
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0285.rows BesselBatch0285.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0285.rows BesselBatch0285.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0285.rows BesselBatch0285.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0285.rows BesselBatch0285.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0286.rows BesselBatch0286.accepted ⟨0,by decide⟩
]
theorem leftAccepted : besselPointCheck (21789443283782237164016404319247162876889/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (21789443283782237164016404319247162876889/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0286.rows BesselBatch0286.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0286.rows BesselBatch0286.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0286.rows BesselBatch0286.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0286.rows BesselBatch0286.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0286.rows BesselBatch0286.accepted ⟨15,by decide⟩
]
theorem rightAccepted : besselPointCheck (5467215531132949586721932183662842304207/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (5467215531132949586721932183662842304207/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0631.rows BesselBatch0631.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0631.rows BesselBatch0631.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0631.rows BesselBatch0631.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0631.rows BesselBatch0631.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0631.rows BesselBatch0631.accepted ⟨60,by decide⟩
]
theorem midAccepted : besselPointCheck (43658305408314035510904133053898532093717/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (43658305408314035510904133053898532093717/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0228.rows ScalarLogs0228.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0228.rows ScalarLogs0228.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0228.rows ScalarLogs0228.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0228.rows ScalarLogs0228.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0228.rows ScalarLogs0228.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0228.rows ScalarLogs0228.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0228.rows ScalarLogs0228.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0228.rows ScalarLogs0228.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0228.rows ScalarLogs0228.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0228.rows ScalarLogs0228.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0228.rows ScalarLogs0228.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0228.rows ScalarLogs0228.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0228.rows ScalarLogs0228.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0228.rows ScalarLogs0228.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0228.rows ScalarLogs0228.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0228.rows ScalarLogs0228.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0114.bracket1830 BracketBatch0114.bracket1831 (43658305408314035510904133053898532093717/20000000000000000000000000000000000000000) (222010427869007691474118252400917446867/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0114.bracket1830 BracketBatch0114.bracket1831
  (43658305408314035510904133053898532093717/20000000000000000000000000000000000000000) (222010427869007691474118252400917446867/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1830
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1831
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0286.rows BesselBatch0286.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0286.rows BesselBatch0286.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0286.rows BesselBatch0286.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0286.rows BesselBatch0286.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0286.rows BesselBatch0286.accepted ⟨10,by decide⟩
]
theorem leftAccepted : besselPointCheck (874754484981271933875509149386054768673/400000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (874754484981271933875509149386054768673/400000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0286.rows BesselBatch0286.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0286.rows BesselBatch0286.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0286.rows BesselBatch0286.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0286.rows BesselBatch0286.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0286.rows BesselBatch0286.accepted ⟨25,by decide⟩
]
theorem rightAccepted : besselPointCheck (5487235618169977196149254542466355602213/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (5487235618169977196149254542466355602213/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0631.rows BesselBatch0631.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0631.rows BesselBatch0631.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0631.rows BesselBatch0631.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0632.rows BesselBatch0632.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0632.rows BesselBatch0632.accepted ⟨1,by decide⟩
]
theorem midAccepted : besselPointCheck (43817804597211707131484746904516791625677/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (43817804597211707131484746904516791625677/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0228.rows ScalarLogs0228.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0228.rows ScalarLogs0228.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0228.rows ScalarLogs0228.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0228.rows ScalarLogs0228.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0228.rows ScalarLogs0228.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0228.rows ScalarLogs0228.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0228.rows ScalarLogs0228.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0228.rows ScalarLogs0228.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0228.rows ScalarLogs0228.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0228.rows ScalarLogs0228.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0228.rows ScalarLogs0228.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0228.rows ScalarLogs0228.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0228.rows ScalarLogs0228.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0228.rows ScalarLogs0228.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0228.rows ScalarLogs0228.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0228.rows ScalarLogs0228.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0114.bracket1831 BracketBatch0114.bracket1832 (43817804597211707131484746904516791625677/20000000000000000000000000000000000000000) (445943737464785246680355079700267284957/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0114.bracket1831 BracketBatch0114.bracket1832
  (43817804597211707131484746904516791625677/20000000000000000000000000000000000000000) (445943737464785246680355079700267284957/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1831
