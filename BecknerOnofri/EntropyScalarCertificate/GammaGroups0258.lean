import BecknerOnofri.EntropyScalarCertificate.Bessel0322
import BecknerOnofri.EntropyScalarCertificate.Bessel0323
import BecknerOnofri.EntropyScalarCertificate.Bessel0650
import BecknerOnofri.EntropyScalarCertificate.Brackets0129
import BecknerOnofri.EntropyScalarCertificate.Logs0258
import BecknerOnofri.ScalarElementaryComposition
import BecknerOnofri.ScalarGammaEnclosure
import BecknerOnofri.ScalarLogBesselEndpoints
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2064
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0322.rows BesselBatch0322.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0322.rows BesselBatch0322.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0322.rows BesselBatch0322.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0322.rows BesselBatch0322.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0322.rows BesselBatch0322.accepted ⟨36,by decide⟩
]
theorem leftAccepted : besselPointCheck (61723708061931199452914349197665332039643/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (61723708061931199452914349197665332039643/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0322.rows BesselBatch0322.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0322.rows BesselBatch0322.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0322.rows BesselBatch0322.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0322.rows BesselBatch0322.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0322.rows BesselBatch0322.accepted ⟨51,by decide⟩
]
theorem rightAccepted : besselPointCheck (61869683457954412246104668091919846370301/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (61869683457954412246104668091919846370301/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0650.rows BesselBatch0650.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0650.rows BesselBatch0650.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0650.rows BesselBatch0650.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0650.rows BesselBatch0650.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0650.rows BesselBatch0650.accepted ⟨14,by decide⟩
]
theorem midAccepted : besselPointCheck (15449173939985701462377377161198147301243/2500000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (15449173939985701462377377161198147301243/2500000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0258.rows ScalarLogs0258.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0258.rows ScalarLogs0258.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0258.rows ScalarLogs0258.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0258.rows ScalarLogs0258.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0258.rows ScalarLogs0258.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0258.rows ScalarLogs0258.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0258.rows ScalarLogs0258.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0258.rows ScalarLogs0258.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0258.rows ScalarLogs0258.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0258.rows ScalarLogs0258.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0258.rows ScalarLogs0258.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0258.rows ScalarLogs0258.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0258.rows ScalarLogs0258.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0258.rows ScalarLogs0258.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0258.rows ScalarLogs0258.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0258.rows ScalarLogs0258.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0129.bracket2064 BracketBatch0129.bracket2065 (15449173939985701462377377161198147301243/2500000000000000000000000000000000000000) (133512122286856970003199547343089543711/625000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0129.bracket2064 BracketBatch0129.bracket2065
  (15449173939985701462377377161198147301243/2500000000000000000000000000000000000000) (133512122286856970003199547343089543711/625000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2064
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2065
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0322.rows BesselBatch0322.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0322.rows BesselBatch0322.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0322.rows BesselBatch0322.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0322.rows BesselBatch0322.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0322.rows BesselBatch0322.accepted ⟨46,by decide⟩
]
theorem leftAccepted : besselPointCheck (30934841728977206123052334045959923185149/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (30934841728977206123052334045959923185149/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0322.rows BesselBatch0322.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0322.rows BesselBatch0322.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0322.rows BesselBatch0322.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0322.rows BesselBatch0322.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0322.rows BesselBatch0322.accepted ⟨61,by decide⟩
]
theorem rightAccepted : besselPointCheck (12403273760037972115204327399775937865637/2000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (12403273760037972115204327399775937865637/2000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0650.rows BesselBatch0650.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0650.rows BesselBatch0650.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0650.rows BesselBatch0650.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0650.rows BesselBatch0650.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0650.rows BesselBatch0650.accepted ⟨19,by decide⟩
]
theorem midAccepted : besselPointCheck (123886052258144272822126305090799535698483/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (123886052258144272822126305090799535698483/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0258.rows ScalarLogs0258.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0258.rows ScalarLogs0258.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0258.rows ScalarLogs0258.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0258.rows ScalarLogs0258.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0258.rows ScalarLogs0258.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0258.rows ScalarLogs0258.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0258.rows ScalarLogs0258.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0258.rows ScalarLogs0258.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0258.rows ScalarLogs0258.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0258.rows ScalarLogs0258.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0258.rows ScalarLogs0258.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0258.rows ScalarLogs0258.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0258.rows ScalarLogs0258.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0258.rows ScalarLogs0258.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0258.rows ScalarLogs0258.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0258.rows ScalarLogs0258.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0129.bracket2065 BracketBatch0129.bracket2066 (123886052258144272822126305090799535698483/20000000000000000000000000000000000000000) (213921080469861438588866551690062250561/1000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0129.bracket2065 BracketBatch0129.bracket2066
  (123886052258144272822126305090799535698483/20000000000000000000000000000000000000000) (213921080469861438588866551690062250561/1000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2065
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2066
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0322.rows BesselBatch0322.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0322.rows BesselBatch0322.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0322.rows BesselBatch0322.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0322.rows BesselBatch0322.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0322.rows BesselBatch0322.accepted ⟨56,by decide⟩
]
theorem leftAccepted : besselPointCheck (31008184400094930288010818499439844664091/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (31008184400094930288010818499439844664091/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0323.rows BesselBatch0323.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0323.rows BesselBatch0323.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0323.rows BesselBatch0323.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0323.rows BesselBatch0323.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0323.rows BesselBatch0323.accepted ⟨7,by decide⟩
]
theorem rightAccepted : besselPointCheck (31081884634583923034923202975620178999869/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (31081884634583923034923202975620178999869/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0650.rows BesselBatch0650.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0650.rows BesselBatch0650.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0650.rows BesselBatch0650.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0650.rows BesselBatch0650.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0650.rows BesselBatch0650.accepted ⟨24,by decide⟩
]
theorem midAccepted : besselPointCheck (1552251725866971333073350536876500591599/250000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1552251725866971333073350536876500591599/250000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0258.rows ScalarLogs0258.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0258.rows ScalarLogs0258.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0258.rows ScalarLogs0258.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0258.rows ScalarLogs0258.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0258.rows ScalarLogs0258.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0258.rows ScalarLogs0258.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0258.rows ScalarLogs0258.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0258.rows ScalarLogs0258.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0258.rows ScalarLogs0258.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0258.rows ScalarLogs0258.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0258.rows ScalarLogs0258.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0258.rows ScalarLogs0258.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0258.rows ScalarLogs0258.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0258.rows ScalarLogs0258.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0258.rows ScalarLogs0258.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0258.rows ScalarLogs0258.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0129.bracket2066 BracketBatch0129.bracket2067 (1552251725866971333073350536876500591599/250000000000000000000000000000000000000) (2142235761220396381588338691184448115683/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0129.bracket2066 BracketBatch0129.bracket2067
  (1552251725866971333073350536876500591599/250000000000000000000000000000000000000) (2142235761220396381588338691184448115683/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2066
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2067
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0322.rows BesselBatch0322.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0322.rows BesselBatch0322.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0323.rows BesselBatch0323.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0323.rows BesselBatch0323.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0323.rows BesselBatch0323.accepted ⟨2,by decide⟩
]
theorem leftAccepted : besselPointCheck (12432753853833569213969281190248071599947/2000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (12432753853833569213969281190248071599947/2000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0323.rows BesselBatch0323.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0323.rows BesselBatch0323.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0323.rows BesselBatch0323.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0323.rows BesselBatch0323.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0323.rows BesselBatch0323.accepted ⟨17,by decide⟩
]
theorem rightAccepted : besselPointCheck (31155945047982562220603808045071245238333/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (31155945047982562220603808045071245238333/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0650.rows BesselBatch0650.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0650.rows BesselBatch0650.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0650.rows BesselBatch0650.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0650.rows BesselBatch0650.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0650.rows BesselBatch0650.accepted ⟨29,by decide⟩
]
theorem midAccepted : besselPointCheck (124475659365132970511054022041382848476401/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (124475659365132970511054022041382848476401/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0258.rows ScalarLogs0258.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0258.rows ScalarLogs0258.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0258.rows ScalarLogs0258.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0258.rows ScalarLogs0258.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0258.rows ScalarLogs0258.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0258.rows ScalarLogs0258.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0258.rows ScalarLogs0258.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0258.rows ScalarLogs0258.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0258.rows ScalarLogs0258.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0258.rows ScalarLogs0258.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0258.rows ScalarLogs0258.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0258.rows ScalarLogs0258.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0258.rows ScalarLogs0258.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0258.rows ScalarLogs0258.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0258.rows ScalarLogs0258.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0258.rows ScalarLogs0258.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0129.bracket2067 BracketBatch0129.bracket2068 (124475659365132970511054022041382848476401/20000000000000000000000000000000000000000) (2145268866412963219571829259857152242399/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0129.bracket2067 BracketBatch0129.bracket2068
  (124475659365132970511054022041382848476401/20000000000000000000000000000000000000000) (2145268866412963219571829259857152242399/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2067
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2068
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0323.rows BesselBatch0323.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0323.rows BesselBatch0323.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0323.rows BesselBatch0323.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0323.rows BesselBatch0323.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0323.rows BesselBatch0323.accepted ⟨12,by decide⟩
]
theorem leftAccepted : besselPointCheck (62311890095965124441207616090142490476663/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (62311890095965124441207616090142490476663/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0323.rows BesselBatch0323.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0323.rows BesselBatch0323.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0323.rows BesselBatch0323.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0323.rows BesselBatch0323.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0323.rows BesselBatch0323.accepted ⟨27,by decide⟩
]
theorem rightAccepted : besselPointCheck (6246073656282280356426954473167745710401/1000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (6246073656282280356426954473167745710401/1000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0650.rows BesselBatch0650.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0650.rows BesselBatch0650.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0650.rows BesselBatch0650.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0650.rows BesselBatch0650.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0650.rows BesselBatch0650.accepted ⟨34,by decide⟩
]
theorem midAccepted : besselPointCheck (124772626658787928005477160821819947580673/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (124772626658787928005477160821819947580673/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0258.rows ScalarLogs0258.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0258.rows ScalarLogs0258.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0258.rows ScalarLogs0258.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0258.rows ScalarLogs0258.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0258.rows ScalarLogs0258.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0258.rows ScalarLogs0258.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0258.rows ScalarLogs0258.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0258.rows ScalarLogs0258.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0258.rows ScalarLogs0258.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0258.rows ScalarLogs0258.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0258.rows ScalarLogs0258.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0258.rows ScalarLogs0258.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0258.rows ScalarLogs0258.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0258.rows ScalarLogs0258.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0258.rows ScalarLogs0258.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0258.rows ScalarLogs0258.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0129.bracket2068 BracketBatch0129.bracket2069 (124772626658787928005477160821819947580673/20000000000000000000000000000000000000000) (2148310160836350594180697244549167548409/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0129.bracket2068 BracketBatch0129.bracket2069
  (124772626658787928005477160821819947580673/20000000000000000000000000000000000000000) (2148310160836350594180697244549167548409/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2068
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2069
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0323.rows BesselBatch0323.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0323.rows BesselBatch0323.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0323.rows BesselBatch0323.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0323.rows BesselBatch0323.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0323.rows BesselBatch0323.accepted ⟨22,by decide⟩
]
theorem leftAccepted : besselPointCheck (62460736562822803564269544731677457104007/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (62460736562822803564269544731677457104007/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0323.rows BesselBatch0323.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0323.rows BesselBatch0323.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0323.rows BesselBatch0323.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0323.rows BesselBatch0323.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0323.rows BesselBatch0323.accepted ⟨37,by decide⟩
]
theorem rightAccepted : besselPointCheck (62610314003773328504729791177021422461633/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (62610314003773328504729791177021422461633/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0650.rows BesselBatch0650.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0650.rows BesselBatch0650.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0650.rows BesselBatch0650.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0650.rows BesselBatch0650.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0650.rows BesselBatch0650.accepted ⟨39,by decide⟩
]
theorem midAccepted : besselPointCheck (3126776264164903301724983397717471989141/500000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (3126776264164903301724983397717471989141/500000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0258.rows ScalarLogs0258.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0258.rows ScalarLogs0258.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0258.rows ScalarLogs0258.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0258.rows ScalarLogs0258.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0258.rows ScalarLogs0258.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0258.rows ScalarLogs0258.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0258.rows ScalarLogs0258.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0258.rows ScalarLogs0258.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0258.rows ScalarLogs0258.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0258.rows ScalarLogs0258.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0258.rows ScalarLogs0258.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0258.rows ScalarLogs0258.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0258.rows ScalarLogs0258.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0258.rows ScalarLogs0258.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0258.rows ScalarLogs0258.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0258.rows ScalarLogs0258.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0129.bracket2069 BracketBatch0129.bracket2070 (3126776264164903301724983397717471989141/500000000000000000000000000000000000000) (2151359685355691036308999933654762558603/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0129.bracket2069 BracketBatch0129.bracket2070
  (3126776264164903301724983397717471989141/500000000000000000000000000000000000000) (2151359685355691036308999933654762558603/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2069
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2070
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0323.rows BesselBatch0323.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0323.rows BesselBatch0323.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0323.rows BesselBatch0323.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0323.rows BesselBatch0323.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0323.rows BesselBatch0323.accepted ⟨32,by decide⟩
]
theorem leftAccepted : besselPointCheck (6261031400377332850472979117702142246163/1000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (6261031400377332850472979117702142246163/1000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0323.rows BesselBatch0323.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0323.rows BesselBatch0323.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0323.rows BesselBatch0323.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0323.rows BesselBatch0323.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0323.rows BesselBatch0323.accepted ⟨47,by decide⟩
]
theorem rightAccepted : besselPointCheck (31380313902638354897460956216924919417997/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (31380313902638354897460956216924919417997/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0650.rows BesselBatch0650.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0650.rows BesselBatch0650.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0650.rows BesselBatch0650.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0650.rows BesselBatch0650.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0650.rows BesselBatch0650.accepted ⟨44,by decide⟩
]
theorem midAccepted : besselPointCheck (15671367726131254787456462951358907662203/2500000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (15671367726131254787456462951358907662203/2500000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0258.rows ScalarLogs0258.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0258.rows ScalarLogs0258.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0258.rows ScalarLogs0258.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0258.rows ScalarLogs0258.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0258.rows ScalarLogs0258.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0258.rows ScalarLogs0258.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0258.rows ScalarLogs0258.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0258.rows ScalarLogs0258.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0258.rows ScalarLogs0258.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0258.rows ScalarLogs0258.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0258.rows ScalarLogs0258.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0258.rows ScalarLogs0258.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0258.rows ScalarLogs0258.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0258.rows ScalarLogs0258.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0258.rows ScalarLogs0258.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0258.rows ScalarLogs0258.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0129.bracket2070 BracketBatch0129.bracket2071 (15671367726131254787456462951358907662203/2500000000000000000000000000000000000000) (2154417481144216690021473665546653128557/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0129.bracket2070 BracketBatch0129.bracket2071
  (15671367726131254787456462951358907662203/2500000000000000000000000000000000000000) (2154417481144216690021473665546653128557/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2070
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2071
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0323.rows BesselBatch0323.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0323.rows BesselBatch0323.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0323.rows BesselBatch0323.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0323.rows BesselBatch0323.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0323.rows BesselBatch0323.accepted ⟨42,by decide⟩
]
theorem leftAccepted : besselPointCheck (62760627805276709794921912433849838835991/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (62760627805276709794921912433849838835991/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0323.rows BesselBatch0323.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0323.rows BesselBatch0323.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0323.rows BesselBatch0323.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0323.rows BesselBatch0323.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0323.rows BesselBatch0323.accepted ⟨57,by decide⟩
]
theorem rightAccepted : besselPointCheck (62911683406866154319690842395342282943993/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (62911683406866154319690842395342282943993/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0650.rows BesselBatch0650.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0650.rows BesselBatch0650.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0650.rows BesselBatch0650.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0650.rows BesselBatch0650.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0650.rows BesselBatch0650.accepted ⟨49,by decide⟩
]
theorem midAccepted : besselPointCheck (7854519450758929007163297176824507611249/1250000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (7854519450758929007163297176824507611249/1250000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0258.rows ScalarLogs0258.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0258.rows ScalarLogs0258.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0258.rows ScalarLogs0258.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0258.rows ScalarLogs0258.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0258.rows ScalarLogs0258.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0258.rows ScalarLogs0258.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0258.rows ScalarLogs0258.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0258.rows ScalarLogs0258.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0258.rows ScalarLogs0258.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0258.rows ScalarLogs0258.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0258.rows ScalarLogs0258.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0258.rows ScalarLogs0258.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0258.rows ScalarLogs0258.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0258.rows ScalarLogs0258.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0258.rows ScalarLogs0258.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0258.rows ScalarLogs0258.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0129.bracket2071 BracketBatch0129.bracket2072 (7854519450758929007163297176824507611249/1250000000000000000000000000000000000000) (1078741794843149264048934542665950576497/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0129.bracket2071 BracketBatch0129.bracket2072
  (7854519450758929007163297176824507611249/1250000000000000000000000000000000000000) (1078741794843149264048934542665950576497/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2071
