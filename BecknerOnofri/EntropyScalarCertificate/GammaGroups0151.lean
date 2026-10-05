import BecknerOnofri.EntropyScalarCertificate.Bessel0188
import BecknerOnofri.EntropyScalarCertificate.Bessel0189
import BecknerOnofri.EntropyScalarCertificate.Bessel0190
import BecknerOnofri.EntropyScalarCertificate.Bessel0583
import BecknerOnofri.EntropyScalarCertificate.Brackets0075
import BecknerOnofri.EntropyScalarCertificate.Brackets0076
import BecknerOnofri.EntropyScalarCertificate.Logs0151
import BecknerOnofri.ScalarElementaryComposition
import BecknerOnofri.ScalarGammaEnclosure
import BecknerOnofri.ScalarLogBesselEndpoints
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1208
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0188.rows BesselBatch0188.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0188.rows BesselBatch0188.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0188.rows BesselBatch0188.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0188.rows BesselBatch0188.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0188.rows BesselBatch0188.accepted ⟨52,by decide⟩
]
theorem leftAccepted : besselPointCheck (9767839072354472750535179155816507333103/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (9767839072354472750535179155816507333103/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0188.rows BesselBatch0188.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0189.rows BesselBatch0189.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0189.rows BesselBatch0189.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0189.rows BesselBatch0189.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0189.rows BesselBatch0189.accepted ⟨3,by decide⟩
]
theorem rightAccepted : besselPointCheck (9797201895488519110271212426617975216849/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (9797201895488519110271212426617975216849/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0583.rows BesselBatch0583.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0583.rows BesselBatch0583.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0583.rows BesselBatch0583.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0583.rows BesselBatch0583.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0583.rows BesselBatch0583.accepted ⟨22,by decide⟩
]
theorem midAccepted : besselPointCheck (305703765122546747825099868475538789843/312500000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (305703765122546747825099868475538789843/312500000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0151.rows ScalarLogs0151.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0151.rows ScalarLogs0151.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0151.rows ScalarLogs0151.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0151.rows ScalarLogs0151.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0151.rows ScalarLogs0151.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0151.rows ScalarLogs0151.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0151.rows ScalarLogs0151.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0151.rows ScalarLogs0151.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0151.rows ScalarLogs0151.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0151.rows ScalarLogs0151.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0151.rows ScalarLogs0151.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0151.rows ScalarLogs0151.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0151.rows ScalarLogs0151.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0151.rows ScalarLogs0151.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0151.rows ScalarLogs0151.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0151.rows ScalarLogs0151.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0075.bracket1208 BracketBatch0075.bracket1209 (305703765122546747825099868475538789843/312500000000000000000000000000000000000) (114435338438296816871536925413441347021/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0075.bracket1208 BracketBatch0075.bracket1209
  (305703765122546747825099868475538789843/312500000000000000000000000000000000000) (114435338438296816871536925413441347021/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1208
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1209
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0188.rows BesselBatch0188.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0188.rows BesselBatch0188.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0188.rows BesselBatch0188.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0188.rows BesselBatch0188.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0188.rows BesselBatch0188.accepted ⟨62,by decide⟩
]
theorem leftAccepted : besselPointCheck (4898600947744259555135606213308987608423/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (4898600947744259555135606213308987608423/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0189.rows BesselBatch0189.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0189.rows BesselBatch0189.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0189.rows BesselBatch0189.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0189.rows BesselBatch0189.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0189.rows BesselBatch0189.accepted ⟨13,by decide⟩
]
theorem rightAccepted : besselPointCheck (9826709035785659706408959770729568091297/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (9826709035785659706408959770729568091297/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0583.rows BesselBatch0583.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0583.rows BesselBatch0583.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0583.rows BesselBatch0583.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0583.rows BesselBatch0583.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0583.rows BesselBatch0583.accepted ⟨27,by decide⟩
]
theorem midAccepted : besselPointCheck (19623910931274178816680172197347543308143/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (19623910931274178816680172197347543308143/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0151.rows ScalarLogs0151.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0151.rows ScalarLogs0151.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0151.rows ScalarLogs0151.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0151.rows ScalarLogs0151.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0151.rows ScalarLogs0151.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0151.rows ScalarLogs0151.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0151.rows ScalarLogs0151.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0151.rows ScalarLogs0151.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0151.rows ScalarLogs0151.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0151.rows ScalarLogs0151.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0151.rows ScalarLogs0151.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0151.rows ScalarLogs0151.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0151.rows ScalarLogs0151.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0151.rows ScalarLogs0151.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0151.rows ScalarLogs0151.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0151.rows ScalarLogs0151.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0075.bracket1209 BracketBatch0075.bracket1210 (19623910931274178816680172197347543308143/20000000000000000000000000000000000000000) (1843664332133629273005215295043189683/80000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0075.bracket1209 BracketBatch0075.bracket1210
  (19623910931274178816680172197347543308143/20000000000000000000000000000000000000000) (1843664332133629273005215295043189683/80000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1209
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1210
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0189.rows BesselBatch0189.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0189.rows BesselBatch0189.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0189.rows BesselBatch0189.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0189.rows BesselBatch0189.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0189.rows BesselBatch0189.accepted ⟨8,by decide⟩
]
theorem leftAccepted : besselPointCheck (4913354517892829853204479885364784045647/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (4913354517892829853204479885364784045647/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0189.rows BesselBatch0189.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0189.rows BesselBatch0189.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0189.rows BesselBatch0189.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0189.rows BesselBatch0189.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0189.rows BesselBatch0189.accepted ⟨23,by decide⟩
]
theorem rightAccepted : besselPointCheck (9856361936463390607173856368577200982903/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (9856361936463390607173856368577200982903/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0583.rows BesselBatch0583.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0583.rows BesselBatch0583.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0583.rows BesselBatch0583.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0583.rows BesselBatch0583.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0583.rows BesselBatch0583.accepted ⟨32,by decide⟩
]
theorem midAccepted : besselPointCheck (19683070972249050313582816139306769074197/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (19683070972249050313582816139306769074197/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0151.rows ScalarLogs0151.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0151.rows ScalarLogs0151.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0151.rows ScalarLogs0151.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0151.rows ScalarLogs0151.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0151.rows ScalarLogs0151.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0151.rows ScalarLogs0151.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0151.rows ScalarLogs0151.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0151.rows ScalarLogs0151.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0151.rows ScalarLogs0151.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0151.rows ScalarLogs0151.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0151.rows ScalarLogs0151.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0151.rows ScalarLogs0151.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0151.rows ScalarLogs0151.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0151.rows ScalarLogs0151.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0151.rows ScalarLogs0151.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0151.rows ScalarLogs0151.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0075.bracket1210 BracketBatch0075.bracket1211 (19683070972249050313582816139306769074197/20000000000000000000000000000000000000000) (9282229821419176256494807419638614207/400000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0075.bracket1210 BracketBatch0075.bracket1211
  (19683070972249050313582816139306769074197/20000000000000000000000000000000000000000) (9282229821419176256494807419638614207/400000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1210
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1211
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0189.rows BesselBatch0189.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0189.rows BesselBatch0189.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0189.rows BesselBatch0189.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0189.rows BesselBatch0189.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0189.rows BesselBatch0189.accepted ⟨18,by decide⟩
]
theorem leftAccepted : besselPointCheck (98563619364633906071738563685772009829/100000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (98563619364633906071738563685772009829/100000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0189.rows BesselBatch0189.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0189.rows BesselBatch0189.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0189.rows BesselBatch0189.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0189.rows BesselBatch0189.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0189.rows BesselBatch0189.accepted ⟨33,by decide⟩
]
theorem rightAccepted : besselPointCheck (9886162060657258015239396126947399002267/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (9886162060657258015239396126947399002267/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0583.rows BesselBatch0583.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0583.rows BesselBatch0583.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0583.rows BesselBatch0583.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0583.rows BesselBatch0583.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0583.rows BesselBatch0583.accepted ⟨37,by decide⟩
]
theorem midAccepted : besselPointCheck (19742523997120648622413252495524599985167/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (19742523997120648622413252495524599985167/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0151.rows ScalarLogs0151.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0151.rows ScalarLogs0151.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0151.rows ScalarLogs0151.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0151.rows ScalarLogs0151.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0151.rows ScalarLogs0151.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0151.rows ScalarLogs0151.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0151.rows ScalarLogs0151.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0151.rows ScalarLogs0151.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0151.rows ScalarLogs0151.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0151.rows ScalarLogs0151.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0151.rows ScalarLogs0151.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0151.rows ScalarLogs0151.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0151.rows ScalarLogs0151.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0151.rows ScalarLogs0151.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0151.rows ScalarLogs0151.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0151.rows ScalarLogs0151.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0075.bracket1211 BracketBatch0075.bracket1212 (19742523997120648622413252495524599985167/20000000000000000000000000000000000000000) (23366386755332204594061668228237568683/1000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0075.bracket1211 BracketBatch0075.bracket1212
  (19742523997120648622413252495524599985167/20000000000000000000000000000000000000000) (23366386755332204594061668228237568683/1000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1211
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1212
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0189.rows BesselBatch0189.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0189.rows BesselBatch0189.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0189.rows BesselBatch0189.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0189.rows BesselBatch0189.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0189.rows BesselBatch0189.accepted ⟨28,by decide⟩
]
theorem leftAccepted : besselPointCheck (1235770257582157251904924515868424875283/1250000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1235770257582157251904924515868424875283/1250000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0189.rows BesselBatch0189.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0189.rows BesselBatch0189.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0189.rows BesselBatch0189.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0189.rows BesselBatch0189.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0189.rows BesselBatch0189.accepted ⟨43,by decide⟩
]
theorem rightAccepted : besselPointCheck (4958055445884951280659415011208886132101/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (4958055445884951280659415011208886132101/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0583.rows BesselBatch0583.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0583.rows BesselBatch0583.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0583.rows BesselBatch0583.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0583.rows BesselBatch0583.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0583.rows BesselBatch0583.accepted ⟨42,by decide⟩
]
theorem midAccepted : besselPointCheck (9901136476213580288279113074682585633233/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (9901136476213580288279113074682585633233/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0151.rows ScalarLogs0151.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0151.rows ScalarLogs0151.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0151.rows ScalarLogs0151.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0151.rows ScalarLogs0151.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0151.rows ScalarLogs0151.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0151.rows ScalarLogs0151.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0151.rows ScalarLogs0151.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0151.rows ScalarLogs0151.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0151.rows ScalarLogs0151.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0151.rows ScalarLogs0151.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0151.rows ScalarLogs0151.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0151.rows ScalarLogs0151.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0151.rows ScalarLogs0151.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0151.rows ScalarLogs0151.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0151.rows ScalarLogs0151.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0151.rows ScalarLogs0151.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0075.bracket1212 BracketBatch0075.bracket1213 (9901136476213580288279113074682585633233/10000000000000000000000000000000000000000) (235282487082224193769190141804325993437/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0075.bracket1212 BracketBatch0075.bracket1213
  (9901136476213580288279113074682585633233/10000000000000000000000000000000000000000) (235282487082224193769190141804325993437/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1212
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1213
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0189.rows BesselBatch0189.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0189.rows BesselBatch0189.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0189.rows BesselBatch0189.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0189.rows BesselBatch0189.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0189.rows BesselBatch0189.accepted ⟨38,by decide⟩
]
theorem leftAccepted : besselPointCheck (9916110891769902561318830022417772264199/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (9916110891769902561318830022417772264199/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0189.rows BesselBatch0189.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0189.rows BesselBatch0189.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0189.rows BesselBatch0189.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0189.rows BesselBatch0189.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0189.rows BesselBatch0189.accepted ⟨53,by decide⟩
]
theorem rightAccepted : besselPointCheck (1989241986765485281070818224289193961317/2000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1989241986765485281070818224289193961317/2000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0583.rows BesselBatch0583.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0583.rows BesselBatch0583.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0583.rows BesselBatch0583.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0583.rows BesselBatch0583.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0583.rows BesselBatch0583.accepted ⟨47,by decide⟩
]
theorem midAccepted : besselPointCheck (606149927538980986531766392329826113/610351562500000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (606149927538980986531766392329826113/610351562500000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0151.rows ScalarLogs0151.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0151.rows ScalarLogs0151.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0151.rows ScalarLogs0151.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0151.rows ScalarLogs0151.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0151.rows ScalarLogs0151.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0151.rows ScalarLogs0151.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0151.rows ScalarLogs0151.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0151.rows ScalarLogs0151.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0151.rows ScalarLogs0151.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0151.rows ScalarLogs0151.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0151.rows ScalarLogs0151.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0151.rows ScalarLogs0151.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0151.rows ScalarLogs0151.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0151.rows ScalarLogs0151.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0151.rows ScalarLogs0151.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0151.rows ScalarLogs0151.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0075.bracket1213 BracketBatch0075.bracket1214 (606149927538980986531766392329826113/610351562500000000000000000000000000) (118455842270040695342198211151567039643/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0075.bracket1213 BracketBatch0075.bracket1214
  (606149927538980986531766392329826113/610351562500000000000000000000000000) (118455842270040695342198211151567039643/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1213
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1214
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0189.rows BesselBatch0189.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0189.rows BesselBatch0189.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0189.rows BesselBatch0189.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0189.rows BesselBatch0189.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0189.rows BesselBatch0189.accepted ⟨48,by decide⟩
]
theorem leftAccepted : besselPointCheck (4973104966913713202677045560722984903291/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (4973104966913713202677045560722984903291/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0189.rows BesselBatch0189.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0189.rows BesselBatch0189.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0189.rows BesselBatch0189.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0189.rows BesselBatch0189.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0189.rows BesselBatch0189.accepted ⟨63,by decide⟩
]
theorem rightAccepted : besselPointCheck (249411517796081514448530667697381752777/250000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (249411517796081514448530667697381752777/250000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0583.rows BesselBatch0583.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0583.rows BesselBatch0583.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0583.rows BesselBatch0583.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0583.rows BesselBatch0583.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0583.rows BesselBatch0583.accepted ⟨52,by decide⟩
]
theorem midAccepted : besselPointCheck (9961335322835343491647658914670619958831/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (9961335322835343491647658914670619958831/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0151.rows ScalarLogs0151.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0151.rows ScalarLogs0151.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0151.rows ScalarLogs0151.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0151.rows ScalarLogs0151.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0151.rows ScalarLogs0151.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0151.rows ScalarLogs0151.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0151.rows ScalarLogs0151.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0151.rows ScalarLogs0151.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0151.rows ScalarLogs0151.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0151.rows ScalarLogs0151.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0151.rows ScalarLogs0151.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0151.rows ScalarLogs0151.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0151.rows ScalarLogs0151.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0151.rows ScalarLogs0151.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0151.rows ScalarLogs0151.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0151.rows ScalarLogs0151.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0075.bracket1214 BracketBatch0075.bracket1215 (9961335322835343491647658914670619958831/10000000000000000000000000000000000000000) (238551541265280583961452908436989237461/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0075.bracket1214 BracketBatch0075.bracket1215
  (9961335322835343491647658914670619958831/10000000000000000000000000000000000000000) (238551541265280583961452908436989237461/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1214
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1215
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0189.rows BesselBatch0189.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0189.rows BesselBatch0189.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0189.rows BesselBatch0189.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0189.rows BesselBatch0189.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0189.rows BesselBatch0189.accepted ⟨58,by decide⟩
]
theorem leftAccepted : besselPointCheck (9976460711843260577941226707895270111077/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (9976460711843260577941226707895270111077/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0190.rows BesselBatch0190.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0190.rows BesselBatch0190.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0190.rows BesselBatch0190.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0190.rows BesselBatch0190.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0190.rows BesselBatch0190.accepted ⟨9,by decide⟩
]
theorem rightAccepted : besselPointCheck (1000686477218971483374976700640704307879/1000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1000686477218971483374976700640704307879/1000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0583.rows BesselBatch0583.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0583.rows BesselBatch0583.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0583.rows BesselBatch0583.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0583.rows BesselBatch0583.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0583.rows BesselBatch0583.accepted ⟨57,by decide⟩
]
theorem midAccepted : besselPointCheck (19983325484032975411690993714302313189867/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (19983325484032975411690993714302313189867/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0151.rows ScalarLogs0151.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0151.rows ScalarLogs0151.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0151.rows ScalarLogs0151.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0151.rows ScalarLogs0151.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0151.rows ScalarLogs0151.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0151.rows ScalarLogs0151.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0151.rows ScalarLogs0151.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0151.rows ScalarLogs0151.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0151.rows ScalarLogs0151.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0151.rows ScalarLogs0151.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0151.rows ScalarLogs0151.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0151.rows ScalarLogs0151.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0151.rows ScalarLogs0151.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0151.rows ScalarLogs0151.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0151.rows ScalarLogs0151.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0151.rows ScalarLogs0151.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0075.bracket1215 BracketBatch0076.bracket1216 (19983325484032975411690993714302313189867/20000000000000000000000000000000000000000) (120101069765785794920099469761180585299/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0075.bracket1215 BracketBatch0076.bracket1216
  (19983325484032975411690993714302313189867/20000000000000000000000000000000000000000) (120101069765785794920099469761180585299/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1215
