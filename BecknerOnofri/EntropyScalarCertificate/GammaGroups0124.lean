import BecknerOnofri.EntropyScalarCertificate.Bessel0155
import BecknerOnofri.EntropyScalarCertificate.Bessel0156
import BecknerOnofri.EntropyScalarCertificate.Bessel0566
import BecknerOnofri.EntropyScalarCertificate.Bessel0567
import BecknerOnofri.EntropyScalarCertificate.Brackets0062
import BecknerOnofri.EntropyScalarCertificate.Logs0124
import BecknerOnofri.ScalarElementaryComposition
import BecknerOnofri.ScalarGammaEnclosure
import BecknerOnofri.ScalarLogBesselEndpoints
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0992
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0155.rows BesselBatch0155.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0155.rows BesselBatch0155.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0155.rows BesselBatch0155.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0155.rows BesselBatch0155.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0155.rows BesselBatch0155.accepted ⟨4,by decide⟩
]
theorem leftAccepted : besselPointCheck (674963625460216992152767822829716750491/1250000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (674963625460216992152767822829716750491/1250000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0155.rows BesselBatch0155.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0155.rows BesselBatch0155.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0155.rows BesselBatch0155.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0155.rows BesselBatch0155.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0155.rows BesselBatch0155.accepted ⟨19,by decide⟩
]
theorem rightAccepted : besselPointCheck (5414586492493893499336840993913415066957/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (5414586492493893499336840993913415066957/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0566.rows BesselBatch0566.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0566.rows BesselBatch0566.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0566.rows BesselBatch0566.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0566.rows BesselBatch0566.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0566.rows BesselBatch0566.accepted ⟨30,by decide⟩
]
theorem midAccepted : besselPointCheck (2162859099235125887311796715310229814177/4000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (2162859099235125887311796715310229814177/4000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0124.rows ScalarLogs0124.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0124.rows ScalarLogs0124.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0124.rows ScalarLogs0124.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0124.rows ScalarLogs0124.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0124.rows ScalarLogs0124.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0124.rows ScalarLogs0124.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0124.rows ScalarLogs0124.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0124.rows ScalarLogs0124.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0124.rows ScalarLogs0124.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0124.rows ScalarLogs0124.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0124.rows ScalarLogs0124.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0124.rows ScalarLogs0124.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0124.rows ScalarLogs0124.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0124.rows ScalarLogs0124.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0124.rows ScalarLogs0124.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0124.rows ScalarLogs0124.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0062.bracket0992 BracketBatch0062.bracket0993 (2162859099235125887311796715310229814177/4000000000000000000000000000000000000000) (21730293394086986724812549039147833043/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0062.bracket0992 BracketBatch0062.bracket0993
  (2162859099235125887311796715310229814177/4000000000000000000000000000000000000000) (21730293394086986724812549039147833043/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0992
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0993
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0155.rows BesselBatch0155.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0155.rows BesselBatch0155.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0155.rows BesselBatch0155.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0155.rows BesselBatch0155.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0155.rows BesselBatch0155.accepted ⟨14,by decide⟩
]
theorem leftAccepted : besselPointCheck (2707293246246946749668420496956707533477/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (2707293246246946749668420496956707533477/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0155.rows BesselBatch0155.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0155.rows BesselBatch0155.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0155.rows BesselBatch0155.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0155.rows BesselBatch0155.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0155.rows BesselBatch0155.accepted ⟨29,by decide⟩
]
theorem rightAccepted : besselPointCheck (542949356789395311481243618345126158937/1000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (542949356789395311481243618345126158937/1000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0566.rows BesselBatch0566.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0566.rows BesselBatch0566.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0566.rows BesselBatch0566.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0566.rows BesselBatch0566.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0566.rows BesselBatch0566.accepted ⟨35,by decide⟩
]
theorem midAccepted : besselPointCheck (2711020015096961653537319294341169164081/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (2711020015096961653537319294341169164081/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0124.rows ScalarLogs0124.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0124.rows ScalarLogs0124.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0124.rows ScalarLogs0124.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0124.rows ScalarLogs0124.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0124.rows ScalarLogs0124.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0124.rows ScalarLogs0124.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0124.rows ScalarLogs0124.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0124.rows ScalarLogs0124.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0124.rows ScalarLogs0124.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0124.rows ScalarLogs0124.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0124.rows ScalarLogs0124.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0124.rows ScalarLogs0124.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0124.rows ScalarLogs0124.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0124.rows ScalarLogs0124.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0124.rows ScalarLogs0124.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0124.rows ScalarLogs0124.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0062.bracket0993 BracketBatch0062.bracket0994 (2711020015096961653537319294341169164081/5000000000000000000000000000000000000000) (43849950701085661271024914883892531221/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0062.bracket0993 BracketBatch0062.bracket0994
  (2711020015096961653537319294341169164081/5000000000000000000000000000000000000000) (43849950701085661271024914883892531221/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0993
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0994
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0155.rows BesselBatch0155.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0155.rows BesselBatch0155.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0155.rows BesselBatch0155.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0155.rows BesselBatch0155.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0155.rows BesselBatch0155.accepted ⟨24,by decide⟩
]
theorem leftAccepted : besselPointCheck (5429493567893953114812436183451261589367/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (5429493567893953114812436183451261589367/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0155.rows BesselBatch0155.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0155.rows BesselBatch0155.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0155.rows BesselBatch0155.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0155.rows BesselBatch0155.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0155.rows BesselBatch0155.accepted ⟨39,by decide⟩
]
theorem rightAccepted : besselPointCheck (17013844998432582131301889499533663967/31250000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (17013844998432582131301889499533663967/31250000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0566.rows BesselBatch0566.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0566.rows BesselBatch0566.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0566.rows BesselBatch0566.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0566.rows BesselBatch0566.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0566.rows BesselBatch0566.accepted ⟨40,by decide⟩
]
theorem midAccepted : besselPointCheck (10873923967392379396829040823302034058807/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (10873923967392379396829040823302034058807/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0124.rows ScalarLogs0124.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0124.rows ScalarLogs0124.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0124.rows ScalarLogs0124.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0124.rows ScalarLogs0124.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0124.rows ScalarLogs0124.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0124.rows ScalarLogs0124.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0124.rows ScalarLogs0124.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0124.rows ScalarLogs0124.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0124.rows ScalarLogs0124.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0124.rows ScalarLogs0124.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0124.rows ScalarLogs0124.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0124.rows ScalarLogs0124.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0124.rows ScalarLogs0124.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0124.rows ScalarLogs0124.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0124.rows ScalarLogs0124.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0124.rows ScalarLogs0124.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0062.bracket0994 BracketBatch0062.bracket0995 (10873923967392379396829040823302034058807/20000000000000000000000000000000000000000) (44242091052065527545269793182614002977/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0062.bracket0994 BracketBatch0062.bracket0995
  (10873923967392379396829040823302034058807/20000000000000000000000000000000000000000) (44242091052065527545269793182614002977/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0994
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0995
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0155.rows BesselBatch0155.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0155.rows BesselBatch0155.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0155.rows BesselBatch0155.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0155.rows BesselBatch0155.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0155.rows BesselBatch0155.accepted ⟨34,by decide⟩
]
theorem leftAccepted : besselPointCheck (5444430399498426282016604639850772469437/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (5444430399498426282016604639850772469437/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0155.rows BesselBatch0155.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0155.rows BesselBatch0155.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0155.rows BesselBatch0155.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0155.rows BesselBatch0155.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0155.rows BesselBatch0155.accepted ⟨49,by decide⟩
]
theorem rightAccepted : besselPointCheck (5459397158155687874886044498513119646529/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (5459397158155687874886044498513119646529/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0566.rows BesselBatch0566.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0566.rows BesselBatch0566.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0566.rows BesselBatch0566.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0566.rows BesselBatch0566.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0566.rows BesselBatch0566.accepted ⟨45,by decide⟩
]
theorem midAccepted : besselPointCheck (5451913778827057078451324569181946057983/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (5451913778827057078451324569181946057983/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0124.rows ScalarLogs0124.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0124.rows ScalarLogs0124.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0124.rows ScalarLogs0124.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0124.rows ScalarLogs0124.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0124.rows ScalarLogs0124.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0124.rows ScalarLogs0124.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0124.rows ScalarLogs0124.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0124.rows ScalarLogs0124.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0124.rows ScalarLogs0124.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0124.rows ScalarLogs0124.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0124.rows ScalarLogs0124.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0124.rows ScalarLogs0124.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0124.rows ScalarLogs0124.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0124.rows ScalarLogs0124.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0124.rows ScalarLogs0124.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0124.rows ScalarLogs0124.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0062.bracket0995 BracketBatch0062.bracket0996 (5451913778827057078451324569181946057983/10000000000000000000000000000000000000000) (22318511798425975098843867787782582863/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0062.bracket0995 BracketBatch0062.bracket0996
  (5451913778827057078451324569181946057983/10000000000000000000000000000000000000000) (22318511798425975098843867787782582863/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0995
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0996
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0155.rows BesselBatch0155.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0155.rows BesselBatch0155.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0155.rows BesselBatch0155.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0155.rows BesselBatch0155.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0155.rows BesselBatch0155.accepted ⟨44,by decide⟩
]
theorem leftAccepted : besselPointCheck (2729698579077843937443022249256559823263/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (2729698579077843937443022249256559823263/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0155.rows BesselBatch0155.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0155.rows BesselBatch0155.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0155.rows BesselBatch0155.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0155.rows BesselBatch0155.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0155.rows BesselBatch0155.accepted ⟨59,by decide⟩
]
theorem rightAccepted : besselPointCheck (54743940159580784404185345444452971431/100000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (54743940159580784404185345444452971431/100000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0566.rows BesselBatch0566.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0566.rows BesselBatch0566.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0566.rows BesselBatch0566.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0566.rows BesselBatch0566.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0566.rows BesselBatch0566.accepted ⟨50,by decide⟩
]
theorem midAccepted : besselPointCheck (5466895587056883157652289521479208394813/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (5466895587056883157652289521479208394813/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0124.rows ScalarLogs0124.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0124.rows ScalarLogs0124.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0124.rows ScalarLogs0124.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0124.rows ScalarLogs0124.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0124.rows ScalarLogs0124.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0124.rows ScalarLogs0124.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0124.rows ScalarLogs0124.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0124.rows ScalarLogs0124.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0124.rows ScalarLogs0124.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0124.rows ScalarLogs0124.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0124.rows ScalarLogs0124.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0124.rows ScalarLogs0124.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0124.rows ScalarLogs0124.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0124.rows ScalarLogs0124.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0124.rows ScalarLogs0124.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0124.rows ScalarLogs0124.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0062.bracket0996 BracketBatch0062.bracket0997 (5466895587056883157652289521479208394813/10000000000000000000000000000000000000000) (45034764173772406448907458214857715699/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0062.bracket0996 BracketBatch0062.bracket0997
  (5466895587056883157652289521479208394813/10000000000000000000000000000000000000000) (45034764173772406448907458214857715699/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0996
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0997
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0155.rows BesselBatch0155.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0155.rows BesselBatch0155.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0155.rows BesselBatch0155.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0155.rows BesselBatch0155.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0155.rows BesselBatch0155.accepted ⟨54,by decide⟩
]
theorem leftAccepted : besselPointCheck (5474394015958078440418534544445297143097/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (5474394015958078440418534544445297143097/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0156.rows BesselBatch0156.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0156.rows BesselBatch0156.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0156.rows BesselBatch0156.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0156.rows BesselBatch0156.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0156.rows BesselBatch0156.accepted ⟨5,by decide⟩
]
theorem rightAccepted : besselPointCheck (686177643281768795344103840481344028099/1250000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (686177643281768795344103840481344028099/1250000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0566.rows BesselBatch0566.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0566.rows BesselBatch0566.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0566.rows BesselBatch0566.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0566.rows BesselBatch0566.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0566.rows BesselBatch0566.accepted ⟨55,by decide⟩
]
theorem midAccepted : besselPointCheck (10963815162212228803171365268296049367889/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (10963815162212228803171365268296049367889/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0124.rows ScalarLogs0124.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0124.rows ScalarLogs0124.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0124.rows ScalarLogs0124.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0124.rows ScalarLogs0124.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0124.rows ScalarLogs0124.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0124.rows ScalarLogs0124.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0124.rows ScalarLogs0124.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0124.rows ScalarLogs0124.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0124.rows ScalarLogs0124.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0124.rows ScalarLogs0124.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0124.rows ScalarLogs0124.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0124.rows ScalarLogs0124.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0124.rows ScalarLogs0124.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0124.rows ScalarLogs0124.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0124.rows ScalarLogs0124.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0124.rows ScalarLogs0124.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0062.bracket0997 BracketBatch0062.bracket0998 (10963815162212228803171365268296049367889/20000000000000000000000000000000000000000) (45435328704343653323602545549189860237/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0062.bracket0997 BracketBatch0062.bracket0998
  (10963815162212228803171365268296049367889/20000000000000000000000000000000000000000) (45435328704343653323602545549189860237/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0997
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0998
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0155.rows BesselBatch0155.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0155.rows BesselBatch0155.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0155.rows BesselBatch0155.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0155.rows BesselBatch0155.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0156.rows BesselBatch0156.accepted ⟨0,by decide⟩
]
theorem leftAccepted : besselPointCheck (5489421146254150362752830723850752224789/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (5489421146254150362752830723850752224789/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0156.rows BesselBatch0156.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0156.rows BesselBatch0156.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0156.rows BesselBatch0156.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0156.rows BesselBatch0156.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0156.rows BesselBatch0156.accepted ⟨15,by decide⟩
]
theorem rightAccepted : besselPointCheck (1376119680915264979951979841575730134817/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1376119680915264979951979841575730134817/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0566.rows BesselBatch0566.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0566.rows BesselBatch0566.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0566.rows BesselBatch0566.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0566.rows BesselBatch0566.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0566.rows BesselBatch0566.accepted ⟨60,by decide⟩
]
theorem midAccepted : besselPointCheck (10993899869915210282560750090153672764057/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (10993899869915210282560750090153672764057/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0124.rows ScalarLogs0124.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0124.rows ScalarLogs0124.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0124.rows ScalarLogs0124.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0124.rows ScalarLogs0124.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0124.rows ScalarLogs0124.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0124.rows ScalarLogs0124.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0124.rows ScalarLogs0124.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0124.rows ScalarLogs0124.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0124.rows ScalarLogs0124.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0124.rows ScalarLogs0124.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0124.rows ScalarLogs0124.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0124.rows ScalarLogs0124.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0124.rows ScalarLogs0124.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0124.rows ScalarLogs0124.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0124.rows ScalarLogs0124.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0124.rows ScalarLogs0124.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0062.bracket0998 BracketBatch0062.bracket0999 (10993899869915210282560750090153672764057/20000000000000000000000000000000000000000) (45838733193878560238461271766179386267/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0062.bracket0998 BracketBatch0062.bracket0999
  (10993899869915210282560750090153672764057/20000000000000000000000000000000000000000) (45838733193878560238461271766179386267/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0998
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0999
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0156.rows BesselBatch0156.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0156.rows BesselBatch0156.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0156.rows BesselBatch0156.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0156.rows BesselBatch0156.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0156.rows BesselBatch0156.accepted ⟨10,by decide⟩
]
theorem leftAccepted : besselPointCheck (1100895744732211983961583873260584107853/2000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1100895744732211983961583873260584107853/2000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0156.rows BesselBatch0156.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0156.rows BesselBatch0156.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0156.rows BesselBatch0156.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0156.rows BesselBatch0156.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0156.rows BesselBatch0156.accepted ⟨25,by decide⟩
]
theorem rightAccepted : besselPointCheck (5519566924077107291212923072069897506551/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (5519566924077107291212923072069897506551/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0566.rows BesselBatch0566.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0566.rows BesselBatch0566.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0566.rows BesselBatch0566.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0567.rows BesselBatch0567.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0567.rows BesselBatch0567.accepted ⟨1,by decide⟩
]
theorem midAccepted : besselPointCheck (1378005705967270901377605304796602255727/2500000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1378005705967270901377605304796602255727/2500000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0124.rows ScalarLogs0124.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0124.rows ScalarLogs0124.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0124.rows ScalarLogs0124.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0124.rows ScalarLogs0124.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0124.rows ScalarLogs0124.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0124.rows ScalarLogs0124.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0124.rows ScalarLogs0124.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0124.rows ScalarLogs0124.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0124.rows ScalarLogs0124.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0124.rows ScalarLogs0124.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0124.rows ScalarLogs0124.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0124.rows ScalarLogs0124.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0124.rows ScalarLogs0124.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0124.rows ScalarLogs0124.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0124.rows ScalarLogs0124.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0124.rows ScalarLogs0124.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0062.bracket0999 BracketBatch0062.bracket1000 (1378005705967270901377605304796602255727/2500000000000000000000000000000000000000) (9248998746419937051064146474484075221/2000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0062.bracket0999 BracketBatch0062.bracket1000
  (1378005705967270901377605304796602255727/2500000000000000000000000000000000000000) (9248998746419937051064146474484075221/2000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0999
