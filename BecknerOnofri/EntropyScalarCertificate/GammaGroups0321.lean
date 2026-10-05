import BecknerOnofri.EntropyScalarCertificate.Bessel0401
import BecknerOnofri.EntropyScalarCertificate.Bessel0402
import BecknerOnofri.EntropyScalarCertificate.Bessel0689
import BecknerOnofri.EntropyScalarCertificate.Bessel0690
import BecknerOnofri.EntropyScalarCertificate.Brackets0160
import BecknerOnofri.EntropyScalarCertificate.Brackets0161
import BecknerOnofri.EntropyScalarCertificate.Logs0321
import BecknerOnofri.ScalarElementaryComposition
import BecknerOnofri.ScalarGammaEnclosure
import BecknerOnofri.ScalarLogBesselEndpoints
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2568
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0401.rows BesselBatch0401.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0401.rows BesselBatch0401.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0401.rows BesselBatch0401.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0401.rows BesselBatch0401.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0401.rows BesselBatch0401.accepted ⟨20,by decide⟩
]
theorem leftAccepted : besselPointCheck (404487615904026647762331459592270350950527/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (404487615904026647762331459592270350950527/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0401.rows BesselBatch0401.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0401.rows BesselBatch0401.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0401.rows BesselBatch0401.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0401.rows BesselBatch0401.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0401.rows BesselBatch0401.accepted ⟨35,by decide⟩
]
theorem rightAccepted : besselPointCheck (81158503017356289488684802908969934159789/2000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (81158503017356289488684802908969934159789/2000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0689.rows BesselBatch0689.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0689.rows BesselBatch0689.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0689.rows BesselBatch0689.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0689.rows BesselBatch0689.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0689.rows BesselBatch0689.accepted ⟨38,by decide⟩
]
theorem midAccepted : besselPointCheck (25321254093462752975179858566785000679671/625000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (25321254093462752975179858566785000679671/625000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0321.rows ScalarLogs0321.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0321.rows ScalarLogs0321.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0321.rows ScalarLogs0321.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0321.rows ScalarLogs0321.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0321.rows ScalarLogs0321.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0321.rows ScalarLogs0321.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0321.rows ScalarLogs0321.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0321.rows ScalarLogs0321.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0321.rows ScalarLogs0321.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0321.rows ScalarLogs0321.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0321.rows ScalarLogs0321.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0321.rows ScalarLogs0321.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0321.rows ScalarLogs0321.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0321.rows ScalarLogs0321.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0321.rows ScalarLogs0321.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0321.rows ScalarLogs0321.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0160.bracket2568 BracketBatch0160.bracket2569 (25321254093462752975179858566785000679671/625000000000000000000000000000000000000) (1183337916069120155833667359664513713763/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0160.bracket2568 BracketBatch0160.bracket2569
  (25321254093462752975179858566785000679671/625000000000000000000000000000000000000) (1183337916069120155833667359664513713763/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2568
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2569
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0401.rows BesselBatch0401.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0401.rows BesselBatch0401.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0401.rows BesselBatch0401.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0401.rows BesselBatch0401.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0401.rows BesselBatch0401.accepted ⟨30,by decide⟩
]
theorem leftAccepted : besselPointCheck (202896257543390723721712007272424835399471/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (202896257543390723721712007272424835399471/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0401.rows BesselBatch0401.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0401.rows BesselBatch0401.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0401.rows BesselBatch0401.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0401.rows BesselBatch0401.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0401.rows BesselBatch0401.accepted ⟨45,by decide⟩
]
theorem rightAccepted : besselPointCheck (407105887896189817366706020407815233170709/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (407105887896189817366706020407815233170709/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0689.rows BesselBatch0689.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0689.rows BesselBatch0689.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0689.rows BesselBatch0689.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0689.rows BesselBatch0689.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0689.rows BesselBatch0689.accepted ⟨43,by decide⟩
]
theorem midAccepted : besselPointCheck (812898402982971264810130034952664903969651/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (812898402982971264810130034952664903969651/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0321.rows ScalarLogs0321.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0321.rows ScalarLogs0321.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0321.rows ScalarLogs0321.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0321.rows ScalarLogs0321.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0321.rows ScalarLogs0321.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0321.rows ScalarLogs0321.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0321.rows ScalarLogs0321.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0321.rows ScalarLogs0321.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0321.rows ScalarLogs0321.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0321.rows ScalarLogs0321.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0321.rows ScalarLogs0321.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0321.rows ScalarLogs0321.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0321.rows ScalarLogs0321.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0321.rows ScalarLogs0321.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0321.rows ScalarLogs0321.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0321.rows ScalarLogs0321.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0160.bracket2569 BracketBatch0160.bracket2570 (812898402982971264810130034952664903969651/20000000000000000000000000000000000000000) (947615430609218876962917775386148429899/2000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0160.bracket2569 BracketBatch0160.bracket2570
  (812898402982971264810130034952664903969651/20000000000000000000000000000000000000000) (947615430609218876962917775386148429899/2000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2569
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2570
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0401.rows BesselBatch0401.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0401.rows BesselBatch0401.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0401.rows BesselBatch0401.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0401.rows BesselBatch0401.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0401.rows BesselBatch0401.accepted ⟨40,by decide⟩
]
theorem leftAccepted : besselPointCheck (203552943948094908683353010203907616585353/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (203552943948094908683353010203907616585353/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0401.rows BesselBatch0401.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0401.rows BesselBatch0401.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0401.rows BesselBatch0401.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0401.rows BesselBatch0401.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0401.rows BesselBatch0401.accepted ⟨55,by decide⟩
]
theorem rightAccepted : besselPointCheck (204213908568190372029969222742371923814571/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (204213908568190372029969222742371923814571/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0689.rows BesselBatch0689.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0689.rows BesselBatch0689.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0689.rows BesselBatch0689.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0689.rows BesselBatch0689.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0689.rows BesselBatch0689.accepted ⟨48,by decide⟩
]
theorem midAccepted : besselPointCheck (101941713129071320178330558236569885099981/2500000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (101941713129071320178330558236569885099981/2500000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0321.rows ScalarLogs0321.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0321.rows ScalarLogs0321.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0321.rows ScalarLogs0321.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0321.rows ScalarLogs0321.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0321.rows ScalarLogs0321.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0321.rows ScalarLogs0321.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0321.rows ScalarLogs0321.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0321.rows ScalarLogs0321.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0321.rows ScalarLogs0321.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0321.rows ScalarLogs0321.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0321.rows ScalarLogs0321.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0321.rows ScalarLogs0321.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0321.rows ScalarLogs0321.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0321.rows ScalarLogs0321.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0321.rows ScalarLogs0321.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0321.rows ScalarLogs0321.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0160.bracket2570 BracketBatch0160.bracket2571 (101941713129071320178330558236569885099981/2500000000000000000000000000000000000000) (4742818526448273878775642287876403402597/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0160.bracket2570 BracketBatch0160.bracket2571
  (101941713129071320178330558236569885099981/2500000000000000000000000000000000000000) (4742818526448273878775642287876403402597/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2570
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2571
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0401.rows BesselBatch0401.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0401.rows BesselBatch0401.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0401.rows BesselBatch0401.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0401.rows BesselBatch0401.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0401.rows BesselBatch0401.accepted ⟨50,by decide⟩
]
theorem leftAccepted : besselPointCheck (408427817136380744059938445484743847629139/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (408427817136380744059938445484743847629139/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0401.rows BesselBatch0401.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0401.rows BesselBatch0401.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0401.rows BesselBatch0401.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0402.rows BesselBatch0402.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0402.rows BesselBatch0402.accepted ⟨1,by decide⟩
]
theorem rightAccepted : besselPointCheck (102439596673472535412716398347361124311013/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (102439596673472535412716398347361124311013/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0689.rows BesselBatch0689.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0689.rows BesselBatch0689.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0689.rows BesselBatch0689.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0689.rows BesselBatch0689.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0689.rows BesselBatch0689.accepted ⟨53,by decide⟩
]
theorem midAccepted : besselPointCheck (818186203830270885710804038874188344873191/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (818186203830270885710804038874188344873191/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0321.rows ScalarLogs0321.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0321.rows ScalarLogs0321.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0321.rows ScalarLogs0321.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0321.rows ScalarLogs0321.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0321.rows ScalarLogs0321.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0321.rows ScalarLogs0321.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0321.rows ScalarLogs0321.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0321.rows ScalarLogs0321.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0321.rows ScalarLogs0321.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0321.rows ScalarLogs0321.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0321.rows ScalarLogs0321.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0321.rows ScalarLogs0321.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0321.rows ScalarLogs0321.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0321.rows ScalarLogs0321.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0321.rows ScalarLogs0321.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0321.rows ScalarLogs0321.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0160.bracket2571 BracketBatch0160.bracket2572 (818186203830270885710804038874188344873191/20000000000000000000000000000000000000000) (1186893970678770524009994005597557692697/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0160.bracket2571 BracketBatch0160.bracket2572
  (818186203830270885710804038874188344873191/20000000000000000000000000000000000000000) (1186893970678770524009994005597557692697/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2571
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2572
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0401.rows BesselBatch0401.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0401.rows BesselBatch0401.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0401.rows BesselBatch0401.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0401.rows BesselBatch0401.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0401.rows BesselBatch0401.accepted ⟨60,by decide⟩
]
theorem leftAccepted : besselPointCheck (409758386693890141650865593389444497244049/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (409758386693890141650865593389444497244049/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0402.rows BesselBatch0402.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0402.rows BesselBatch0402.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0402.rows BesselBatch0402.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0402.rows BesselBatch0402.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0402.rows BesselBatch0402.accepted ⟨11,by decide⟩
]
theorem rightAccepted : besselPointCheck (411097681555405227722695662740736842580807/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (411097681555405227722695662740736842580807/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0689.rows BesselBatch0689.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0689.rows BesselBatch0689.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0689.rows BesselBatch0689.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0689.rows BesselBatch0689.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0689.rows BesselBatch0689.accepted ⟨58,by decide⟩
]
theorem midAccepted : besselPointCheck (102607008531161921171695157016272667478107/2500000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (102607008531161921171695157016272667478107/2500000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0321.rows ScalarLogs0321.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0321.rows ScalarLogs0321.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0321.rows ScalarLogs0321.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0321.rows ScalarLogs0321.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0321.rows ScalarLogs0321.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0321.rows ScalarLogs0321.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0321.rows ScalarLogs0321.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0321.rows ScalarLogs0321.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0321.rows ScalarLogs0321.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0321.rows ScalarLogs0321.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0321.rows ScalarLogs0321.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0321.rows ScalarLogs0321.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0321.rows ScalarLogs0321.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0321.rows ScalarLogs0321.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0321.rows ScalarLogs0321.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0321.rows ScalarLogs0321.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0160.bracket2572 BracketBatch0160.bracket2573 (102607008531161921171695157016272667478107/2500000000000000000000000000000000000000) (2376174660474567542502837582072451585783/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0160.bracket2572 BracketBatch0160.bracket2573
  (102607008531161921171695157016272667478107/2500000000000000000000000000000000000000) (2376174660474567542502837582072451585783/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2572
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2573
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0402.rows BesselBatch0402.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0402.rows BesselBatch0402.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0402.rows BesselBatch0402.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0402.rows BesselBatch0402.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0402.rows BesselBatch0402.accepted ⟨6,by decide⟩
]
theorem leftAccepted : besselPointCheck (102774420388851306930673915685184210645201/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (102774420388851306930673915685184210645201/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0402.rows BesselBatch0402.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0402.rows BesselBatch0402.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0402.rows BesselBatch0402.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0402.rows BesselBatch0402.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0402.rows BesselBatch0402.accepted ⟨21,by decide⟩
]
theorem rightAccepted : besselPointCheck (412445787825859117114102846190062894353279/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (412445787825859117114102846190062894353279/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0689.rows BesselBatch0689.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0689.rows BesselBatch0689.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0689.rows BesselBatch0689.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0689.rows BesselBatch0689.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0689.rows BesselBatch0689.accepted ⟨63,by decide⟩
]
theorem midAccepted : besselPointCheck (823543469381264344836798508930799736934083/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (823543469381264344836798508930799736934083/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0321.rows ScalarLogs0321.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0321.rows ScalarLogs0321.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0321.rows ScalarLogs0321.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0321.rows ScalarLogs0321.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0321.rows ScalarLogs0321.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0321.rows ScalarLogs0321.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0321.rows ScalarLogs0321.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0321.rows ScalarLogs0321.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0321.rows ScalarLogs0321.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0321.rows ScalarLogs0321.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0321.rows ScalarLogs0321.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0321.rows ScalarLogs0321.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0321.rows ScalarLogs0321.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0321.rows ScalarLogs0321.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0321.rows ScalarLogs0321.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0321.rows ScalarLogs0321.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0160.bracket2573 BracketBatch0160.bracket2574 (823543469381264344836798508930799736934083/20000000000000000000000000000000000000000) (148660591910413403383897363638025738049/312500000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0160.bracket2573 BracketBatch0160.bracket2574
  (823543469381264344836798508930799736934083/20000000000000000000000000000000000000000) (148660591910413403383897363638025738049/312500000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2573
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2574
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0402.rows BesselBatch0402.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0402.rows BesselBatch0402.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0402.rows BesselBatch0402.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0402.rows BesselBatch0402.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0402.rows BesselBatch0402.accepted ⟨16,by decide⟩
]
theorem leftAccepted : besselPointCheck (103111446956464779278525711547515723588319/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (103111446956464779278525711547515723588319/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0402.rows BesselBatch0402.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0402.rows BesselBatch0402.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0402.rows BesselBatch0402.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0402.rows BesselBatch0402.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0402.rows BesselBatch0402.accepted ⟨31,by decide⟩
]
theorem rightAccepted : besselPointCheck (206901396373441862253676885245142327460239/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (206901396373441862253676885245142327460239/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0690.rows BesselBatch0690.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0690.rows BesselBatch0690.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0690.rows BesselBatch0690.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0690.rows BesselBatch0690.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0690.rows BesselBatch0690.accepted ⟨4,by decide⟩
]
theorem midAccepted : besselPointCheck (413124290286371420810728308340173774636877/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (413124290286371420810728308340173774636877/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0321.rows ScalarLogs0321.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0321.rows ScalarLogs0321.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0321.rows ScalarLogs0321.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0321.rows ScalarLogs0321.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0321.rows ScalarLogs0321.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0321.rows ScalarLogs0321.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0321.rows ScalarLogs0321.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0321.rows ScalarLogs0321.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0321.rows ScalarLogs0321.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0321.rows ScalarLogs0321.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0321.rows ScalarLogs0321.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0321.rows ScalarLogs0321.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0321.rows ScalarLogs0321.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0321.rows ScalarLogs0321.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0321.rows ScalarLogs0321.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0321.rows ScalarLogs0321.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0160.bracket2574 BracketBatch0160.bracket2575 (413124290286371420810728308340173774636877/10000000000000000000000000000000000000000) (595243105517510572588312760663925982243/1250000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0160.bracket2574 BracketBatch0160.bracket2575
  (413124290286371420810728308340173774636877/10000000000000000000000000000000000000000) (595243105517510572588312760663925982243/1250000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2574
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2575
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0402.rows BesselBatch0402.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0402.rows BesselBatch0402.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0402.rows BesselBatch0402.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0402.rows BesselBatch0402.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0402.rows BesselBatch0402.accepted ⟨26,by decide⟩
]
theorem leftAccepted : besselPointCheck (16552111709875348980294150819611386196819/400000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (16552111709875348980294150819611386196819/400000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0402.rows BesselBatch0402.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0402.rows BesselBatch0402.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0402.rows BesselBatch0402.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0402.rows BesselBatch0402.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0402.rows BesselBatch0402.accepted ⟨41,by decide⟩
]
theorem rightAccepted : besselPointCheck (207584392357814640487571967498756691313861/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (207584392357814640487571967498756691313861/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0690.rows BesselBatch0690.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0690.rows BesselBatch0690.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0690.rows BesselBatch0690.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0690.rows BesselBatch0690.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0690.rows BesselBatch0690.accepted ⟨9,by decide⟩
]
theorem midAccepted : besselPointCheck (828971577462513005482497705487798037548197/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (828971577462513005482497705487798037548197/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0321.rows ScalarLogs0321.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0321.rows ScalarLogs0321.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0321.rows ScalarLogs0321.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0321.rows ScalarLogs0321.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0321.rows ScalarLogs0321.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0321.rows ScalarLogs0321.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0321.rows ScalarLogs0321.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0321.rows ScalarLogs0321.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0321.rows ScalarLogs0321.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0321.rows ScalarLogs0321.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0321.rows ScalarLogs0321.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0321.rows ScalarLogs0321.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0321.rows ScalarLogs0321.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0321.rows ScalarLogs0321.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0321.rows ScalarLogs0321.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0321.rows ScalarLogs0321.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0160.bracket2575 BracketBatch0161.bracket2576 (828971577462513005482497705487798037548197/20000000000000000000000000000000000000000) (2383383565871106139963886983398062885761/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0160.bracket2575 BracketBatch0161.bracket2576
  (828971577462513005482497705487798037548197/20000000000000000000000000000000000000000) (2383383565871106139963886983398062885761/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2575
