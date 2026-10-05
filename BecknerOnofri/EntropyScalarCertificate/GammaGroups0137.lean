import BecknerOnofri.EntropyScalarCertificate.Bessel0171
import BecknerOnofri.EntropyScalarCertificate.Bessel0172
import BecknerOnofri.EntropyScalarCertificate.Bessel0574
import BecknerOnofri.EntropyScalarCertificate.Bessel0575
import BecknerOnofri.EntropyScalarCertificate.Brackets0068
import BecknerOnofri.EntropyScalarCertificate.Brackets0069
import BecknerOnofri.EntropyScalarCertificate.Logs0137
import BecknerOnofri.ScalarElementaryComposition
import BecknerOnofri.ScalarGammaEnclosure
import BecknerOnofri.ScalarLogBesselEndpoints
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1096
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0171.rows BesselBatch0171.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0171.rows BesselBatch0171.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0171.rows BesselBatch0171.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0171.rows BesselBatch0171.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0171.rows BesselBatch0171.accepted ⟨20,by decide⟩
]
theorem leftAccepted : besselPointCheck (357168524020092603664889803671945530193/500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (357168524020092603664889803671945530193/500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0171.rows BesselBatch0171.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0171.rows BesselBatch0171.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0171.rows BesselBatch0171.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0171.rows BesselBatch0171.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0171.rows BesselBatch0171.accepted ⟨35,by decide⟩
]
theorem rightAccepted : besselPointCheck (3581265306034620017660791706078732525471/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (3581265306034620017660791706078732525471/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0574.rows BesselBatch0574.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0574.rows BesselBatch0574.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0574.rows BesselBatch0574.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0574.rows BesselBatch0574.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0574.rows BesselBatch0574.accepted ⟨38,by decide⟩
]
theorem midAccepted : besselPointCheck (7152950546235546054309689742798187827401/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (7152950546235546054309689742798187827401/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0137.rows ScalarLogs0137.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0137.rows ScalarLogs0137.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0137.rows ScalarLogs0137.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0137.rows ScalarLogs0137.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0137.rows ScalarLogs0137.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0137.rows ScalarLogs0137.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0137.rows ScalarLogs0137.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0137.rows ScalarLogs0137.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0137.rows ScalarLogs0137.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0137.rows ScalarLogs0137.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0137.rows ScalarLogs0137.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0137.rows ScalarLogs0137.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0137.rows ScalarLogs0137.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0137.rows ScalarLogs0137.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0137.rows ScalarLogs0137.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0137.rows ScalarLogs0137.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0068.bracket1096 BracketBatch0068.bracket1097 (7152950546235546054309689742798187827401/10000000000000000000000000000000000000000) (102135514065367974807015128430318683549/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0068.bracket1096 BracketBatch0068.bracket1097
  (7152950546235546054309689742798187827401/10000000000000000000000000000000000000000) (102135514065367974807015128430318683549/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1096
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1097
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0171.rows BesselBatch0171.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0171.rows BesselBatch0171.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0171.rows BesselBatch0171.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0171.rows BesselBatch0171.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0171.rows BesselBatch0171.accepted ⟨30,by decide⟩
]
theorem leftAccepted : besselPointCheck (7162530612069240035321583412157465050939/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (7162530612069240035321583412157465050939/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0171.rows BesselBatch0171.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0171.rows BesselBatch0171.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0171.rows BesselBatch0171.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0171.rows BesselBatch0171.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0171.rows BesselBatch0171.accepted ⟨45,by decide⟩
]
theorem rightAccepted : besselPointCheck (1795436921624070892302535577735430751549/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1795436921624070892302535577735430751549/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0574.rows BesselBatch0574.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0574.rows BesselBatch0574.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0574.rows BesselBatch0574.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0574.rows BesselBatch0574.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0574.rows BesselBatch0574.accepted ⟨43,by decide⟩
]
theorem midAccepted : besselPointCheck (2868855659713104720906345144619837611427/4000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (2868855659713104720906345144619837611427/4000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0137.rows ScalarLogs0137.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0137.rows ScalarLogs0137.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0137.rows ScalarLogs0137.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0137.rows ScalarLogs0137.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0137.rows ScalarLogs0137.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0137.rows ScalarLogs0137.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0137.rows ScalarLogs0137.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0137.rows ScalarLogs0137.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0137.rows ScalarLogs0137.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0137.rows ScalarLogs0137.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0137.rows ScalarLogs0137.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0137.rows ScalarLogs0137.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0137.rows ScalarLogs0137.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0137.rows ScalarLogs0137.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0137.rows ScalarLogs0137.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0137.rows ScalarLogs0137.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0068.bracket1097 BracketBatch0068.bracket1098 (2868855659713104720906345144619837611427/4000000000000000000000000000000000000000) (51458061721827198763772766690498907533/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0068.bracket1097 BracketBatch0068.bracket1098
  (2868855659713104720906345144619837611427/4000000000000000000000000000000000000000) (51458061721827198763772766690498907533/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1097
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1098
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0171.rows BesselBatch0171.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0171.rows BesselBatch0171.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0171.rows BesselBatch0171.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0171.rows BesselBatch0171.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0171.rows BesselBatch0171.accepted ⟨40,by decide⟩
]
theorem leftAccepted : besselPointCheck (7181747686496283569210142310941723006193/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (7181747686496283569210142310941723006193/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0171.rows BesselBatch0171.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0171.rows BesselBatch0171.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0171.rows BesselBatch0171.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0171.rows BesselBatch0171.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0171.rows BesselBatch0171.accepted ⟨55,by decide⟩
]
theorem rightAccepted : besselPointCheck (7201022106017832246838084909484916181119/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (7201022106017832246838084909484916181119/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0574.rows BesselBatch0574.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0574.rows BesselBatch0574.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0574.rows BesselBatch0574.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0574.rows BesselBatch0574.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0574.rows BesselBatch0574.accepted ⟨48,by decide⟩
]
theorem midAccepted : besselPointCheck (898923112032132238503014201276664949207/1250000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (898923112032132238503014201276664949207/1250000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0137.rows ScalarLogs0137.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0137.rows ScalarLogs0137.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0137.rows ScalarLogs0137.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0137.rows ScalarLogs0137.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0137.rows ScalarLogs0137.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0137.rows ScalarLogs0137.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0137.rows ScalarLogs0137.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0137.rows ScalarLogs0137.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0137.rows ScalarLogs0137.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0137.rows ScalarLogs0137.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0137.rows ScalarLogs0137.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0137.rows ScalarLogs0137.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0137.rows ScalarLogs0137.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0137.rows ScalarLogs0137.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0137.rows ScalarLogs0137.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0137.rows ScalarLogs0137.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0068.bracket1098 BracketBatch0068.bracket1099 (898923112032132238503014201276664949207/1250000000000000000000000000000000000000) (103701728931599310026521157543538697369/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0068.bracket1098 BracketBatch0068.bracket1099
  (898923112032132238503014201276664949207/1250000000000000000000000000000000000000) (103701728931599310026521157543538697369/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1098
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1099
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0171.rows BesselBatch0171.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0171.rows BesselBatch0171.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0171.rows BesselBatch0171.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0171.rows BesselBatch0171.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0171.rows BesselBatch0171.accepted ⟨50,by decide⟩
]
theorem leftAccepted : besselPointCheck (1800255526504458061709521227371229045279/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1800255526504458061709521227371229045279/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0171.rows BesselBatch0171.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0171.rows BesselBatch0171.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0171.rows BesselBatch0171.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0172.rows BesselBatch0172.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0172.rows BesselBatch0172.accepted ⟨1,by decide⟩
]
theorem rightAccepted : besselPointCheck (7220354276830760443648117110438870673911/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (7220354276830760443648117110438870673911/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0574.rows BesselBatch0574.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0574.rows BesselBatch0574.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0574.rows BesselBatch0574.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0574.rows BesselBatch0574.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0574.rows BesselBatch0574.accepted ⟨53,by decide⟩
]
theorem midAccepted : besselPointCheck (14421376382848592690486202019923786855027/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (14421376382848592690486202019923786855027/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0137.rows ScalarLogs0137.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0137.rows ScalarLogs0137.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0137.rows ScalarLogs0137.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0137.rows ScalarLogs0137.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0137.rows ScalarLogs0137.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0137.rows ScalarLogs0137.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0137.rows ScalarLogs0137.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0137.rows ScalarLogs0137.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0137.rows ScalarLogs0137.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0137.rows ScalarLogs0137.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0137.rows ScalarLogs0137.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0137.rows ScalarLogs0137.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0137.rows ScalarLogs0137.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0137.rows ScalarLogs0137.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0137.rows ScalarLogs0137.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0137.rows ScalarLogs0137.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0068.bracket1099 BracketBatch0068.bracket1100 (14421376382848592690486202019923786855027/20000000000000000000000000000000000000000) (52246179824692206334379224218213690457/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0068.bracket1099 BracketBatch0068.bracket1100
  (14421376382848592690486202019923786855027/20000000000000000000000000000000000000000) (52246179824692206334379224218213690457/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1099
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1100
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0171.rows BesselBatch0171.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0171.rows BesselBatch0171.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0171.rows BesselBatch0171.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0171.rows BesselBatch0171.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0171.rows BesselBatch0171.accepted ⟨60,by decide⟩
]
theorem leftAccepted : besselPointCheck (1805088569207690110912029277609717668477/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1805088569207690110912029277609717668477/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0172.rows BesselBatch0172.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0172.rows BesselBatch0172.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0172.rows BesselBatch0172.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0172.rows BesselBatch0172.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0172.rows BesselBatch0172.accepted ⟨11,by decide⟩
]
theorem rightAccepted : besselPointCheck (7239744609042321549207471972421670628957/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (7239744609042321549207471972421670628957/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0574.rows BesselBatch0574.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0574.rows BesselBatch0574.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0574.rows BesselBatch0574.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0574.rows BesselBatch0574.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0574.rows BesselBatch0574.accepted ⟨58,by decide⟩
]
theorem midAccepted : besselPointCheck (2892019777174616398571117816572108260573/4000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (2892019777174616398571117816572108260573/4000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0137.rows ScalarLogs0137.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0137.rows ScalarLogs0137.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0137.rows ScalarLogs0137.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0137.rows ScalarLogs0137.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0137.rows ScalarLogs0137.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0137.rows ScalarLogs0137.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0137.rows ScalarLogs0137.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0137.rows ScalarLogs0137.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0137.rows ScalarLogs0137.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0137.rows ScalarLogs0137.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0137.rows ScalarLogs0137.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0137.rows ScalarLogs0137.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0137.rows ScalarLogs0137.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0137.rows ScalarLogs0137.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0137.rows ScalarLogs0137.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0137.rows ScalarLogs0137.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0068.bracket1100 BracketBatch0068.bracket1101 (2892019777174616398571117816572108260573/4000000000000000000000000000000000000000) (105288044919638717389004169296627447629/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0068.bracket1100 BracketBatch0068.bracket1101
  (2892019777174616398571117816572108260573/4000000000000000000000000000000000000000) (105288044919638717389004169296627447629/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1100
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1101
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0172.rows BesselBatch0172.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0172.rows BesselBatch0172.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0172.rows BesselBatch0172.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0172.rows BesselBatch0172.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0172.rows BesselBatch0172.accepted ⟨6,by decide⟩
]
theorem leftAccepted : besselPointCheck (3619872304521160774603735986210835314477/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (3619872304521160774603735986210835314477/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0172.rows BesselBatch0172.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0172.rows BesselBatch0172.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0172.rows BesselBatch0172.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0172.rows BesselBatch0172.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0172.rows BesselBatch0172.accepted ⟨21,by decide⟩
]
theorem rightAccepted : besselPointCheck (7259193516719236908986007311055800684377/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (7259193516719236908986007311055800684377/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0574.rows BesselBatch0574.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0574.rows BesselBatch0574.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0574.rows BesselBatch0574.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0574.rows BesselBatch0574.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0574.rows BesselBatch0574.accepted ⟨63,by decide⟩
]
theorem midAccepted : besselPointCheck (14498938125761558458193479283477471313331/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (14498938125761558458193479283477471313331/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0137.rows ScalarLogs0137.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0137.rows ScalarLogs0137.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0137.rows ScalarLogs0137.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0137.rows ScalarLogs0137.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0137.rows ScalarLogs0137.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0137.rows ScalarLogs0137.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0137.rows ScalarLogs0137.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0137.rows ScalarLogs0137.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0137.rows ScalarLogs0137.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0137.rows ScalarLogs0137.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0137.rows ScalarLogs0137.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0137.rows ScalarLogs0137.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0137.rows ScalarLogs0137.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0137.rows ScalarLogs0137.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0137.rows ScalarLogs0137.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0137.rows ScalarLogs0137.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0068.bracket1101 BracketBatch0068.bracket1102 (14498938125761558458193479283477471313331/20000000000000000000000000000000000000000) (106088814269579153976957680746972866353/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0068.bracket1101 BracketBatch0068.bracket1102
  (14498938125761558458193479283477471313331/20000000000000000000000000000000000000000) (106088814269579153976957680746972866353/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1101
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1102
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0172.rows BesselBatch0172.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0172.rows BesselBatch0172.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0172.rows BesselBatch0172.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0172.rows BesselBatch0172.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0172.rows BesselBatch0172.accepted ⟨16,by decide⟩
]
theorem leftAccepted : besselPointCheck (3629596758359618454493003655527900342187/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (3629596758359618454493003655527900342187/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0172.rows BesselBatch0172.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0172.rows BesselBatch0172.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0172.rows BesselBatch0172.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0172.rows BesselBatch0172.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0172.rows BesselBatch0172.accepted ⟨31,by decide⟩
]
theorem rightAccepted : besselPointCheck (7278701417937532595286850705232125018383/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (7278701417937532595286850705232125018383/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0575.rows BesselBatch0575.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0575.rows BesselBatch0575.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0575.rows BesselBatch0575.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0575.rows BesselBatch0575.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0575.rows BesselBatch0575.accepted ⟨4,by decide⟩
]
theorem midAccepted : besselPointCheck (14537894934656769504272858016287925702757/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (14537894934656769504272858016287925702757/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0137.rows ScalarLogs0137.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0137.rows ScalarLogs0137.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0137.rows ScalarLogs0137.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0137.rows ScalarLogs0137.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0137.rows ScalarLogs0137.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0137.rows ScalarLogs0137.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0137.rows ScalarLogs0137.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0137.rows ScalarLogs0137.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0137.rows ScalarLogs0137.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0137.rows ScalarLogs0137.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0137.rows ScalarLogs0137.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0137.rows ScalarLogs0137.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0137.rows ScalarLogs0137.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0137.rows ScalarLogs0137.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0137.rows ScalarLogs0137.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0137.rows ScalarLogs0137.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0068.bracket1102 BracketBatch0068.bracket1103 (14537894934656769504272858016287925702757/20000000000000000000000000000000000000000) (3340459294786933053497212544090359617/312500000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0068.bracket1102 BracketBatch0068.bracket1103
  (14537894934656769504272858016287925702757/20000000000000000000000000000000000000000) (3340459294786933053497212544090359617/312500000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1102
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1103
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0172.rows BesselBatch0172.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0172.rows BesselBatch0172.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0172.rows BesselBatch0172.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0172.rows BesselBatch0172.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0172.rows BesselBatch0172.accepted ⟨26,by decide⟩
]
theorem leftAccepted : besselPointCheck (363935070896876629764342535261606250919/500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (363935070896876629764342535261606250919/500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0172.rows BesselBatch0172.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0172.rows BesselBatch0172.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0172.rows BesselBatch0172.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0172.rows BesselBatch0172.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0172.rows BesselBatch0172.accepted ⟨41,by decide⟩
]
theorem rightAccepted : besselPointCheck (456141795927071085752315302784996331993/625000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (456141795927071085752315302784996331993/625000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0575.rows BesselBatch0575.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0575.rows BesselBatch0575.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0575.rows BesselBatch0575.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0575.rows BesselBatch0575.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0575.rows BesselBatch0575.accepted ⟨9,by decide⟩
]
theorem midAccepted : besselPointCheck (3644242538192667491830973887448016582567/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (3644242538192667491830973887448016582567/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0137.rows ScalarLogs0137.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0137.rows ScalarLogs0137.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0137.rows ScalarLogs0137.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0137.rows ScalarLogs0137.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0137.rows ScalarLogs0137.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0137.rows ScalarLogs0137.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0137.rows ScalarLogs0137.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0137.rows ScalarLogs0137.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0137.rows ScalarLogs0137.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0137.rows ScalarLogs0137.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0137.rows ScalarLogs0137.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0137.rows ScalarLogs0137.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0137.rows ScalarLogs0137.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0137.rows ScalarLogs0137.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0137.rows ScalarLogs0137.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0137.rows ScalarLogs0137.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0068.bracket1103 BracketBatch0069.bracket1104 (3644242538192667491830973887448016582567/5000000000000000000000000000000000000000) (26926407814861304777750801195995000049/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0068.bracket1103 BracketBatch0069.bracket1104
  (3644242538192667491830973887448016582567/5000000000000000000000000000000000000000) (26926407814861304777750801195995000049/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1103
