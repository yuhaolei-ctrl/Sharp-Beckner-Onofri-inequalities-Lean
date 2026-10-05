import BecknerOnofri.EntropyScalarCertificate.Bessel0068
import BecknerOnofri.EntropyScalarCertificate.Bessel0069
import BecknerOnofri.EntropyScalarCertificate.Bessel0070
import BecknerOnofri.EntropyScalarCertificate.Bessel0523
import BecknerOnofri.EntropyScalarCertificate.Brackets0027
import BecknerOnofri.EntropyScalarCertificate.Brackets0028
import BecknerOnofri.EntropyScalarCertificate.Logs0055
import BecknerOnofri.ScalarElementaryComposition
import BecknerOnofri.ScalarGammaEnclosure
import BecknerOnofri.ScalarLogBesselEndpoints
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0440
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0068.rows BesselBatch0068.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0068.rows BesselBatch0068.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0068.rows BesselBatch0068.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0068.rows BesselBatch0068.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0068.rows BesselBatch0068.accepted ⟨52,by decide⟩
]
theorem leftAccepted : besselPointCheck (73017689916657911403932846365906143053/500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (73017689916657911403932846365906143053/500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0068.rows BesselBatch0068.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0069.rows BesselBatch0069.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0069.rows BesselBatch0069.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0069.rows BesselBatch0069.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0069.rows BesselBatch0069.accepted ⟨3,by decide⟩
]
theorem rightAccepted : besselPointCheck (365604599881062658790321669690133706187/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (365604599881062658790321669690133706187/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0523.rows BesselBatch0523.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0523.rows BesselBatch0523.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0523.rows BesselBatch0523.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0523.rows BesselBatch0523.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0523.rows BesselBatch0523.accepted ⟨22,by decide⟩
]
theorem midAccepted : besselPointCheck (182673262366088053952496475379916105363/1250000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (182673262366088053952496475379916105363/1250000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0055.rows ScalarLogs0055.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0055.rows ScalarLogs0055.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0055.rows ScalarLogs0055.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0055.rows ScalarLogs0055.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0055.rows ScalarLogs0055.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0055.rows ScalarLogs0055.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0055.rows ScalarLogs0055.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0055.rows ScalarLogs0055.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0055.rows ScalarLogs0055.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0055.rows ScalarLogs0055.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0055.rows ScalarLogs0055.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0055.rows ScalarLogs0055.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0055.rows ScalarLogs0055.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0055.rows ScalarLogs0055.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0055.rows ScalarLogs0055.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0055.rows ScalarLogs0055.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0027.bracket0440 BracketBatch0027.bracket0441 (182673262366088053952496475379916105363/1250000000000000000000000000000000000000) (171057110938392102527529781608792241/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0027.bracket0440 BracketBatch0027.bracket0441
  (182673262366088053952496475379916105363/1250000000000000000000000000000000000000) (171057110938392102527529781608792241/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0440
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0441
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0068.rows BesselBatch0068.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0068.rows BesselBatch0068.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0068.rows BesselBatch0068.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0068.rows BesselBatch0068.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0068.rows BesselBatch0068.accepted ⟨62,by decide⟩
]
theorem leftAccepted : besselPointCheck (292483679904850127032257335752106964949/2000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (292483679904850127032257335752106964949/2000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0069.rows BesselBatch0069.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0069.rows BesselBatch0069.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0069.rows BesselBatch0069.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0069.rows BesselBatch0069.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0069.rows BesselBatch0069.accepted ⟨13,by decide⟩
]
theorem rightAccepted : besselPointCheck (1464483184892061242103916819820065636797/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1464483184892061242103916819820065636797/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0523.rows BesselBatch0523.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0523.rows BesselBatch0523.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0523.rows BesselBatch0523.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0523.rows BesselBatch0523.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0523.rows BesselBatch0523.accepted ⟨27,by decide⟩
]
theorem midAccepted : besselPointCheck (1463450792208155938632601749290300230771/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1463450792208155938632601749290300230771/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0055.rows ScalarLogs0055.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0055.rows ScalarLogs0055.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0055.rows ScalarLogs0055.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0055.rows ScalarLogs0055.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0055.rows ScalarLogs0055.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0055.rows ScalarLogs0055.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0055.rows ScalarLogs0055.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0055.rows ScalarLogs0055.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0055.rows ScalarLogs0055.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0055.rows ScalarLogs0055.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0055.rows ScalarLogs0055.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0055.rows ScalarLogs0055.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0055.rows ScalarLogs0055.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0055.rows ScalarLogs0055.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0055.rows ScalarLogs0055.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0055.rows ScalarLogs0055.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0027.bracket0441 BracketBatch0027.bracket0442 (1463450792208155938632601749290300230771/10000000000000000000000000000000000000000) (344022635508556866394991084955099903/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0027.bracket0441 BracketBatch0027.bracket0442
  (1463450792208155938632601749290300230771/10000000000000000000000000000000000000000) (344022635508556866394991084955099903/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0441
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0442
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0069.rows BesselBatch0069.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0069.rows BesselBatch0069.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0069.rows BesselBatch0069.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0069.rows BesselBatch0069.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0069.rows BesselBatch0069.accepted ⟨8,by decide⟩
]
theorem leftAccepted : besselPointCheck (732241592446030621051958409910032818397/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (732241592446030621051958409910032818397/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0069.rows BesselBatch0069.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0069.rows BesselBatch0069.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0069.rows BesselBatch0069.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0069.rows BesselBatch0069.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0069.rows BesselBatch0069.accepted ⟨23,by decide⟩
]
theorem rightAccepted : besselPointCheck (1466548154721601751360317212763738208129/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1466548154721601751360317212763738208129/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0523.rows BesselBatch0523.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0523.rows BesselBatch0523.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0523.rows BesselBatch0523.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0523.rows BesselBatch0523.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0523.rows BesselBatch0523.accepted ⟨32,by decide⟩
]
theorem midAccepted : besselPointCheck (2931031339613662993464234032583803844923/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (2931031339613662993464234032583803844923/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0055.rows ScalarLogs0055.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0055.rows ScalarLogs0055.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0055.rows ScalarLogs0055.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0055.rows ScalarLogs0055.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0055.rows ScalarLogs0055.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0055.rows ScalarLogs0055.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0055.rows ScalarLogs0055.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0055.rows ScalarLogs0055.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0055.rows ScalarLogs0055.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0055.rows ScalarLogs0055.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0055.rows ScalarLogs0055.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0055.rows ScalarLogs0055.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0055.rows ScalarLogs0055.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0055.rows ScalarLogs0055.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0055.rows ScalarLogs0055.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0055.rows ScalarLogs0055.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0027.bracket0442 BracketBatch0027.bracket0443 (2931031339613662993464234032583803844923/20000000000000000000000000000000000000000) (345939047063782234579713003636401369/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0027.bracket0442 BracketBatch0027.bracket0443
  (2931031339613662993464234032583803844923/20000000000000000000000000000000000000000) (345939047063782234579713003636401369/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0442
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0443
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0069.rows BesselBatch0069.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0069.rows BesselBatch0069.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0069.rows BesselBatch0069.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0069.rows BesselBatch0069.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0069.rows BesselBatch0069.accepted ⟨18,by decide⟩
]
theorem leftAccepted : besselPointCheck (733274077360800875680158606381869104063/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (733274077360800875680158606381869104063/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0069.rows BesselBatch0069.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0069.rows BesselBatch0069.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0069.rows BesselBatch0069.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0069.rows BesselBatch0069.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0069.rows BesselBatch0069.accepted ⟨33,by decide⟩
]
theorem rightAccepted : besselPointCheck (734306654649008635640618128112779949977/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (734306654649008635640618128112779949977/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0523.rows BesselBatch0523.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0523.rows BesselBatch0523.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0523.rows BesselBatch0523.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0523.rows BesselBatch0523.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0523.rows BesselBatch0523.accepted ⟨37,by decide⟩
]
theorem midAccepted : besselPointCheck (36689518300245237783019418362366226351/250000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (36689518300245237783019418362366226351/250000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0055.rows ScalarLogs0055.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0055.rows ScalarLogs0055.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0055.rows ScalarLogs0055.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0055.rows ScalarLogs0055.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0055.rows ScalarLogs0055.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0055.rows ScalarLogs0055.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0055.rows ScalarLogs0055.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0055.rows ScalarLogs0055.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0055.rows ScalarLogs0055.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0055.rows ScalarLogs0055.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0055.rows ScalarLogs0055.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0055.rows ScalarLogs0055.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0055.rows ScalarLogs0055.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0055.rows ScalarLogs0055.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0055.rows ScalarLogs0055.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0055.rows ScalarLogs0055.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0027.bracket0443 BracketBatch0027.bracket0444 (36689518300245237783019418362366226351/250000000000000000000000000000000000000) (86965869785882211413116344845769117/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0027.bracket0443 BracketBatch0027.bracket0444
  (36689518300245237783019418362366226351/250000000000000000000000000000000000000) (86965869785882211413116344845769117/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0443
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0444
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0069.rows BesselBatch0069.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0069.rows BesselBatch0069.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0069.rows BesselBatch0069.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0069.rows BesselBatch0069.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0069.rows BesselBatch0069.accepted ⟨28,by decide⟩
]
theorem leftAccepted : besselPointCheck (1468613309298017271281236256225559899951/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1468613309298017271281236256225559899951/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0069.rows BesselBatch0069.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0069.rows BesselBatch0069.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0069.rows BesselBatch0069.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0069.rows BesselBatch0069.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0069.rows BesselBatch0069.accepted ⟨43,by decide⟩
]
theorem rightAccepted : besselPointCheck (91917415556661659527557538946046867871/625000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (91917415556661659527557538946046867871/625000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0523.rows BesselBatch0523.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0523.rows BesselBatch0523.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0523.rows BesselBatch0523.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0523.rows BesselBatch0523.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0523.rows BesselBatch0523.accepted ⟨42,by decide⟩
]
theorem midAccepted : besselPointCheck (2939291958204603823722156879362309785887/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (2939291958204603823722156879362309785887/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0055.rows ScalarLogs0055.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0055.rows ScalarLogs0055.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0055.rows ScalarLogs0055.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0055.rows ScalarLogs0055.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0055.rows ScalarLogs0055.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0055.rows ScalarLogs0055.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0055.rows ScalarLogs0055.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0055.rows ScalarLogs0055.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0055.rows ScalarLogs0055.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0055.rows ScalarLogs0055.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0055.rows ScalarLogs0055.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0055.rows ScalarLogs0055.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0055.rows ScalarLogs0055.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0055.rows ScalarLogs0055.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0055.rows ScalarLogs0055.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0055.rows ScalarLogs0055.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0027.bracket0444 BracketBatch0027.bracket0445 (2939291958204603823722156879362309785887/20000000000000000000000000000000000000000) (174897977191388248381608940918643541/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0027.bracket0444 BracketBatch0027.bracket0445
  (2939291958204603823722156879362309785887/20000000000000000000000000000000000000000) (174897977191388248381608940918643541/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0444
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0445
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0069.rows BesselBatch0069.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0069.rows BesselBatch0069.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0069.rows BesselBatch0069.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0069.rows BesselBatch0069.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0069.rows BesselBatch0069.accepted ⟨38,by decide⟩
]
theorem leftAccepted : besselPointCheck (1470678648906586552440920623136749885933/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1470678648906586552440920623136749885933/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0069.rows BesselBatch0069.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0069.rows BesselBatch0069.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0069.rows BesselBatch0069.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0069.rows BesselBatch0069.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0069.rows BesselBatch0069.accepted ⟨53,by decide⟩
]
theorem rightAccepted : besselPointCheck (1472744173832722224201966315860320254797/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1472744173832722224201966315860320254797/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0523.rows BesselBatch0523.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0523.rows BesselBatch0523.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0523.rows BesselBatch0523.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0523.rows BesselBatch0523.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0523.rows BesselBatch0523.accepted ⟨47,by decide⟩
]
theorem midAccepted : besselPointCheck (294342282273930877664288693899707014073/2000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (294342282273930877664288693899707014073/2000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0055.rows ScalarLogs0055.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0055.rows ScalarLogs0055.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0055.rows ScalarLogs0055.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0055.rows ScalarLogs0055.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0055.rows ScalarLogs0055.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0055.rows ScalarLogs0055.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0055.rows ScalarLogs0055.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0055.rows ScalarLogs0055.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0055.rows ScalarLogs0055.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0055.rows ScalarLogs0055.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0055.rows ScalarLogs0055.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0055.rows ScalarLogs0055.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0055.rows ScalarLogs0055.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0055.rows ScalarLogs0055.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0055.rows ScalarLogs0055.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0055.rows ScalarLogs0055.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0027.bracket0445 BracketBatch0027.bracket0446 (294342282273930877664288693899707014073/2000000000000000000000000000000000000000) (35173649545042792366634926754149911/1000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0027.bracket0445 BracketBatch0027.bracket0446
  (294342282273930877664288693899707014073/2000000000000000000000000000000000000000) (35173649545042792366634926754149911/1000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0445
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0446
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0069.rows BesselBatch0069.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0069.rows BesselBatch0069.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0069.rows BesselBatch0069.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0069.rows BesselBatch0069.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0069.rows BesselBatch0069.accepted ⟨48,by decide⟩
]
theorem leftAccepted : besselPointCheck (736372086916361112100983157930160127397/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (736372086916361112100983157930160127397/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0069.rows BesselBatch0069.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0069.rows BesselBatch0069.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0069.rows BesselBatch0069.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0069.rows BesselBatch0069.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0069.rows BesselBatch0069.accepted ⟨63,by decide⟩
]
theorem rightAccepted : besselPointCheck (1474809884361971031518994480023864911053/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1474809884361971031518994480023864911053/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0523.rows BesselBatch0523.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0523.rows BesselBatch0523.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0523.rows BesselBatch0523.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0523.rows BesselBatch0523.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0523.rows BesselBatch0523.accepted ⟨52,by decide⟩
]
theorem midAccepted : besselPointCheck (2947554058194693255720960795884185165847/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (2947554058194693255720960795884185165847/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0055.rows ScalarLogs0055.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0055.rows ScalarLogs0055.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0055.rows ScalarLogs0055.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0055.rows ScalarLogs0055.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0055.rows ScalarLogs0055.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0055.rows ScalarLogs0055.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0055.rows ScalarLogs0055.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0055.rows ScalarLogs0055.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0055.rows ScalarLogs0055.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0055.rows ScalarLogs0055.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0055.rows ScalarLogs0055.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0055.rows ScalarLogs0055.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0055.rows ScalarLogs0055.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0055.rows ScalarLogs0055.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0055.rows ScalarLogs0055.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0055.rows ScalarLogs0055.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0027.bracket0446 BracketBatch0027.bracket0447 (2947554058194693255720960795884185165847/20000000000000000000000000000000000000000) (88421281262330124524911679875247953/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0027.bracket0446 BracketBatch0027.bracket0447
  (2947554058194693255720960795884185165847/20000000000000000000000000000000000000000) (88421281262330124524911679875247953/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0446
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0447
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0069.rows BesselBatch0069.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0069.rows BesselBatch0069.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0069.rows BesselBatch0069.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0069.rows BesselBatch0069.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0069.rows BesselBatch0069.accepted ⟨58,by decide⟩
]
theorem leftAccepted : besselPointCheck (29496197687239420630379889600477298221/200000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (29496197687239420630379889600477298221/200000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0070.rows BesselBatch0070.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0070.rows BesselBatch0070.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0070.rows BesselBatch0070.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0070.rows BesselBatch0070.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0070.rows BesselBatch0070.accepted ⟨9,by decide⟩
]
theorem rightAccepted : besselPointCheck (1476875780780014071981646209933991205803/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1476875780780014071981646209933991205803/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0523.rows BesselBatch0523.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0523.rows BesselBatch0523.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0523.rows BesselBatch0523.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0523.rows BesselBatch0523.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0523.rows BesselBatch0523.accepted ⟨57,by decide⟩
]
theorem midAccepted : besselPointCheck (2951685665141985103500640689957856116853/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (2951685665141985103500640689957856116853/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0055.rows ScalarLogs0055.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0055.rows ScalarLogs0055.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0055.rows ScalarLogs0055.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0055.rows ScalarLogs0055.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0055.rows ScalarLogs0055.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0055.rows ScalarLogs0055.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0055.rows ScalarLogs0055.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0055.rows ScalarLogs0055.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0055.rows ScalarLogs0055.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0055.rows ScalarLogs0055.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0055.rows ScalarLogs0055.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0055.rows ScalarLogs0055.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0055.rows ScalarLogs0055.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0055.rows ScalarLogs0055.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0055.rows ScalarLogs0055.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0055.rows ScalarLogs0055.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0027.bracket0447 BracketBatch0028.bracket0448 (2951685665141985103500640689957856116853/20000000000000000000000000000000000000000) (14225674636649517802474657429721803/400000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0027.bracket0447 BracketBatch0028.bracket0448
  (2951685665141985103500640689957856116853/20000000000000000000000000000000000000000) (14225674636649517802474657429721803/400000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0447
