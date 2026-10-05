import BecknerOnofri.EntropyScalarCertificate.Bessel0282
import BecknerOnofri.EntropyScalarCertificate.Bessel0283
import BecknerOnofri.EntropyScalarCertificate.Bessel0630
import BecknerOnofri.EntropyScalarCertificate.Brackets0113
import BecknerOnofri.EntropyScalarCertificate.Logs0226
import BecknerOnofri.ScalarElementaryComposition
import BecknerOnofri.ScalarGammaEnclosure
import BecknerOnofri.ScalarLogBesselEndpoints
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1808
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0282.rows BesselBatch0282.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0282.rows BesselBatch0282.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0282.rows BesselBatch0282.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0282.rows BesselBatch0282.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0282.rows BesselBatch0282.accepted ⟨36,by decide⟩
]
theorem leftAccepted : besselPointCheck (21326371689653593054170338114511370756933/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (21326371689653593054170338114511370756933/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0282.rows BesselBatch0282.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0282.rows BesselBatch0282.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0282.rows BesselBatch0282.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0282.rows BesselBatch0282.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0282.rows BesselBatch0282.accepted ⟨51,by decide⟩
]
theorem rightAccepted : besselPointCheck (4268289283820195507336971942748960054577/2000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (4268289283820195507336971942748960054577/2000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0630.rows BesselBatch0630.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0630.rows BesselBatch0630.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0630.rows BesselBatch0630.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0630.rows BesselBatch0630.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0630.rows BesselBatch0630.accepted ⟨14,by decide⟩
]
theorem midAccepted : besselPointCheck (21333909054377285295427598914128085514909/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (21333909054377285295427598914128085514909/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0226.rows ScalarLogs0226.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0226.rows ScalarLogs0226.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0226.rows ScalarLogs0226.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0226.rows ScalarLogs0226.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0226.rows ScalarLogs0226.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0226.rows ScalarLogs0226.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0226.rows ScalarLogs0226.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0226.rows ScalarLogs0226.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0226.rows ScalarLogs0226.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0226.rows ScalarLogs0226.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0226.rows ScalarLogs0226.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0226.rows ScalarLogs0226.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0226.rows ScalarLogs0226.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0226.rows ScalarLogs0226.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0226.rows ScalarLogs0226.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0226.rows ScalarLogs0226.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0113.bracket1808 BracketBatch0113.bracket1809 (21333909054377285295427598914128085514909/10000000000000000000000000000000000000000) (868099285011694028920535278193762465519/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0113.bracket1808 BracketBatch0113.bracket1809
  (21333909054377285295427598914128085514909/10000000000000000000000000000000000000000) (868099285011694028920535278193762465519/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1808
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1809
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0282.rows BesselBatch0282.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0282.rows BesselBatch0282.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0282.rows BesselBatch0282.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0282.rows BesselBatch0282.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0282.rows BesselBatch0282.accepted ⟨46,by decide⟩
]
theorem leftAccepted : besselPointCheck (10670723209550488768342429856872400136441/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (10670723209550488768342429856872400136441/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0282.rows BesselBatch0282.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0282.rows BesselBatch0282.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0282.rows BesselBatch0282.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0282.rows BesselBatch0282.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0282.rows BesselBatch0282.accepted ⟨61,by decide⟩
]
theorem rightAccepted : besselPointCheck (10678272738602955049545718255005350145331/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (10678272738602955049545718255005350145331/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0630.rows BesselBatch0630.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0630.rows BesselBatch0630.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0630.rows BesselBatch0630.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0630.rows BesselBatch0630.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0630.rows BesselBatch0630.accepted ⟨19,by decide⟩
]
theorem midAccepted : besselPointCheck (5337248987038360954472037027969437570443/2500000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (5337248987038360954472037027969437570443/2500000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0226.rows ScalarLogs0226.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0226.rows ScalarLogs0226.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0226.rows ScalarLogs0226.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0226.rows ScalarLogs0226.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0226.rows ScalarLogs0226.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0226.rows ScalarLogs0226.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0226.rows ScalarLogs0226.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0226.rows ScalarLogs0226.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0226.rows ScalarLogs0226.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0226.rows ScalarLogs0226.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0226.rows ScalarLogs0226.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0226.rows ScalarLogs0226.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0226.rows ScalarLogs0226.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0226.rows ScalarLogs0226.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0226.rows ScalarLogs0226.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0226.rows ScalarLogs0226.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0113.bracket1809 BracketBatch0113.bracket1810 (5337248987038360954472037027969437570443/2500000000000000000000000000000000000000) (434421532933326006214782885843593892873/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0113.bracket1809 BracketBatch0113.bracket1810
  (5337248987038360954472037027969437570443/2500000000000000000000000000000000000000) (434421532933326006214782885843593892873/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1809
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1810
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0282.rows BesselBatch0282.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0282.rows BesselBatch0282.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0282.rows BesselBatch0282.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0282.rows BesselBatch0282.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0282.rows BesselBatch0282.accepted ⟨56,by decide⟩
]
theorem leftAccepted : besselPointCheck (21356545477205910099091436510010700290659/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (21356545477205910099091436510010700290659/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0283.rows BesselBatch0283.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0283.rows BesselBatch0283.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0283.rows BesselBatch0283.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0283.rows BesselBatch0283.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0283.rows BesselBatch0283.accepted ⟨7,by decide⟩
]
theorem rightAccepted : besselPointCheck (854866756938734145422275482093722335259/400000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (854866756938734145422275482093722335259/400000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0630.rows BesselBatch0630.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0630.rows BesselBatch0630.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0630.rows BesselBatch0630.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0630.rows BesselBatch0630.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0630.rows BesselBatch0630.accepted ⟨24,by decide⟩
]
theorem midAccepted : besselPointCheck (21364107200337131867324161781176879336067/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (21364107200337131867324161781176879336067/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0226.rows ScalarLogs0226.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0226.rows ScalarLogs0226.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0226.rows ScalarLogs0226.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0226.rows ScalarLogs0226.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0226.rows ScalarLogs0226.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0226.rows ScalarLogs0226.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0226.rows ScalarLogs0226.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0226.rows ScalarLogs0226.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0226.rows ScalarLogs0226.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0226.rows ScalarLogs0226.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0226.rows ScalarLogs0226.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0226.rows ScalarLogs0226.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0226.rows ScalarLogs0226.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0226.rows ScalarLogs0226.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0226.rows ScalarLogs0226.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0226.rows ScalarLogs0226.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0113.bracket1810 BracketBatch0113.bracket1811 (21364107200337131867324161781176879336067/10000000000000000000000000000000000000000) (217396934853850831677890655813260212503/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0113.bracket1810 BracketBatch0113.bracket1811
  (21364107200337131867324161781176879336067/10000000000000000000000000000000000000000) (217396934853850831677890655813260212503/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1810
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1811
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0282.rows BesselBatch0282.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0282.rows BesselBatch0282.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0283.rows BesselBatch0283.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0283.rows BesselBatch0283.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0283.rows BesselBatch0283.accepted ⟨2,by decide⟩
]
theorem leftAccepted : besselPointCheck (667864653858386051111152720385720574421/312500000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (667864653858386051111152720385720574421/312500000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0283.rows BesselBatch0283.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0283.rows BesselBatch0283.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0283.rows BesselBatch0283.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0283.rows BesselBatch0283.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0283.rows BesselBatch0283.accepted ⟨17,by decide⟩
]
theorem rightAccepted : besselPointCheck (5346704204393337136316166279844762154063/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (5346704204393337136316166279844762154063/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0630.rows BesselBatch0630.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0630.rows BesselBatch0630.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0630.rows BesselBatch0630.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0630.rows BesselBatch0630.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0630.rows BesselBatch0630.accepted ⟨29,by decide⟩
]
theorem midAccepted : besselPointCheck (10689621435260425545205388042930526749431/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (10689621435260425545205388042930526749431/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0226.rows ScalarLogs0226.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0226.rows ScalarLogs0226.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0226.rows ScalarLogs0226.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0226.rows ScalarLogs0226.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0226.rows ScalarLogs0226.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0226.rows ScalarLogs0226.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0226.rows ScalarLogs0226.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0226.rows ScalarLogs0226.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0226.rows ScalarLogs0226.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0226.rows ScalarLogs0226.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0226.rows ScalarLogs0226.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0226.rows ScalarLogs0226.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0226.rows ScalarLogs0226.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0226.rows ScalarLogs0226.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0226.rows ScalarLogs0226.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0226.rows ScalarLogs0226.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0113.bracket1811 BracketBatch0113.bracket1812 (10689621435260425545205388042930526749431/5000000000000000000000000000000000000000) (870333307152241292707537256828571222371/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0113.bracket1811 BracketBatch0113.bracket1812
  (10689621435260425545205388042930526749431/5000000000000000000000000000000000000000) (870333307152241292707537256828571222371/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1811
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1812
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0283.rows BesselBatch0283.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0283.rows BesselBatch0283.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0283.rows BesselBatch0283.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0283.rows BesselBatch0283.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0283.rows BesselBatch0283.accepted ⟨12,by decide⟩
]
theorem leftAccepted : besselPointCheck (21386816817573348545264665119379048616249/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (21386816817573348545264665119379048616249/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0283.rows BesselBatch0283.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0283.rows BesselBatch0283.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0283.rows BesselBatch0283.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0283.rows BesselBatch0283.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0283.rows BesselBatch0283.accepted ⟨27,by decide⟩
]
theorem rightAccepted : besselPointCheck (21401989219391719826333871801767710307159/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (21401989219391719826333871801767710307159/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0630.rows BesselBatch0630.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0630.rows BesselBatch0630.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0630.rows BesselBatch0630.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0630.rows BesselBatch0630.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0630.rows BesselBatch0630.accepted ⟨34,by decide⟩
]
theorem midAccepted : besselPointCheck (2674300377310316773224908557571672432713/1250000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (2674300377310316773224908557571672432713/1250000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0226.rows ScalarLogs0226.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0226.rows ScalarLogs0226.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0226.rows ScalarLogs0226.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0226.rows ScalarLogs0226.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0226.rows ScalarLogs0226.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0226.rows ScalarLogs0226.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0226.rows ScalarLogs0226.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0226.rows ScalarLogs0226.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0226.rows ScalarLogs0226.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0226.rows ScalarLogs0226.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0226.rows ScalarLogs0226.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0226.rows ScalarLogs0226.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0226.rows ScalarLogs0226.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0226.rows ScalarLogs0226.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0226.rows ScalarLogs0226.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0226.rows ScalarLogs0226.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0113.bracket1812 BracketBatch0113.bracket1813 (2674300377310316773224908557571672432713/1250000000000000000000000000000000000000) (850663838451619173676618675293992521/9765625000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0113.bracket1812 BracketBatch0113.bracket1813
  (2674300377310316773224908557571672432713/1250000000000000000000000000000000000000) (850663838451619173676618675293992521/9765625000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1812
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1813
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0283.rows BesselBatch0283.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0283.rows BesselBatch0283.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0283.rows BesselBatch0283.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0283.rows BesselBatch0283.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0283.rows BesselBatch0283.accepted ⟨22,by decide⟩
]
theorem leftAccepted : besselPointCheck (5350497304847929956583467950441927576789/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (5350497304847929956583467950441927576789/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0283.rows BesselBatch0283.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0283.rows BesselBatch0283.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0283.rows BesselBatch0283.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0283.rows BesselBatch0283.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0283.rows BesselBatch0283.accepted ⟨37,by decide⟩
]
theorem rightAccepted : besselPointCheck (10708593094490393744539463411520809479631/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (10708593094490393744539463411520809479631/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0630.rows BesselBatch0630.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0630.rows BesselBatch0630.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0630.rows BesselBatch0630.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0630.rows BesselBatch0630.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0630.rows BesselBatch0630.accepted ⟨39,by decide⟩
]
theorem midAccepted : besselPointCheck (21409587704186253657706399312404664633209/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (21409587704186253657706399312404664633209/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0226.rows ScalarLogs0226.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0226.rows ScalarLogs0226.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0226.rows ScalarLogs0226.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0226.rows ScalarLogs0226.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0226.rows ScalarLogs0226.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0226.rows ScalarLogs0226.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0226.rows ScalarLogs0226.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0226.rows ScalarLogs0226.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0226.rows ScalarLogs0226.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0226.rows ScalarLogs0226.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0226.rows ScalarLogs0226.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0226.rows ScalarLogs0226.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0226.rows ScalarLogs0226.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0226.rows ScalarLogs0226.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0226.rows ScalarLogs0226.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0226.rows ScalarLogs0226.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0113.bracket1813 BracketBatch0113.bracket1814 (21409587704186253657706399312404664633209/10000000000000000000000000000000000000000) (871827131182352071025667930118705596661/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0113.bracket1813 BracketBatch0113.bracket1814
  (21409587704186253657706399312404664633209/10000000000000000000000000000000000000000) (871827131182352071025667930118705596661/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1813
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1814
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0283.rows BesselBatch0283.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0283.rows BesselBatch0283.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0283.rows BesselBatch0283.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0283.rows BesselBatch0283.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0283.rows BesselBatch0283.accepted ⟨32,by decide⟩
]
theorem leftAccepted : besselPointCheck (21417186188980787489078926823041618959259/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (21417186188980787489078926823041618959259/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0283.rows BesselBatch0283.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0283.rows BesselBatch0283.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0283.rows BesselBatch0283.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0283.rows BesselBatch0283.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0283.rows BesselBatch0283.accepted ⟨47,by decide⟩
]
theorem rightAccepted : besselPointCheck (1071620389329254015376252286798505556561/500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1071620389329254015376252286798505556561/500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0630.rows BesselBatch0630.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0630.rows BesselBatch0630.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0630.rows BesselBatch0630.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0630.rows BesselBatch0630.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0630.rows BesselBatch0630.accepted ⟨44,by decide⟩
]
theorem midAccepted : besselPointCheck (42849593975565867796603972559011730090479/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (42849593975565867796603972559011730090479/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0226.rows ScalarLogs0226.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0226.rows ScalarLogs0226.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0226.rows ScalarLogs0226.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0226.rows ScalarLogs0226.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0226.rows ScalarLogs0226.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0226.rows ScalarLogs0226.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0226.rows ScalarLogs0226.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0226.rows ScalarLogs0226.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0226.rows ScalarLogs0226.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0226.rows ScalarLogs0226.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0226.rows ScalarLogs0226.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0226.rows ScalarLogs0226.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0226.rows ScalarLogs0226.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0226.rows ScalarLogs0226.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0226.rows ScalarLogs0226.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0226.rows ScalarLogs0226.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0113.bracket1814 BracketBatch0113.bracket1815 (42849593975565867796603972559011730090479/20000000000000000000000000000000000000000) (3490301561916943801943830418660910459/40000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0113.bracket1814 BracketBatch0113.bracket1815
  (42849593975565867796603972559011730090479/20000000000000000000000000000000000000000) (3490301561916943801943830418660910459/40000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1814
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1815
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0283.rows BesselBatch0283.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0283.rows BesselBatch0283.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0283.rows BesselBatch0283.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0283.rows BesselBatch0283.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0283.rows BesselBatch0283.accepted ⟨42,by decide⟩
]
theorem leftAccepted : besselPointCheck (21432407786585080307525045735970111131217/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (21432407786585080307525045735970111131217/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0283.rows BesselBatch0283.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0283.rows BesselBatch0283.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0283.rows BesselBatch0283.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0283.rows BesselBatch0283.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0283.rows BesselBatch0283.accepted ⟨57,by decide⟩
]
theorem rightAccepted : besselPointCheck (21447654072637052928219640249543794337613/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (21447654072637052928219640249543794337613/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0630.rows BesselBatch0630.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0630.rows BesselBatch0630.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0630.rows BesselBatch0630.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0630.rows BesselBatch0630.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0630.rows BesselBatch0630.accepted ⟨49,by decide⟩
]
theorem midAccepted : besselPointCheck (4288006185922213323574468598551390546883/2000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (4288006185922213323574468598551390546883/2000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0226.rows ScalarLogs0226.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0226.rows ScalarLogs0226.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0226.rows ScalarLogs0226.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0226.rows ScalarLogs0226.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0226.rows ScalarLogs0226.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0226.rows ScalarLogs0226.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0226.rows ScalarLogs0226.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0226.rows ScalarLogs0226.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0226.rows ScalarLogs0226.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0226.rows ScalarLogs0226.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0226.rows ScalarLogs0226.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0226.rows ScalarLogs0226.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0226.rows ScalarLogs0226.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0226.rows ScalarLogs0226.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0226.rows ScalarLogs0226.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0226.rows ScalarLogs0226.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0113.bracket1815 BracketBatch0113.bracket1816 (4288006185922213323574468598551390546883/2000000000000000000000000000000000000000) (873324549971443904745780831845771477621/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0113.bracket1815 BracketBatch0113.bracket1816
  (4288006185922213323574468598551390546883/2000000000000000000000000000000000000000) (873324549971443904745780831845771477621/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1815
