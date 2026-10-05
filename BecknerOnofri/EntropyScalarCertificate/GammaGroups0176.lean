import BecknerOnofri.EntropyScalarCertificate.Bessel0220
import BecknerOnofri.EntropyScalarCertificate.Bessel0221
import BecknerOnofri.EntropyScalarCertificate.Bessel0598
import BecknerOnofri.EntropyScalarCertificate.Bessel0599
import BecknerOnofri.EntropyScalarCertificate.Brackets0088
import BecknerOnofri.EntropyScalarCertificate.Logs0176
import BecknerOnofri.ScalarElementaryComposition
import BecknerOnofri.ScalarGammaEnclosure
import BecknerOnofri.ScalarLogBesselEndpoints
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1408
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0220.rows BesselBatch0220.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0220.rows BesselBatch0220.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0220.rows BesselBatch0220.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0220.rows BesselBatch0220.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0220.rows BesselBatch0220.accepted ⟨4,by decide⟩
]
theorem leftAccepted : besselPointCheck (67045969358724374733920485096783552497/40000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (67045969358724374733920485096783552497/40000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0220.rows BesselBatch0220.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0220.rows BesselBatch0220.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0220.rows BesselBatch0220.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0220.rows BesselBatch0220.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0220.rows BesselBatch0220.accepted ⟨19,by decide⟩
]
theorem rightAccepted : besselPointCheck (83850871355643323831772900855439438247/50000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (83850871355643323831772900855439438247/50000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0598.rows BesselBatch0598.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0598.rows BesselBatch0598.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0598.rows BesselBatch0598.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0598.rows BesselBatch0598.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0598.rows BesselBatch0598.accepted ⟨62,by decide⟩
]
theorem midAccepted : besselPointCheck (670633332216195168996694028905675515473/400000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (670633332216195168996694028905675515473/400000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0176.rows ScalarLogs0176.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0176.rows ScalarLogs0176.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0176.rows ScalarLogs0176.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0176.rows ScalarLogs0176.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0176.rows ScalarLogs0176.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0176.rows ScalarLogs0176.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0176.rows ScalarLogs0176.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0176.rows ScalarLogs0176.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0176.rows ScalarLogs0176.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0176.rows ScalarLogs0176.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0176.rows ScalarLogs0176.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0176.rows ScalarLogs0176.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0176.rows ScalarLogs0176.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0176.rows ScalarLogs0176.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0176.rows ScalarLogs0176.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0176.rows ScalarLogs0176.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0088.bracket1408 BracketBatch0088.bracket1409 (670633332216195168996694028905675515473/400000000000000000000000000000000000000) (628843789468537721162062952822801759499/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0088.bracket1408 BracketBatch0088.bracket1409
  (670633332216195168996694028905675515473/400000000000000000000000000000000000000) (628843789468537721162062952822801759499/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1408
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1409
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0220.rows BesselBatch0220.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0220.rows BesselBatch0220.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0220.rows BesselBatch0220.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0220.rows BesselBatch0220.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0220.rows BesselBatch0220.accepted ⟨14,by decide⟩
]
theorem leftAccepted : besselPointCheck (16770174271128664766354580171087887649397/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (16770174271128664766354580171087887649397/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0220.rows BesselBatch0220.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0220.rows BesselBatch0220.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0220.rows BesselBatch0220.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0220.rows BesselBatch0220.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0220.rows BesselBatch0220.accepted ⟨29,by decide⟩
]
theorem rightAccepted : besselPointCheck (4194716607721273751308723256989200401073/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (4194716607721273751308723256989200401073/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0598.rows BesselBatch0598.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0599.rows BesselBatch0599.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0599.rows BesselBatch0599.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0599.rows BesselBatch0599.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0599.rows BesselBatch0599.accepted ⟨3,by decide⟩
]
theorem midAccepted : besselPointCheck (33549040702013759771589473199044689253689/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (33549040702013759771589473199044689253689/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0176.rows ScalarLogs0176.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0176.rows ScalarLogs0176.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0176.rows ScalarLogs0176.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0176.rows ScalarLogs0176.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0176.rows ScalarLogs0176.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0176.rows ScalarLogs0176.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0176.rows ScalarLogs0176.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0176.rows ScalarLogs0176.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0176.rows ScalarLogs0176.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0176.rows ScalarLogs0176.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0176.rows ScalarLogs0176.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0176.rows ScalarLogs0176.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0176.rows ScalarLogs0176.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0176.rows ScalarLogs0176.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0176.rows ScalarLogs0176.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0176.rows ScalarLogs0176.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0088.bracket1409 BracketBatch0088.bracket1410 (33549040702013759771589473199044689253689/20000000000000000000000000000000000000000) (125864872655273845820805183609819389673/2000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0088.bracket1409 BracketBatch0088.bracket1410
  (33549040702013759771589473199044689253689/20000000000000000000000000000000000000000) (125864872655273845820805183609819389673/2000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1409
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1410
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0220.rows BesselBatch0220.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0220.rows BesselBatch0220.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0220.rows BesselBatch0220.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0220.rows BesselBatch0220.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0220.rows BesselBatch0220.accepted ⟨24,by decide⟩
]
theorem leftAccepted : besselPointCheck (16778866430885095005234893027956801604289/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (16778866430885095005234893027956801604289/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0220.rows BesselBatch0220.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0220.rows BesselBatch0220.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0220.rows BesselBatch0220.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0220.rows BesselBatch0220.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0220.rows BesselBatch0220.accepted ⟨39,by decide⟩
]
theorem rightAccepted : besselPointCheck (839378441933569084078675514842530158469/500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (839378441933569084078675514842530158469/500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0599.rows BesselBatch0599.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0599.rows BesselBatch0599.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0599.rows BesselBatch0599.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0599.rows BesselBatch0599.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0599.rows BesselBatch0599.accepted ⟨8,by decide⟩
]
theorem midAccepted : besselPointCheck (33566435269556476686808403324807404773669/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (33566435269556476686808403324807404773669/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0176.rows ScalarLogs0176.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0176.rows ScalarLogs0176.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0176.rows ScalarLogs0176.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0176.rows ScalarLogs0176.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0176.rows ScalarLogs0176.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0176.rows ScalarLogs0176.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0176.rows ScalarLogs0176.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0176.rows ScalarLogs0176.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0176.rows ScalarLogs0176.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0176.rows ScalarLogs0176.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0176.rows ScalarLogs0176.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0176.rows ScalarLogs0176.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0176.rows ScalarLogs0176.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0176.rows ScalarLogs0176.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0176.rows ScalarLogs0176.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0176.rows ScalarLogs0176.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0088.bracket1410 BracketBatch0088.bracket1411 (33566435269556476686808403324807404773669/20000000000000000000000000000000000000000) (125961082758410350271967929413215565953/2000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0088.bracket1410 BracketBatch0088.bracket1411
  (33566435269556476686808403324807404773669/20000000000000000000000000000000000000000) (125961082758410350271967929413215565953/2000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1410
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1411
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0220.rows BesselBatch0220.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0220.rows BesselBatch0220.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0220.rows BesselBatch0220.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0220.rows BesselBatch0220.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0220.rows BesselBatch0220.accepted ⟨34,by decide⟩
]
theorem leftAccepted : besselPointCheck (16787568838671381681573510296850603169377/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (16787568838671381681573510296850603169377/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0220.rows BesselBatch0220.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0220.rows BesselBatch0220.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0220.rows BesselBatch0220.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0220.rows BesselBatch0220.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0220.rows BesselBatch0220.accepted ⟨49,by decide⟩
]
theorem rightAccepted : besselPointCheck (16796281514257515810152594074231324946607/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (16796281514257515810152594074231324946607/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0599.rows BesselBatch0599.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0599.rows BesselBatch0599.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0599.rows BesselBatch0599.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0599.rows BesselBatch0599.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0599.rows BesselBatch0599.accepted ⟨13,by decide⟩
]
theorem midAccepted : besselPointCheck (2098990647058056093232881523192620507249/1250000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (2098990647058056093232881523192620507249/1250000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0176.rows ScalarLogs0176.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0176.rows ScalarLogs0176.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0176.rows ScalarLogs0176.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0176.rows ScalarLogs0176.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0176.rows ScalarLogs0176.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0176.rows ScalarLogs0176.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0176.rows ScalarLogs0176.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0176.rows ScalarLogs0176.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0176.rows ScalarLogs0176.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0176.rows ScalarLogs0176.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0176.rows ScalarLogs0176.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0176.rows ScalarLogs0176.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0176.rows ScalarLogs0176.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0176.rows ScalarLogs0176.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0176.rows ScalarLogs0176.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0176.rows ScalarLogs0176.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0088.bracket1411 BracketBatch0088.bracket1412 (2098990647058056093232881523192620507249/1250000000000000000000000000000000000000) (63028694171258776851225600029296220647/1000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0088.bracket1411 BracketBatch0088.bracket1412
  (2098990647058056093232881523192620507249/1250000000000000000000000000000000000000) (63028694171258776851225600029296220647/1000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1411
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1412
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0220.rows BesselBatch0220.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0220.rows BesselBatch0220.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0220.rows BesselBatch0220.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0220.rows BesselBatch0220.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0220.rows BesselBatch0220.accepted ⟨44,by decide⟩
]
theorem leftAccepted : besselPointCheck (4199070378564378952538148518557831236651/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (4199070378564378952538148518557831236651/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0220.rows BesselBatch0220.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0220.rows BesselBatch0220.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0220.rows BesselBatch0220.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0220.rows BesselBatch0220.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0220.rows BesselBatch0220.accepted ⟨59,by decide⟩
]
theorem rightAccepted : besselPointCheck (4201251119365656866544034788878653683067/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (4201251119365656866544034788878653683067/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0599.rows BesselBatch0599.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0599.rows BesselBatch0599.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0599.rows BesselBatch0599.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0599.rows BesselBatch0599.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0599.rows BesselBatch0599.accepted ⟨18,by decide⟩
]
theorem midAccepted : besselPointCheck (4200160748965017909541091653718242459859/2500000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (4200160748965017909541091653718242459859/2500000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0176.rows ScalarLogs0176.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0176.rows ScalarLogs0176.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0176.rows ScalarLogs0176.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0176.rows ScalarLogs0176.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0176.rows ScalarLogs0176.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0176.rows ScalarLogs0176.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0176.rows ScalarLogs0176.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0176.rows ScalarLogs0176.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0176.rows ScalarLogs0176.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0176.rows ScalarLogs0176.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0176.rows ScalarLogs0176.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0176.rows ScalarLogs0176.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0176.rows ScalarLogs0176.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0176.rows ScalarLogs0176.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0176.rows ScalarLogs0176.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0176.rows ScalarLogs0176.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0088.bracket1412 BracketBatch0088.bracket1413 (4200160748965017909541091653718242459859/2500000000000000000000000000000000000000) (315384473868137500807512192350487504009/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0088.bracket1412 BracketBatch0088.bracket1413
  (4200160748965017909541091653718242459859/2500000000000000000000000000000000000000) (315384473868137500807512192350487504009/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1412
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1413
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0220.rows BesselBatch0220.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0220.rows BesselBatch0220.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0220.rows BesselBatch0220.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0220.rows BesselBatch0220.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0220.rows BesselBatch0220.accepted ⟨54,by decide⟩
]
theorem leftAccepted : besselPointCheck (3361000895492525493235227831102922946453/2000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (3361000895492525493235227831102922946453/2000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0221.rows BesselBatch0221.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0221.rows BesselBatch0221.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0221.rows BesselBatch0221.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0221.rows BesselBatch0221.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0221.rows BesselBatch0221.accepted ⟨5,by decide⟩
]
theorem rightAccepted : besselPointCheck (105085860925969572570767129156125641523/62500000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (105085860925969572570767129156125641523/62500000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0599.rows BesselBatch0599.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0599.rows BesselBatch0599.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0599.rows BesselBatch0599.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0599.rows BesselBatch0599.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0599.rows BesselBatch0599.accepted ⟨23,by decide⟩
]
theorem midAccepted : besselPointCheck (6723748445123551815499775964098943475189/4000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (6723748445123551815499775964098943475189/4000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0176.rows ScalarLogs0176.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0176.rows ScalarLogs0176.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0176.rows ScalarLogs0176.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0176.rows ScalarLogs0176.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0176.rows ScalarLogs0176.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0176.rows ScalarLogs0176.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0176.rows ScalarLogs0176.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0176.rows ScalarLogs0176.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0176.rows ScalarLogs0176.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0176.rows ScalarLogs0176.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0176.rows ScalarLogs0176.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0176.rows ScalarLogs0176.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0176.rows ScalarLogs0176.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0176.rows ScalarLogs0176.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0176.rows ScalarLogs0176.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0176.rows ScalarLogs0176.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0088.bracket1413 BracketBatch0088.bracket1414 (6723748445123551815499775964098943475189/4000000000000000000000000000000000000000) (631251432562708970391503882097710573127/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0088.bracket1413 BracketBatch0088.bracket1414
  (6723748445123551815499775964098943475189/4000000000000000000000000000000000000000) (631251432562708970391503882097710573127/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1413
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1414
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0220.rows BesselBatch0220.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0220.rows BesselBatch0220.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0220.rows BesselBatch0220.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0220.rows BesselBatch0220.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0221.rows BesselBatch0221.accepted ⟨0,by decide⟩
]
theorem leftAccepted : besselPointCheck (16813737748155131611322740664980102643677/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (16813737748155131611322740664980102643677/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0221.rows BesselBatch0221.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0221.rows BesselBatch0221.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0221.rows BesselBatch0221.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0221.rows BesselBatch0221.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0221.rows BesselBatch0221.accepted ⟨15,by decide⟩
]
theorem rightAccepted : besselPointCheck (16822481346252874420741578746962650453199/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (16822481346252874420741578746962650453199/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0599.rows BesselBatch0599.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0599.rows BesselBatch0599.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0599.rows BesselBatch0599.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0599.rows BesselBatch0599.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0599.rows BesselBatch0599.accepted ⟨28,by decide⟩
]
theorem midAccepted : besselPointCheck (8409054773602001508016079852985688274219/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (8409054773602001508016079852985688274219/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0176.rows ScalarLogs0176.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0176.rows ScalarLogs0176.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0176.rows ScalarLogs0176.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0176.rows ScalarLogs0176.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0176.rows ScalarLogs0176.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0176.rows ScalarLogs0176.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0176.rows ScalarLogs0176.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0176.rows ScalarLogs0176.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0176.rows ScalarLogs0176.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0176.rows ScalarLogs0176.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0176.rows ScalarLogs0176.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0176.rows ScalarLogs0176.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0176.rows ScalarLogs0176.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0176.rows ScalarLogs0176.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0176.rows ScalarLogs0176.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0176.rows ScalarLogs0176.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0088.bracket1414 BracketBatch0088.bracket1415 (8409054773602001508016079852985688274219/5000000000000000000000000000000000000000) (5053875175142284450642653764063462599/80000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0088.bracket1414 BracketBatch0088.bracket1415
  (8409054773602001508016079852985688274219/5000000000000000000000000000000000000000) (5053875175142284450642653764063462599/80000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1414
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1415
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0221.rows BesselBatch0221.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0221.rows BesselBatch0221.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0221.rows BesselBatch0221.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0221.rows BesselBatch0221.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0221.rows BesselBatch0221.accepted ⟨10,by decide⟩
]
theorem leftAccepted : besselPointCheck (4205620336563218605185394686740662613299/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (4205620336563218605185394686740662613299/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0221.rows BesselBatch0221.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0221.rows BesselBatch0221.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0221.rows BesselBatch0221.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0221.rows BesselBatch0221.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0221.rows BesselBatch0221.accepted ⟨25,by decide⟩
]
theorem rightAccepted : besselPointCheck (2103904411465410014122935677740174949053/1250000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (2103904411465410014122935677740174949053/1250000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0599.rows BesselBatch0599.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0599.rows BesselBatch0599.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0599.rows BesselBatch0599.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0599.rows BesselBatch0599.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0599.rows BesselBatch0599.accepted ⟨33,by decide⟩
]
theorem midAccepted : besselPointCheck (1682685831898807726686253208444202502281/1000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1682685831898807726686253208444202502281/1000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0176.rows ScalarLogs0176.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0176.rows ScalarLogs0176.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0176.rows ScalarLogs0176.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0176.rows ScalarLogs0176.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0176.rows ScalarLogs0176.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0176.rows ScalarLogs0176.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0176.rows ScalarLogs0176.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0176.rows ScalarLogs0176.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0176.rows ScalarLogs0176.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0176.rows ScalarLogs0176.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0176.rows ScalarLogs0176.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0176.rows ScalarLogs0176.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0176.rows ScalarLogs0176.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0176.rows ScalarLogs0176.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0176.rows ScalarLogs0176.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0176.rows ScalarLogs0176.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0088.bracket1415 BracketBatch0088.bracket1416 (1682685831898807726686253208444202502281/1000000000000000000000000000000000000000) (632217841428703570689134176873244661293/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0088.bracket1415 BracketBatch0088.bracket1416
  (1682685831898807726686253208444202502281/1000000000000000000000000000000000000000) (632217841428703570689134176873244661293/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1415
