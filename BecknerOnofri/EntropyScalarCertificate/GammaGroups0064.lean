import BecknerOnofri.EntropyScalarCertificate.Bessel0080
import BecknerOnofri.EntropyScalarCertificate.Bessel0081
import BecknerOnofri.EntropyScalarCertificate.Bessel0528
import BecknerOnofri.EntropyScalarCertificate.Bessel0529
import BecknerOnofri.EntropyScalarCertificate.Brackets0032
import BecknerOnofri.EntropyScalarCertificate.Logs0064
import BecknerOnofri.ScalarElementaryComposition
import BecknerOnofri.ScalarGammaEnclosure
import BecknerOnofri.ScalarLogBesselEndpoints
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0512
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0080.rows BesselBatch0080.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0080.rows BesselBatch0080.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0080.rows BesselBatch0080.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0080.rows BesselBatch0080.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0080.rows BesselBatch0080.accepted ⟨4,by decide⟩
]
theorem leftAccepted : besselPointCheck (1609492978472663531004913563492736999263/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1609492978472663531004913563492736999263/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0080.rows BesselBatch0080.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0080.rows BesselBatch0080.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0080.rows BesselBatch0080.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0080.rows BesselBatch0080.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0080.rows BesselBatch0080.accepted ⟨19,by decide⟩
]
theorem rightAccepted : besselPointCheck (322314315416049752583564197974616066269/2000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (322314315416049752583564197974616066269/2000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0528.rows BesselBatch0528.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0528.rows BesselBatch0528.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0528.rows BesselBatch0528.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0528.rows BesselBatch0528.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0528.rows BesselBatch0528.accepted ⟨62,by decide⟩
]
theorem midAccepted : besselPointCheck (201316534722057018370170909585363583163/1250000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (201316534722057018370170909585363583163/1250000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0064.rows ScalarLogs0064.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0064.rows ScalarLogs0064.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0064.rows ScalarLogs0064.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0064.rows ScalarLogs0064.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0064.rows ScalarLogs0064.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0064.rows ScalarLogs0064.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0064.rows ScalarLogs0064.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0064.rows ScalarLogs0064.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0064.rows ScalarLogs0064.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0064.rows ScalarLogs0064.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0064.rows ScalarLogs0064.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0064.rows ScalarLogs0064.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0064.rows ScalarLogs0064.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0064.rows ScalarLogs0064.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0064.rows ScalarLogs0064.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0064.rows ScalarLogs0064.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0032.bracket0512 BracketBatch0032.bracket0513 (201316534722057018370170909585363583163/1250000000000000000000000000000000000000) (250671827909287345793371175782586249/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0032.bracket0512 BracketBatch0032.bracket0513
  (201316534722057018370170909585363583163/1250000000000000000000000000000000000000) (250671827909287345793371175782586249/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0512
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0513
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0080.rows BesselBatch0080.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0080.rows BesselBatch0080.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0080.rows BesselBatch0080.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0080.rows BesselBatch0080.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0080.rows BesselBatch0080.accepted ⟨14,by decide⟩
]
theorem leftAccepted : besselPointCheck (805785788540124381458910494936540165671/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (805785788540124381458910494936540165671/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0080.rows BesselBatch0080.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0080.rows BesselBatch0080.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0080.rows BesselBatch0080.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0080.rows BesselBatch0080.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0080.rows BesselBatch0080.accepted ⟨29,by decide⟩
]
theorem rightAccepted : besselPointCheck (1613650380740726981087912247742638711247/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1613650380740726981087912247742638711247/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0528.rows BesselBatch0528.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0529.rows BesselBatch0529.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0529.rows BesselBatch0529.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0529.rows BesselBatch0529.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0529.rows BesselBatch0529.accepted ⟨3,by decide⟩
]
theorem midAccepted : besselPointCheck (3225221957820975744005733237615719042589/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (3225221957820975744005733237615719042589/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0064.rows ScalarLogs0064.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0064.rows ScalarLogs0064.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0064.rows ScalarLogs0064.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0064.rows ScalarLogs0064.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0064.rows ScalarLogs0064.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0064.rows ScalarLogs0064.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0064.rows ScalarLogs0064.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0064.rows ScalarLogs0064.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0064.rows ScalarLogs0064.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0064.rows ScalarLogs0064.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0064.rows ScalarLogs0064.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0064.rows ScalarLogs0064.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0064.rows ScalarLogs0064.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0064.rows ScalarLogs0064.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0064.rows ScalarLogs0064.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0064.rows ScalarLogs0064.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0032.bracket0513 BracketBatch0032.bracket0514 (3225221957820975744005733237615719042589/20000000000000000000000000000000000000000) (503887675523556033152314289506520111/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0032.bracket0513 BracketBatch0032.bracket0514
  (3225221957820975744005733237615719042589/20000000000000000000000000000000000000000) (503887675523556033152314289506520111/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0513
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0514
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0080.rows BesselBatch0080.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0080.rows BesselBatch0080.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0080.rows BesselBatch0080.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0080.rows BesselBatch0080.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0080.rows BesselBatch0080.accepted ⟨24,by decide⟩
]
theorem leftAccepted : besselPointCheck (403412595185181745271978061935659677811/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (403412595185181745271978061935659677811/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0080.rows BesselBatch0080.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0080.rows BesselBatch0080.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0080.rows BesselBatch0080.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0080.rows BesselBatch0080.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0080.rows BesselBatch0080.accepted ⟨39,by decide⟩
]
theorem rightAccepted : besselPointCheck (1615729389749333896242554665723396123839/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1615729389749333896242554665723396123839/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0529.rows BesselBatch0529.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0529.rows BesselBatch0529.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0529.rows BesselBatch0529.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0529.rows BesselBatch0529.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0529.rows BesselBatch0529.accepted ⟨8,by decide⟩
]
theorem midAccepted : besselPointCheck (3229379770490060877330466913466034835083/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (3229379770490060877330466913466034835083/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0064.rows ScalarLogs0064.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0064.rows ScalarLogs0064.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0064.rows ScalarLogs0064.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0064.rows ScalarLogs0064.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0064.rows ScalarLogs0064.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0064.rows ScalarLogs0064.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0064.rows ScalarLogs0064.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0064.rows ScalarLogs0064.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0064.rows ScalarLogs0064.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0064.rows ScalarLogs0064.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0064.rows ScalarLogs0064.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0064.rows ScalarLogs0064.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0064.rows ScalarLogs0064.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0064.rows ScalarLogs0064.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0064.rows ScalarLogs0064.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0064.rows ScalarLogs0064.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0032.bracket0514 BracketBatch0032.bracket0515 (3229379770490060877330466913466034835083/20000000000000000000000000000000000000000) (63305175933952074838050945806490583/1250000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0032.bracket0514 BracketBatch0032.bracket0515
  (3229379770490060877330466913466034835083/20000000000000000000000000000000000000000) (63305175933952074838050945806490583/1250000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0514
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0515
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0080.rows BesselBatch0080.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0080.rows BesselBatch0080.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0080.rows BesselBatch0080.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0080.rows BesselBatch0080.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0080.rows BesselBatch0080.accepted ⟨34,by decide⟩
]
theorem leftAccepted : besselPointCheck (403932347437333474060638666430849030959/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (403932347437333474060638666430849030959/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0080.rows BesselBatch0080.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0080.rows BesselBatch0080.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0080.rows BesselBatch0080.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0080.rows BesselBatch0080.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0080.rows BesselBatch0080.accepted ⟨49,by decide⟩
]
theorem rightAccepted : besselPointCheck (808904302200728139980470730478248658859/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (808904302200728139980470730478248658859/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0529.rows BesselBatch0529.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0529.rows BesselBatch0529.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0529.rows BesselBatch0529.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0529.rows BesselBatch0529.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0529.rows BesselBatch0529.accepted ⟨13,by decide⟩
]
theorem midAccepted : besselPointCheck (1616768997075395088101748063339946720777/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1616768997075395088101748063339946720777/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0064.rows ScalarLogs0064.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0064.rows ScalarLogs0064.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0064.rows ScalarLogs0064.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0064.rows ScalarLogs0064.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0064.rows ScalarLogs0064.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0064.rows ScalarLogs0064.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0064.rows ScalarLogs0064.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0064.rows ScalarLogs0064.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0064.rows ScalarLogs0064.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0064.rows ScalarLogs0064.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0064.rows ScalarLogs0064.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0064.rows ScalarLogs0064.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0064.rows ScalarLogs0064.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0064.rows ScalarLogs0064.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0064.rows ScalarLogs0064.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0064.rows ScalarLogs0064.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0032.bracket0515 BracketBatch0032.bracket0516 (1616768997075395088101748063339946720777/10000000000000000000000000000000000000000) (509004876735005603760216195442404571/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0032.bracket0515 BracketBatch0032.bracket0516
  (1616768997075395088101748063339946720777/10000000000000000000000000000000000000000) (509004876735005603760216195442404571/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0515
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0516
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0080.rows BesselBatch0080.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0080.rows BesselBatch0080.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0080.rows BesselBatch0080.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0080.rows BesselBatch0080.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0080.rows BesselBatch0080.accepted ⟨44,by decide⟩
]
theorem leftAccepted : besselPointCheck (323561720880291255992188292191299463543/2000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (323561720880291255992188292191299463543/2000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0080.rows BesselBatch0080.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0080.rows BesselBatch0080.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0080.rows BesselBatch0080.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0080.rows BesselBatch0080.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0080.rows BesselBatch0080.accepted ⟨59,by decide⟩
]
theorem rightAccepted : besselPointCheck (2531075039050987842923341413520284949/15625000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (2531075039050987842923341413520284949/15625000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0529.rows BesselBatch0529.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0529.rows BesselBatch0529.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0529.rows BesselBatch0529.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0529.rows BesselBatch0529.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0529.rows BesselBatch0529.accepted ⟨18,by decide⟩
]
theorem midAccepted : besselPointCheck (129507865175763539977275198624379187403/800000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (129507865175763539977275198624379187403/800000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0064.rows ScalarLogs0064.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0064.rows ScalarLogs0064.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0064.rows ScalarLogs0064.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0064.rows ScalarLogs0064.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0064.rows ScalarLogs0064.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0064.rows ScalarLogs0064.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0064.rows ScalarLogs0064.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0064.rows ScalarLogs0064.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0064.rows ScalarLogs0064.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0064.rows ScalarLogs0064.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0064.rows ScalarLogs0064.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0064.rows ScalarLogs0064.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0064.rows ScalarLogs0064.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0064.rows ScalarLogs0064.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0064.rows ScalarLogs0064.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0064.rows ScalarLogs0064.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0032.bracket0516 BracketBatch0032.bracket0517 (129507865175763539977275198624379187403/800000000000000000000000000000000000000) (51157810842077268989566202871029591/1000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0032.bracket0516 BracketBatch0032.bracket0517
  (129507865175763539977275198624379187403/800000000000000000000000000000000000000) (51157810842077268989566202871029591/1000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0516
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0517
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0080.rows BesselBatch0080.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0080.rows BesselBatch0080.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0080.rows BesselBatch0080.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0080.rows BesselBatch0080.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0080.rows BesselBatch0080.accepted ⟨54,by decide⟩
]
theorem leftAccepted : besselPointCheck (1619888024992632219470938504652982367357/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1619888024992632219470938504652982367357/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0081.rows BesselBatch0081.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0081.rows BesselBatch0081.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0081.rows BesselBatch0081.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0081.rows BesselBatch0081.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0081.rows BesselBatch0081.accepted ⟨5,by decide⟩
]
theorem rightAccepted : besselPointCheck (1621967651818551372721932065188807131619/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1621967651818551372721932065188807131619/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0529.rows BesselBatch0529.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0529.rows BesselBatch0529.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0529.rows BesselBatch0529.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0529.rows BesselBatch0529.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0529.rows BesselBatch0529.accepted ⟨23,by decide⟩
]
theorem midAccepted : besselPointCheck (101307989900349487256027205307555921843/625000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (101307989900349487256027205307555921843/625000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0064.rows ScalarLogs0064.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0064.rows ScalarLogs0064.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0064.rows ScalarLogs0064.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0064.rows ScalarLogs0064.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0064.rows ScalarLogs0064.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0064.rows ScalarLogs0064.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0064.rows ScalarLogs0064.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0064.rows ScalarLogs0064.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0064.rows ScalarLogs0064.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0064.rows ScalarLogs0064.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0064.rows ScalarLogs0064.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0064.rows ScalarLogs0064.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0064.rows ScalarLogs0064.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0064.rows ScalarLogs0064.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0064.rows ScalarLogs0064.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0064.rows ScalarLogs0064.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0032.bracket0517 BracketBatch0032.bracket0518 (101307989900349487256027205307555921843/625000000000000000000000000000000000000) (64270140958847634416507833001796447/1250000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0032.bracket0517 BracketBatch0032.bracket0518
  (101307989900349487256027205307555921843/625000000000000000000000000000000000000) (64270140958847634416507833001796447/1250000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0517
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0518
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0080.rows BesselBatch0080.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0080.rows BesselBatch0080.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0080.rows BesselBatch0080.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0080.rows BesselBatch0080.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0081.rows BesselBatch0081.accepted ⟨0,by decide⟩
]
theorem leftAccepted : besselPointCheck (50686489119329730397560377037150222863/312500000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (50686489119329730397560377037150222863/312500000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0081.rows BesselBatch0081.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0081.rows BesselBatch0081.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0081.rows BesselBatch0081.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0081.rows BesselBatch0081.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0081.rows BesselBatch0081.accepted ⟨15,by decide⟩
]
theorem rightAccepted : besselPointCheck (812023742587527611867116562347942771739/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (812023742587527611867116562347942771739/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0529.rows BesselBatch0529.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0529.rows BesselBatch0529.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0529.rows BesselBatch0529.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0529.rows BesselBatch0529.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0529.rows BesselBatch0529.accepted ⟨28,by decide⟩
]
theorem midAccepted : besselPointCheck (1623007568496803298228082594942346337547/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1623007568496803298228082594942346337547/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0064.rows ScalarLogs0064.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0064.rows ScalarLogs0064.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0064.rows ScalarLogs0064.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0064.rows ScalarLogs0064.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0064.rows ScalarLogs0064.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0064.rows ScalarLogs0064.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0064.rows ScalarLogs0064.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0064.rows ScalarLogs0064.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0064.rows ScalarLogs0064.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0064.rows ScalarLogs0064.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0064.rows ScalarLogs0064.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0064.rows ScalarLogs0064.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0064.rows ScalarLogs0064.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0064.rows ScalarLogs0064.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0064.rows ScalarLogs0064.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0064.rows ScalarLogs0064.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0032.bracket0518 BracketBatch0032.bracket0519 (1623007568496803298228082594942346337547/10000000000000000000000000000000000000000) (516753959661720726731002912132918953/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0032.bracket0518 BracketBatch0032.bracket0519
  (1623007568496803298228082594942346337547/10000000000000000000000000000000000000000) (516753959661720726731002912132918953/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0518
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0519
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0081.rows BesselBatch0081.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0081.rows BesselBatch0081.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0081.rows BesselBatch0081.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0081.rows BesselBatch0081.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0081.rows BesselBatch0081.accepted ⟨10,by decide⟩
]
theorem leftAccepted : besselPointCheck (64961899407002208949369324987835421739/400000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (64961899407002208949369324987835421739/400000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0081.rows BesselBatch0081.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0081.rows BesselBatch0081.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0081.rows BesselBatch0081.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0081.rows BesselBatch0081.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0081.rows BesselBatch0081.accepted ⟨25,by decide⟩
]
theorem rightAccepted : besselPointCheck (1626127525358137338225594806329953679769/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1626127525358137338225594806329953679769/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0529.rows BesselBatch0529.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0529.rows BesselBatch0529.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0529.rows BesselBatch0529.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0529.rows BesselBatch0529.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0529.rows BesselBatch0529.accepted ⟨33,by decide⟩
]
theorem midAccepted : besselPointCheck (812543752633298140489956982756459805811/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (812543752633298140489956982756459805811/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0064.rows ScalarLogs0064.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0064.rows ScalarLogs0064.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0064.rows ScalarLogs0064.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0064.rows ScalarLogs0064.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0064.rows ScalarLogs0064.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0064.rows ScalarLogs0064.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0064.rows ScalarLogs0064.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0064.rows ScalarLogs0064.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0064.rows ScalarLogs0064.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0064.rows ScalarLogs0064.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0064.rows ScalarLogs0064.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0064.rows ScalarLogs0064.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0064.rows ScalarLogs0064.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0064.rows ScalarLogs0064.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0064.rows ScalarLogs0064.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0064.rows ScalarLogs0064.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0032.bracket0519 BracketBatch0032.bracket0520 (812543752633298140489956982756459805811/5000000000000000000000000000000000000000) (519356629605121552217372541415546597/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0032.bracket0519 BracketBatch0032.bracket0520
  (812543752633298140489956982756459805811/5000000000000000000000000000000000000000) (519356629605121552217372541415546597/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0519
