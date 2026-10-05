import BecknerOnofri.EntropyScalarCertificate.Bessel0463
import BecknerOnofri.EntropyScalarCertificate.Bessel0464
import BecknerOnofri.EntropyScalarCertificate.Bessel0465
import BecknerOnofri.EntropyScalarCertificate.Bessel0720
import BecknerOnofri.EntropyScalarCertificate.Bessel0721
import BecknerOnofri.EntropyScalarCertificate.Brackets0185
import BecknerOnofri.EntropyScalarCertificate.Brackets0186
import BecknerOnofri.EntropyScalarCertificate.Logs0371
import BecknerOnofri.ScalarElementaryComposition
import BecknerOnofri.ScalarGammaEnclosure
import BecknerOnofri.ScalarLogBesselEndpoints
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2968
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0463.rows BesselBatch0463.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0463.rows BesselBatch0463.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0463.rows BesselBatch0463.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0463.rows BesselBatch0463.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0463.rows BesselBatch0463.accepted ⟨52,by decide⟩
]
theorem leftAccepted : besselPointCheck (1390142279178445665850358475157934990640521/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1390142279178445665850358475157934990640521/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0463.rows BesselBatch0463.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0464.rows BesselBatch0464.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0464.rows BesselBatch0464.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0464.rows BesselBatch0464.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0464.rows BesselBatch0464.accepted ⟨3,by decide⟩
]
theorem rightAccepted : besselPointCheck (1394011040996579241638156665750767060276263/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1394011040996579241638156665750767060276263/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0720.rows BesselBatch0720.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0720.rows BesselBatch0720.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0720.rows BesselBatch0720.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0720.rows BesselBatch0720.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0720.rows BesselBatch0720.accepted ⟨54,by decide⟩
]
theorem midAccepted : besselPointCheck (174009582510939056718032196306793878182299/1250000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (174009582510939056718032196306793878182299/1250000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0371.rows ScalarLogs0371.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0371.rows ScalarLogs0371.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0371.rows ScalarLogs0371.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0371.rows ScalarLogs0371.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0371.rows ScalarLogs0371.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0371.rows ScalarLogs0371.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0371.rows ScalarLogs0371.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0371.rows ScalarLogs0371.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0371.rows ScalarLogs0371.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0371.rows ScalarLogs0371.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0371.rows ScalarLogs0371.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0371.rows ScalarLogs0371.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0371.rows ScalarLogs0371.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0371.rows ScalarLogs0371.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0371.rows ScalarLogs0371.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0371.rows ScalarLogs0371.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0185.bracket2968 BracketBatch0185.bracket2969 (174009582510939056718032196306793878182299/1250000000000000000000000000000000000000) (6620478647213075860177703052409761879363/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0185.bracket2968 BracketBatch0185.bracket2969
  (174009582510939056718032196306793878182299/1250000000000000000000000000000000000000) (6620478647213075860177703052409761879363/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2968
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2969
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0463.rows BesselBatch0463.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0463.rows BesselBatch0463.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0463.rows BesselBatch0463.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0463.rows BesselBatch0463.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0463.rows BesselBatch0463.accepted ⟨62,by decide⟩
]
theorem leftAccepted : besselPointCheck (69700552049828962081907833287538353013813/500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (69700552049828962081907833287538353013813/500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0464.rows BesselBatch0464.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0464.rows BesselBatch0464.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0464.rows BesselBatch0464.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0464.rows BesselBatch0464.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0464.rows BesselBatch0464.accepted ⟨13,by decide⟩
]
theorem rightAccepted : besselPointCheck (1397901416062316427076265468409748527962537/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1397901416062316427076265468409748527962537/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0720.rows BesselBatch0720.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0720.rows BesselBatch0720.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0720.rows BesselBatch0720.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0720.rows BesselBatch0720.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0720.rows BesselBatch0720.accepted ⟨59,by decide⟩
]
theorem midAccepted : besselPointCheck (2791912457058895668714422134160515588238797/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (2791912457058895668714422134160515588238797/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0371.rows ScalarLogs0371.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0371.rows ScalarLogs0371.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0371.rows ScalarLogs0371.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0371.rows ScalarLogs0371.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0371.rows ScalarLogs0371.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0371.rows ScalarLogs0371.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0371.rows ScalarLogs0371.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0371.rows ScalarLogs0371.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0371.rows ScalarLogs0371.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0371.rows ScalarLogs0371.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0371.rows ScalarLogs0371.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0371.rows ScalarLogs0371.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0371.rows ScalarLogs0371.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0371.rows ScalarLogs0371.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0371.rows ScalarLogs0371.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0371.rows ScalarLogs0371.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0185.bracket2969 BracketBatch0185.bracket2970 (2791912457058895668714422134160515588238797/20000000000000000000000000000000000000000) (3312372971018451333435402130101413488299/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0185.bracket2969 BracketBatch0185.bracket2970
  (2791912457058895668714422134160515588238797/20000000000000000000000000000000000000000) (3312372971018451333435402130101413488299/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2969
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2970
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0464.rows BesselBatch0464.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0464.rows BesselBatch0464.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0464.rows BesselBatch0464.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0464.rows BesselBatch0464.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0464.rows BesselBatch0464.accepted ⟨8,by decide⟩
]
theorem leftAccepted : besselPointCheck (698950708031158213538132734204874263981267/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (698950708031158213538132734204874263981267/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0464.rows BesselBatch0464.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0464.rows BesselBatch0464.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0464.rows BesselBatch0464.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0464.rows BesselBatch0464.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0464.rows BesselBatch0464.accepted ⟨23,by decide⟩
]
theorem rightAccepted : besselPointCheck (1401813585999584641294157505172274363500789/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1401813585999584641294157505172274363500789/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0720.rows BesselBatch0720.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0720.rows BesselBatch0720.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0720.rows BesselBatch0720.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0720.rows BesselBatch0720.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0721.rows BesselBatch0721.accepted ⟨0,by decide⟩
]
theorem midAccepted : besselPointCheck (2799715002061901068370422973582022891463323/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (2799715002061901068370422973582022891463323/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0371.rows ScalarLogs0371.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0371.rows ScalarLogs0371.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0371.rows ScalarLogs0371.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0371.rows ScalarLogs0371.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0371.rows ScalarLogs0371.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0371.rows ScalarLogs0371.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0371.rows ScalarLogs0371.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0371.rows ScalarLogs0371.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0371.rows ScalarLogs0371.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0371.rows ScalarLogs0371.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0371.rows ScalarLogs0371.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0371.rows ScalarLogs0371.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0371.rows ScalarLogs0371.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0371.rows ScalarLogs0371.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0371.rows ScalarLogs0371.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0371.rows ScalarLogs0371.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0185.bracket2970 BracketBatch0185.bracket2971 (2799715002061901068370422973582022891463323/20000000000000000000000000000000000000000) (6629024778578853190546097256738950701417/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0185.bracket2970 BracketBatch0185.bracket2971
  (2799715002061901068370422973582022891463323/20000000000000000000000000000000000000000) (6629024778578853190546097256738950701417/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2970
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2971
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0464.rows BesselBatch0464.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0464.rows BesselBatch0464.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0464.rows BesselBatch0464.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0464.rows BesselBatch0464.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0464.rows BesselBatch0464.accepted ⟨18,by decide⟩
]
theorem leftAccepted : besselPointCheck (700906792999792320647078752586137181750393/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (700906792999792320647078752586137181750393/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0464.rows BesselBatch0464.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0464.rows BesselBatch0464.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0464.rows BesselBatch0464.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0464.rows BesselBatch0464.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0464.rows BesselBatch0464.accepted ⟨33,by decide⟩
]
theorem rightAccepted : besselPointCheck (1405747734473029589182326872778281283172853/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1405747734473029589182326872778281283172853/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0721.rows BesselBatch0721.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0721.rows BesselBatch0721.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0721.rows BesselBatch0721.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0721.rows BesselBatch0721.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0721.rows BesselBatch0721.accepted ⟨5,by decide⟩
]
theorem midAccepted : besselPointCheck (2807561320472614230476484377950555646673639/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (2807561320472614230476484377950555646673639/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0371.rows ScalarLogs0371.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0371.rows ScalarLogs0371.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0371.rows ScalarLogs0371.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0371.rows ScalarLogs0371.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0371.rows ScalarLogs0371.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0371.rows ScalarLogs0371.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0371.rows ScalarLogs0371.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0371.rows ScalarLogs0371.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0371.rows ScalarLogs0371.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0371.rows ScalarLogs0371.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0371.rows ScalarLogs0371.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0371.rows ScalarLogs0371.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0371.rows ScalarLogs0371.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0371.rows ScalarLogs0371.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0371.rows ScalarLogs0371.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0371.rows ScalarLogs0371.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0185.bracket2971 BracketBatch0185.bracket2972 (2807561320472614230476484377950555646673639/20000000000000000000000000000000000000000) (6633315214175495606272181036531213237971/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0185.bracket2971 BracketBatch0185.bracket2972
  (2807561320472614230476484377950555646673639/20000000000000000000000000000000000000000) (6633315214175495606272181036531213237971/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2971
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2972
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0464.rows BesselBatch0464.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0464.rows BesselBatch0464.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0464.rows BesselBatch0464.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0464.rows BesselBatch0464.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0464.rows BesselBatch0464.accepted ⟨28,by decide⟩
]
theorem leftAccepted : besselPointCheck (28114954689460591783646537455565625663457/200000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (28114954689460591783646537455565625663457/200000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0464.rows BesselBatch0464.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0464.rows BesselBatch0464.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0464.rows BesselBatch0464.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0464.rows BesselBatch0464.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0464.rows BesselBatch0464.accepted ⟨43,by decide⟩
]
theorem rightAccepted : besselPointCheck (176213005902094721557415809009393172810697/1250000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (176213005902094721557415809009393172810697/1250000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0721.rows BesselBatch0721.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0721.rows BesselBatch0721.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0721.rows BesselBatch0721.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0721.rows BesselBatch0721.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0721.rows BesselBatch0721.accepted ⟨10,by decide⟩
]
theorem midAccepted : besselPointCheck (1407725890844893680820826672426713332829213/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1407725890844893680820826672426713332829213/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0371.rows ScalarLogs0371.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0371.rows ScalarLogs0371.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0371.rows ScalarLogs0371.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0371.rows ScalarLogs0371.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0371.rows ScalarLogs0371.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0371.rows ScalarLogs0371.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0371.rows ScalarLogs0371.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0371.rows ScalarLogs0371.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0371.rows ScalarLogs0371.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0371.rows ScalarLogs0371.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0371.rows ScalarLogs0371.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0371.rows ScalarLogs0371.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0371.rows ScalarLogs0371.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0371.rows ScalarLogs0371.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0371.rows ScalarLogs0371.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0371.rows ScalarLogs0371.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0185.bracket2972 BracketBatch0185.bracket2973 (1407725890844893680820826672426713332829213/10000000000000000000000000000000000000000) (3318808653272081932542644810165656920399/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0185.bracket2972 BracketBatch0185.bracket2973
  (1407725890844893680820826672426713332829213/10000000000000000000000000000000000000000) (3318808653272081932542644810165656920399/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2972
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2973
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0464.rows BesselBatch0464.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0464.rows BesselBatch0464.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0464.rows BesselBatch0464.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0464.rows BesselBatch0464.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0464.rows BesselBatch0464.accepted ⟨38,by decide⟩
]
theorem leftAccepted : besselPointCheck (1409704047216757772459326472075145382485573/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1409704047216757772459326472075145382485573/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0464.rows BesselBatch0464.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0464.rows BesselBatch0464.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0464.rows BesselBatch0464.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0464.rows BesselBatch0464.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0464.rows BesselBatch0464.accepted ⟨53,by decide⟩
]
theorem rightAccepted : besselPointCheck (1413682712063566161943331397486590802578721/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1413682712063566161943331397486590802578721/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0721.rows BesselBatch0721.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0721.rows BesselBatch0721.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0721.rows BesselBatch0721.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0721.rows BesselBatch0721.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0721.rows BesselBatch0721.accepted ⟨15,by decide⟩
]
theorem midAccepted : besselPointCheck (1411693379640161967201328934780868092532147/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1411693379640161967201328934780868092532147/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0371.rows ScalarLogs0371.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0371.rows ScalarLogs0371.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0371.rows ScalarLogs0371.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0371.rows ScalarLogs0371.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0371.rows ScalarLogs0371.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0371.rows ScalarLogs0371.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0371.rows ScalarLogs0371.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0371.rows ScalarLogs0371.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0371.rows ScalarLogs0371.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0371.rows ScalarLogs0371.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0371.rows ScalarLogs0371.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0371.rows ScalarLogs0371.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0371.rows ScalarLogs0371.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0371.rows ScalarLogs0371.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0371.rows ScalarLogs0371.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0371.rows ScalarLogs0371.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0185.bracket2973 BracketBatch0185.bracket2974 (1411693379640161967201328934780868092532147/10000000000000000000000000000000000000000) (6641931113785544742569042127915037568933/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0185.bracket2973 BracketBatch0185.bracket2974
  (1411693379640161967201328934780868092532147/10000000000000000000000000000000000000000) (6641931113785544742569042127915037568933/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2973
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2974
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0464.rows BesselBatch0464.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0464.rows BesselBatch0464.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0464.rows BesselBatch0464.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0464.rows BesselBatch0464.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0464.rows BesselBatch0464.accepted ⟨48,by decide⟩
]
theorem leftAccepted : besselPointCheck (706841356031783080971665698743295401289359/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (706841356031783080971665698743295401289359/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0464.rows BesselBatch0464.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0464.rows BesselBatch0464.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0464.rows BesselBatch0464.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0464.rows BesselBatch0464.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0464.rows BesselBatch0464.accepted ⟨63,by decide⟩
]
theorem rightAccepted : besselPointCheck (35442097974366717286217868475263102844843/250000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (35442097974366717286217868475263102844843/250000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0721.rows BesselBatch0721.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0721.rows BesselBatch0721.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0721.rows BesselBatch0721.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0721.rows BesselBatch0721.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0721.rows BesselBatch0721.accepted ⟨20,by decide⟩
]
theorem midAccepted : besselPointCheck (1415683315519117426696023068248557458186219/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1415683315519117426696023068248557458186219/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0371.rows ScalarLogs0371.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0371.rows ScalarLogs0371.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0371.rows ScalarLogs0371.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0371.rows ScalarLogs0371.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0371.rows ScalarLogs0371.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0371.rows ScalarLogs0371.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0371.rows ScalarLogs0371.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0371.rows ScalarLogs0371.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0371.rows ScalarLogs0371.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0371.rows ScalarLogs0371.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0371.rows ScalarLogs0371.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0371.rows ScalarLogs0371.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0371.rows ScalarLogs0371.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0371.rows ScalarLogs0371.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0371.rows ScalarLogs0371.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0371.rows ScalarLogs0371.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0185.bracket2974 BracketBatch0185.bracket2975 (1415683315519117426696023068248557458186219/10000000000000000000000000000000000000000) (6646256694386268210286411659701507113211/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0185.bracket2974 BracketBatch0185.bracket2975
  (1415683315519117426696023068248557458186219/10000000000000000000000000000000000000000) (6646256694386268210286411659701507113211/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2974
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2975
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0464.rows BesselBatch0464.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0464.rows BesselBatch0464.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0464.rows BesselBatch0464.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0464.rows BesselBatch0464.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0464.rows BesselBatch0464.accepted ⟨58,by decide⟩
]
theorem leftAccepted : besselPointCheck (1417683918974668691448714739010524113793717/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1417683918974668691448714739010524113793717/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0465.rows BesselBatch0465.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0465.rows BesselBatch0465.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0465.rows BesselBatch0465.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0465.rows BesselBatch0465.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0465.rows BesselBatch0465.accepted ⟨9,by decide⟩
]
theorem rightAccepted : besselPointCheck (710853930034964726641566601337910559600511/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (710853930034964726641566601337910559600511/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0721.rows BesselBatch0721.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0721.rows BesselBatch0721.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0721.rows BesselBatch0721.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0721.rows BesselBatch0721.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0721.rows BesselBatch0721.accepted ⟨25,by decide⟩
]
theorem midAccepted : besselPointCheck (2839391779044598144731847941686345232994739/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (2839391779044598144731847941686345232994739/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0371.rows ScalarLogs0371.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0371.rows ScalarLogs0371.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0371.rows ScalarLogs0371.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0371.rows ScalarLogs0371.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0371.rows ScalarLogs0371.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0371.rows ScalarLogs0371.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0371.rows ScalarLogs0371.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0371.rows ScalarLogs0371.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0371.rows ScalarLogs0371.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0371.rows ScalarLogs0371.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0371.rows ScalarLogs0371.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0371.rows ScalarLogs0371.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0371.rows ScalarLogs0371.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0371.rows ScalarLogs0371.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0371.rows ScalarLogs0371.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0371.rows ScalarLogs0371.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0185.bracket2975 BracketBatch0186.bracket2976 (2839391779044598144731847941686345232994739/20000000000000000000000000000000000000000) (6650594107221500441819354557831816962193/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0185.bracket2975 BracketBatch0186.bracket2976
  (2839391779044598144731847941686345232994739/20000000000000000000000000000000000000000) (6650594107221500441819354557831816962193/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2975
