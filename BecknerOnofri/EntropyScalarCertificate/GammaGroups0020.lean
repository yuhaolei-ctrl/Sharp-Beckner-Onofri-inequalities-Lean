import BecknerOnofri.EntropyScalarCertificate.Bessel0025
import BecknerOnofri.EntropyScalarCertificate.Bessel0026
import BecknerOnofri.EntropyScalarCertificate.Bessel0501
import BecknerOnofri.EntropyScalarCertificate.Bessel0502
import BecknerOnofri.EntropyScalarCertificate.Brackets0010
import BecknerOnofri.EntropyScalarCertificate.Logs0020
import BecknerOnofri.ScalarElementaryComposition
import BecknerOnofri.ScalarGammaEnclosure
import BecknerOnofri.ScalarLogBesselEndpoints
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0160
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0025.rows BesselBatch0025.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0025.rows BesselBatch0025.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0025.rows BesselBatch0025.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0025.rows BesselBatch0025.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0025.rows BesselBatch0025.accepted ⟨4,by decide⟩
]
theorem leftAccepted : besselPointCheck (444244280461187012151517573823262725689/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (444244280461187012151517573823262725689/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0025.rows BesselBatch0025.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0025.rows BesselBatch0025.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0025.rows BesselBatch0025.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0025.rows BesselBatch0025.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0025.rows BesselBatch0025.accepted ⟨19,by decide⟩
]
theorem rightAccepted : besselPointCheck (890512370278933288167675944326869823527/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (890512370278933288167675944326869823527/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0501.rows BesselBatch0501.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0501.rows BesselBatch0501.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0501.rows BesselBatch0501.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0501.rows BesselBatch0501.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0501.rows BesselBatch0501.accepted ⟨30,by decide⟩
]
theorem midAccepted : besselPointCheck (355800186240261462494142218394679054981/4000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (355800186240261462494142218394679054981/4000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0020.rows ScalarLogs0020.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0020.rows ScalarLogs0020.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0020.rows ScalarLogs0020.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0020.rows ScalarLogs0020.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0020.rows ScalarLogs0020.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0020.rows ScalarLogs0020.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0020.rows ScalarLogs0020.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0020.rows ScalarLogs0020.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0020.rows ScalarLogs0020.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0020.rows ScalarLogs0020.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0020.rows ScalarLogs0020.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0020.rows ScalarLogs0020.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0020.rows ScalarLogs0020.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0020.rows ScalarLogs0020.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0020.rows ScalarLogs0020.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0020.rows ScalarLogs0020.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0010.bracket0160 BracketBatch0010.bracket0161 (355800186240261462494142218394679054981/4000000000000000000000000000000000000000) (23765557221337503570206296312483573/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0010.bracket0160 BracketBatch0010.bracket0161
  (355800186240261462494142218394679054981/4000000000000000000000000000000000000000) (23765557221337503570206296312483573/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0160
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0161
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0025.rows BesselBatch0025.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0025.rows BesselBatch0025.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0025.rows BesselBatch0025.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0025.rows BesselBatch0025.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0025.rows BesselBatch0025.accepted ⟨14,by decide⟩
]
theorem leftAccepted : besselPointCheck (222628092569733322041918986081717455881/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (222628092569733322041918986081717455881/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0025.rows BesselBatch0025.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0025.rows BesselBatch0025.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0025.rows BesselBatch0025.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0025.rows BesselBatch0025.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0025.rows BesselBatch0025.accepted ⟨29,by decide⟩
]
theorem rightAccepted : besselPointCheck (892536288438725189834824550555623663743/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (892536288438725189834824550555623663743/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0501.rows BesselBatch0501.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0501.rows BesselBatch0501.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0501.rows BesselBatch0501.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0501.rows BesselBatch0501.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0501.rows BesselBatch0501.accepted ⟨35,by decide⟩
]
theorem midAccepted : besselPointCheck (1783048658717658478002500494882493487267/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1783048658717658478002500494882493487267/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0020.rows ScalarLogs0020.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0020.rows ScalarLogs0020.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0020.rows ScalarLogs0020.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0020.rows ScalarLogs0020.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0020.rows ScalarLogs0020.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0020.rows ScalarLogs0020.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0020.rows ScalarLogs0020.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0020.rows ScalarLogs0020.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0020.rows ScalarLogs0020.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0020.rows ScalarLogs0020.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0020.rows ScalarLogs0020.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0020.rows ScalarLogs0020.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0020.rows ScalarLogs0020.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0020.rows ScalarLogs0020.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0020.rows ScalarLogs0020.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0020.rows ScalarLogs0020.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0010.bracket0161 BracketBatch0010.bracket0162 (1783048658717658478002500494882493487267/20000000000000000000000000000000000000000) (23983302051172484040371329292190541/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0010.bracket0161 BracketBatch0010.bracket0162
  (1783048658717658478002500494882493487267/20000000000000000000000000000000000000000) (23983302051172484040371329292190541/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0161
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0162
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0025.rows BesselBatch0025.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0025.rows BesselBatch0025.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0025.rows BesselBatch0025.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0025.rows BesselBatch0025.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0025.rows BesselBatch0025.accepted ⟨24,by decide⟩
]
theorem leftAccepted : besselPointCheck (44626814421936259491741227527781183187/500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (44626814421936259491741227527781183187/500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0025.rows BesselBatch0025.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0025.rows BesselBatch0025.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0025.rows BesselBatch0025.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0025.rows BesselBatch0025.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0025.rows BesselBatch0025.accepted ⟨39,by decide⟩
]
theorem rightAccepted : besselPointCheck (44728015782897105541791179604520868527/500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (44728015782897105541791179604520868527/500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0501.rows BesselBatch0501.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0501.rows BesselBatch0501.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0501.rows BesselBatch0501.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0501.rows BesselBatch0501.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0501.rows BesselBatch0501.accepted ⟨40,by decide⟩
]
theorem midAccepted : besselPointCheck (44677415102416682516766203566151025857/500000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (44677415102416682516766203566151025857/500000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0020.rows ScalarLogs0020.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0020.rows ScalarLogs0020.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0020.rows ScalarLogs0020.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0020.rows ScalarLogs0020.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0020.rows ScalarLogs0020.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0020.rows ScalarLogs0020.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0020.rows ScalarLogs0020.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0020.rows ScalarLogs0020.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0020.rows ScalarLogs0020.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0020.rows ScalarLogs0020.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0020.rows ScalarLogs0020.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0020.rows ScalarLogs0020.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0020.rows ScalarLogs0020.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0020.rows ScalarLogs0020.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0020.rows ScalarLogs0020.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0020.rows ScalarLogs0020.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0010.bracket0162 BracketBatch0010.bracket0163 (44677415102416682516766203566151025857/500000000000000000000000000000000000000) (48405059242806987921966281971859707/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0010.bracket0162 BracketBatch0010.bracket0163
  (44677415102416682516766203566151025857/500000000000000000000000000000000000000) (48405059242806987921966281971859707/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0162
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0163
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0025.rows BesselBatch0025.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0025.rows BesselBatch0025.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0025.rows BesselBatch0025.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0025.rows BesselBatch0025.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0025.rows BesselBatch0025.accepted ⟨34,by decide⟩
]
theorem leftAccepted : besselPointCheck (894560315657942110835823592090417370537/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (894560315657942110835823592090417370537/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0025.rows BesselBatch0025.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0025.rows BesselBatch0025.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0025.rows BesselBatch0025.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0025.rows BesselBatch0025.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0025.rows BesselBatch0025.accepted ⟨49,by decide⟩
]
theorem rightAccepted : besselPointCheck (896584452192851399568376907211999113449/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (896584452192851399568376907211999113449/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0501.rows BesselBatch0501.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0501.rows BesselBatch0501.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0501.rows BesselBatch0501.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0501.rows BesselBatch0501.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0501.rows BesselBatch0501.accepted ⟨45,by decide⟩
]
theorem midAccepted : besselPointCheck (895572383925396755202100249651208241993/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (895572383925396755202100249651208241993/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0020.rows ScalarLogs0020.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0020.rows ScalarLogs0020.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0020.rows ScalarLogs0020.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0020.rows ScalarLogs0020.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0020.rows ScalarLogs0020.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0020.rows ScalarLogs0020.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0020.rows ScalarLogs0020.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0020.rows ScalarLogs0020.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0020.rows ScalarLogs0020.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0020.rows ScalarLogs0020.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0020.rows ScalarLogs0020.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0020.rows ScalarLogs0020.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0020.rows ScalarLogs0020.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0020.rows ScalarLogs0020.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0020.rows ScalarLogs0020.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0020.rows ScalarLogs0020.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0010.bracket0163 BracketBatch0010.bracket0164 (895572383925396755202100249651208241993/10000000000000000000000000000000000000000) (48846493359870572484544929586564523/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0010.bracket0163 BracketBatch0010.bracket0164
  (895572383925396755202100249651208241993/10000000000000000000000000000000000000000) (48846493359870572484544929586564523/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0163
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0164
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0025.rows BesselBatch0025.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0025.rows BesselBatch0025.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0025.rows BesselBatch0025.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0025.rows BesselBatch0025.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0025.rows BesselBatch0025.accepted ⟨44,by decide⟩
]
theorem leftAccepted : besselPointCheck (448292226096425699784188453605999556723/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (448292226096425699784188453605999556723/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0025.rows BesselBatch0025.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0025.rows BesselBatch0025.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0025.rows BesselBatch0025.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0025.rows BesselBatch0025.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0025.rows BesselBatch0025.accepted ⟨59,by decide⟩
]
theorem rightAccepted : besselPointCheck (224652174574948889455815040679059240507/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (224652174574948889455815040679059240507/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0501.rows BesselBatch0501.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0501.rows BesselBatch0501.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0501.rows BesselBatch0501.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0501.rows BesselBatch0501.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0501.rows BesselBatch0501.accepted ⟨50,by decide⟩
]
theorem midAccepted : besselPointCheck (897596575246323478695818534964118037737/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (897596575246323478695818534964118037737/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0020.rows ScalarLogs0020.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0020.rows ScalarLogs0020.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0020.rows ScalarLogs0020.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0020.rows ScalarLogs0020.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0020.rows ScalarLogs0020.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0020.rows ScalarLogs0020.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0020.rows ScalarLogs0020.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0020.rows ScalarLogs0020.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0020.rows ScalarLogs0020.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0020.rows ScalarLogs0020.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0020.rows ScalarLogs0020.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0020.rows ScalarLogs0020.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0020.rows ScalarLogs0020.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0020.rows ScalarLogs0020.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0020.rows ScalarLogs0020.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0020.rows ScalarLogs0020.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0010.bracket0164 BracketBatch0010.bracket0165 (897596575246323478695818534964118037737/10000000000000000000000000000000000000000) (12322729995178446273280533807819427/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0010.bracket0164 BracketBatch0010.bracket0165
  (897596575246323478695818534964118037737/10000000000000000000000000000000000000000) (12322729995178446273280533807819427/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0164
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0165
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0025.rows BesselBatch0025.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0025.rows BesselBatch0025.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0025.rows BesselBatch0025.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0025.rows BesselBatch0025.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0025.rows BesselBatch0025.accepted ⟨54,by decide⟩
]
theorem leftAccepted : besselPointCheck (35944347931991822312930406508649478481/400000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (35944347931991822312930406508649478481/400000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0026.rows BesselBatch0026.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0026.rows BesselBatch0026.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0026.rows BesselBatch0026.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0026.rows BesselBatch0026.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0026.rows BesselBatch0026.accepted ⟨5,by decide⟩
]
theorem rightAccepted : besselPointCheck (900633054235192427436175176713126493549/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (900633054235192427436175176713126493549/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0501.rows BesselBatch0501.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0501.rows BesselBatch0501.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0501.rows BesselBatch0501.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0501.rows BesselBatch0501.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0501.rows BesselBatch0501.accepted ⟨55,by decide⟩
]
theorem midAccepted : besselPointCheck (899620876267493992629717669714681727787/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (899620876267493992629717669714681727787/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0020.rows ScalarLogs0020.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0020.rows ScalarLogs0020.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0020.rows ScalarLogs0020.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0020.rows ScalarLogs0020.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0020.rows ScalarLogs0020.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0020.rows ScalarLogs0020.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0020.rows ScalarLogs0020.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0020.rows ScalarLogs0020.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0020.rows ScalarLogs0020.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0020.rows ScalarLogs0020.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0020.rows ScalarLogs0020.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0020.rows ScalarLogs0020.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0020.rows ScalarLogs0020.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0020.rows ScalarLogs0020.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0020.rows ScalarLogs0020.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0020.rows ScalarLogs0020.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0010.bracket0165 BracketBatch0010.bracket0166 (899620876267493992629717669714681727787/10000000000000000000000000000000000000000) (49738352663889916359237848040254363/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0010.bracket0165 BracketBatch0010.bracket0166
  (899620876267493992629717669714681727787/10000000000000000000000000000000000000000) (49738352663889916359237848040254363/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0165
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0166
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0025.rows BesselBatch0025.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0025.rows BesselBatch0025.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0025.rows BesselBatch0025.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0025.rows BesselBatch0025.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0026.rows BesselBatch0026.accepted ⟨0,by decide⟩
]
theorem leftAccepted : besselPointCheck (450316527117596213718087588356563246773/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (450316527117596213718087588356563246773/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0026.rows BesselBatch0026.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0026.rows BesselBatch0026.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0026.rows BesselBatch0026.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0026.rows BesselBatch0026.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0026.rows BesselBatch0026.accepted ⟨15,by decide⟩
]
theorem rightAccepted : besselPointCheck (902657520255535377065082475603875801287/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (902657520255535377065082475603875801287/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0501.rows BesselBatch0501.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0501.rows BesselBatch0501.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0501.rows BesselBatch0501.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0501.rows BesselBatch0501.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0501.rows BesselBatch0501.accepted ⟨60,by decide⟩
]
theorem midAccepted : besselPointCheck (1803290574490727804501257652317002294833/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1803290574490727804501257652317002294833/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0020.rows ScalarLogs0020.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0020.rows ScalarLogs0020.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0020.rows ScalarLogs0020.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0020.rows ScalarLogs0020.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0020.rows ScalarLogs0020.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0020.rows ScalarLogs0020.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0020.rows ScalarLogs0020.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0020.rows ScalarLogs0020.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0020.rows ScalarLogs0020.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0020.rows ScalarLogs0020.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0020.rows ScalarLogs0020.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0020.rows ScalarLogs0020.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0020.rows ScalarLogs0020.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0020.rows ScalarLogs0020.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0020.rows ScalarLogs0020.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0020.rows ScalarLogs0020.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0010.bracket0166 BracketBatch0010.bracket0167 (1803290574490727804501257652317002294833/20000000000000000000000000000000000000000) (50188804999334170245588813963604751/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0010.bracket0166 BracketBatch0010.bracket0167
  (1803290574490727804501257652317002294833/20000000000000000000000000000000000000000) (50188804999334170245588813963604751/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0166
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0167
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0026.rows BesselBatch0026.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0026.rows BesselBatch0026.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0026.rows BesselBatch0026.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0026.rows BesselBatch0026.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0026.rows BesselBatch0026.accepted ⟨10,by decide⟩
]
theorem leftAccepted : besselPointCheck (225664380063883844266270618900968950321/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (225664380063883844266270618900968950321/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0026.rows BesselBatch0026.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0026.rows BesselBatch0026.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0026.rows BesselBatch0026.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0026.rows BesselBatch0026.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0026.rows BesselBatch0026.accepted ⟨25,by decide⟩
]
theorem rightAccepted : besselPointCheck (452341048308696744546673497582658752787/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (452341048308696744546673497582658752787/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0501.rows BesselBatch0501.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0501.rows BesselBatch0501.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0501.rows BesselBatch0501.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0502.rows BesselBatch0502.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0502.rows BesselBatch0502.accepted ⟨1,by decide⟩
]
theorem midAccepted : besselPointCheck (903669808436464433079214735384596653429/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (903669808436464433079214735384596653429/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0020.rows ScalarLogs0020.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0020.rows ScalarLogs0020.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0020.rows ScalarLogs0020.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0020.rows ScalarLogs0020.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0020.rows ScalarLogs0020.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0020.rows ScalarLogs0020.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0020.rows ScalarLogs0020.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0020.rows ScalarLogs0020.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0020.rows ScalarLogs0020.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0020.rows ScalarLogs0020.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0020.rows ScalarLogs0020.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0020.rows ScalarLogs0020.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0020.rows ScalarLogs0020.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0020.rows ScalarLogs0020.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0020.rows ScalarLogs0020.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0020.rows ScalarLogs0020.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0010.bracket0167 BracketBatch0010.bracket0168 (903669808436464433079214735384596653429/10000000000000000000000000000000000000000) (3165143163023147901304879084816829/625000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0010.bracket0167 BracketBatch0010.bracket0168
  (903669808436464433079214735384596653429/10000000000000000000000000000000000000000) (3165143163023147901304879084816829/625000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0167
