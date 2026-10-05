import BecknerOnofri.EntropyScalarCertificate.Bessel0060
import BecknerOnofri.EntropyScalarCertificate.Bessel0061
import BecknerOnofri.EntropyScalarCertificate.Bessel0518
import BecknerOnofri.EntropyScalarCertificate.Bessel0519
import BecknerOnofri.EntropyScalarCertificate.Brackets0024
import BecknerOnofri.EntropyScalarCertificate.Logs0048
import BecknerOnofri.ScalarElementaryComposition
import BecknerOnofri.ScalarGammaEnclosure
import BecknerOnofri.ScalarLogBesselEndpoints
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0384
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0060.rows BesselBatch0060.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0060.rows BesselBatch0060.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0060.rows BesselBatch0060.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0060.rows BesselBatch0060.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0060.rows BesselBatch0060.accepted ⟨4,by decide⟩
]
theorem leftAccepted : besselPointCheck (336255335697981353624759667703320153329/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (336255335697981353624759667703320153329/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0060.rows BesselBatch0060.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0060.rows BesselBatch0060.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0060.rows BesselBatch0060.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0060.rows BesselBatch0060.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0060.rows BesselBatch0060.accepted ⟨19,by decide⟩
]
theorem rightAccepted : besselPointCheck (1347076080955387099388067240175605373403/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1347076080955387099388067240175605373403/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0518.rows BesselBatch0518.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0518.rows BesselBatch0518.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0518.rows BesselBatch0518.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0518.rows BesselBatch0518.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0518.rows BesselBatch0518.accepted ⟨62,by decide⟩
]
theorem midAccepted : besselPointCheck (2692097423747312513887105910988885986719/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (2692097423747312513887105910988885986719/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0048.rows ScalarLogs0048.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0048.rows ScalarLogs0048.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0048.rows ScalarLogs0048.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0048.rows ScalarLogs0048.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0048.rows ScalarLogs0048.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0048.rows ScalarLogs0048.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0048.rows ScalarLogs0048.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0048.rows ScalarLogs0048.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0048.rows ScalarLogs0048.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0048.rows ScalarLogs0048.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0048.rows ScalarLogs0048.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0048.rows ScalarLogs0048.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0048.rows ScalarLogs0048.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0048.rows ScalarLogs0048.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0048.rows ScalarLogs0048.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0048.rows ScalarLogs0048.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0024.bracket0384 BracketBatch0024.bracket0385 (2692097423747312513887105910988885986719/20000000000000000000000000000000000000000) (123662868486345835804642025951977221/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0024.bracket0384 BracketBatch0024.bracket0385
  (2692097423747312513887105910988885986719/20000000000000000000000000000000000000000) (123662868486345835804642025951977221/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0384
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0385
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0060.rows BesselBatch0060.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0060.rows BesselBatch0060.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0060.rows BesselBatch0060.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0060.rows BesselBatch0060.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0060.rows BesselBatch0060.accepted ⟨14,by decide⟩
]
theorem leftAccepted : besselPointCheck (6735380404776935496940336200878026867/50000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (6735380404776935496940336200878026867/50000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0060.rows BesselBatch0060.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0060.rows BesselBatch0060.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0060.rows BesselBatch0060.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0060.rows BesselBatch0060.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0060.rows BesselBatch0060.accepted ⟨29,by decide⟩
]
theorem rightAccepted : besselPointCheck (337282746885160296516645335754763406833/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (337282746885160296516645335754763406833/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0518.rows BesselBatch0518.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0519.rows BesselBatch0519.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0519.rows BesselBatch0519.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0519.rows BesselBatch0519.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0519.rows BesselBatch0519.accepted ⟨3,by decide⟩
]
theorem midAccepted : besselPointCheck (674051767124007071363662145798664750183/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (674051767124007071363662145798664750183/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0048.rows ScalarLogs0048.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0048.rows ScalarLogs0048.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0048.rows ScalarLogs0048.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0048.rows ScalarLogs0048.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0048.rows ScalarLogs0048.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0048.rows ScalarLogs0048.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0048.rows ScalarLogs0048.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0048.rows ScalarLogs0048.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0048.rows ScalarLogs0048.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0048.rows ScalarLogs0048.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0048.rows ScalarLogs0048.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0048.rows ScalarLogs0048.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0048.rows ScalarLogs0048.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0048.rows ScalarLogs0048.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0048.rows ScalarLogs0048.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0048.rows ScalarLogs0048.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0024.bracket0385 BracketBatch0024.bracket0386 (674051767124007071363662145798664750183/5000000000000000000000000000000000000000) (248821297037714223155432809675300053/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0024.bracket0385 BracketBatch0024.bracket0386
  (674051767124007071363662145798664750183/5000000000000000000000000000000000000000) (248821297037714223155432809675300053/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0385
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0386
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0060.rows BesselBatch0060.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0060.rows BesselBatch0060.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0060.rows BesselBatch0060.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0060.rows BesselBatch0060.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0060.rows BesselBatch0060.accepted ⟨24,by decide⟩
]
theorem leftAccepted : besselPointCheck (1349130987540641186066581343019053627329/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1349130987540641186066581343019053627329/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0060.rows BesselBatch0060.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0060.rows BesselBatch0060.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0060.rows BesselBatch0060.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0060.rows BesselBatch0060.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0060.rows BesselBatch0060.accepted ⟨39,by decide⟩
]
theorem rightAccepted : besselPointCheck (675593031412799345146219024417504863687/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (675593031412799345146219024417504863687/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0519.rows BesselBatch0519.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0519.rows BesselBatch0519.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0519.rows BesselBatch0519.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0519.rows BesselBatch0519.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0519.rows BesselBatch0519.accepted ⟨8,by decide⟩
]
theorem midAccepted : besselPointCheck (2700317050366239876359019391854063354703/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (2700317050366239876359019391854063354703/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0048.rows ScalarLogs0048.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0048.rows ScalarLogs0048.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0048.rows ScalarLogs0048.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0048.rows ScalarLogs0048.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0048.rows ScalarLogs0048.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0048.rows ScalarLogs0048.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0048.rows ScalarLogs0048.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0048.rows ScalarLogs0048.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0048.rows ScalarLogs0048.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0048.rows ScalarLogs0048.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0048.rows ScalarLogs0048.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0048.rows ScalarLogs0048.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0048.rows ScalarLogs0048.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0048.rows ScalarLogs0048.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0048.rows ScalarLogs0048.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0048.rows ScalarLogs0048.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0024.bracket0386 BracketBatch0024.bracket0387 (2700317050366239876359019391854063354703/20000000000000000000000000000000000000000) (62580910784339906531322171557638113/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0024.bracket0386 BracketBatch0024.bracket0387
  (2700317050366239876359019391854063354703/20000000000000000000000000000000000000000) (62580910784339906531322171557638113/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0386
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0387
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0060.rows BesselBatch0060.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0060.rows BesselBatch0060.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0060.rows BesselBatch0060.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0060.rows BesselBatch0060.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0060.rows BesselBatch0060.accepted ⟨34,by decide⟩
]
theorem leftAccepted : besselPointCheck (1351186062825598690292438048835009727371/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1351186062825598690292438048835009727371/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0060.rows BesselBatch0060.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0060.rows BesselBatch0060.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0060.rows BesselBatch0060.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0060.rows BesselBatch0060.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0060.rows BesselBatch0060.accepted ⟨49,by decide⟩
]
theorem rightAccepted : besselPointCheck (676620653544145582468218898997509113387/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (676620653544145582468218898997509113387/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0519.rows BesselBatch0519.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0519.rows BesselBatch0519.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0519.rows BesselBatch0519.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0519.rows BesselBatch0519.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0519.rows BesselBatch0519.accepted ⟨13,by decide⟩
]
theorem midAccepted : besselPointCheck (540885473982777971045775169366005590829/4000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (540885473982777971045775169366005590829/4000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0048.rows ScalarLogs0048.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0048.rows ScalarLogs0048.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0048.rows ScalarLogs0048.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0048.rows ScalarLogs0048.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0048.rows ScalarLogs0048.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0048.rows ScalarLogs0048.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0048.rows ScalarLogs0048.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0048.rows ScalarLogs0048.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0048.rows ScalarLogs0048.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0048.rows ScalarLogs0048.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0048.rows ScalarLogs0048.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0048.rows ScalarLogs0048.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0048.rows ScalarLogs0048.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0048.rows ScalarLogs0048.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0048.rows ScalarLogs0048.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0048.rows ScalarLogs0048.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0024.bracket0387 BracketBatch0024.bracket0388 (540885473982777971045775169366005590829/4000000000000000000000000000000000000000) (125916397995848638575651804386535331/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0024.bracket0387 BracketBatch0024.bracket0388
  (540885473982777971045775169366005590829/4000000000000000000000000000000000000000) (125916397995848638575651804386535331/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0387
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0388
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0060.rows BesselBatch0060.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0060.rows BesselBatch0060.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0060.rows BesselBatch0060.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0060.rows BesselBatch0060.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0060.rows BesselBatch0060.accepted ⟨44,by decide⟩
]
theorem leftAccepted : besselPointCheck (1353241307088291164936437797995018226771/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1353241307088291164936437797995018226771/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0060.rows BesselBatch0060.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0060.rows BesselBatch0060.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0060.rows BesselBatch0060.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0060.rows BesselBatch0060.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0060.rows BesselBatch0060.accepted ⟨59,by decide⟩
]
theorem rightAccepted : besselPointCheck (1355296720606870923726255811074048772591/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1355296720606870923726255811074048772591/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0519.rows BesselBatch0519.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0519.rows BesselBatch0519.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0519.rows BesselBatch0519.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0519.rows BesselBatch0519.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0519.rows BesselBatch0519.accepted ⟨18,by decide⟩
]
theorem midAccepted : besselPointCheck (1354269013847581044331346804534533499681/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1354269013847581044331346804534533499681/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0048.rows ScalarLogs0048.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0048.rows ScalarLogs0048.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0048.rows ScalarLogs0048.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0048.rows ScalarLogs0048.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0048.rows ScalarLogs0048.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0048.rows ScalarLogs0048.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0048.rows ScalarLogs0048.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0048.rows ScalarLogs0048.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0048.rows ScalarLogs0048.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0048.rows ScalarLogs0048.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0048.rows ScalarLogs0048.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0048.rows ScalarLogs0048.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0048.rows ScalarLogs0048.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0048.rows ScalarLogs0048.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0048.rows ScalarLogs0048.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0048.rows ScalarLogs0048.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0024.bracket0388 BracketBatch0024.bracket0389 (1354269013847581044331346804534533499681/10000000000000000000000000000000000000000) (506697552708170217405106787645687/20000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0024.bracket0388 BracketBatch0024.bracket0389
  (1354269013847581044331346804534533499681/10000000000000000000000000000000000000000) (506697552708170217405106787645687/20000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0388
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0389
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0060.rows BesselBatch0060.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0060.rows BesselBatch0060.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0060.rows BesselBatch0060.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0060.rows BesselBatch0060.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0060.rows BesselBatch0060.accepted ⟨54,by decide⟩
]
theorem leftAccepted : besselPointCheck (338824180151717730931563952768512193147/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (338824180151717730931563952768512193147/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0061.rows BesselBatch0061.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0061.rows BesselBatch0061.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0061.rows BesselBatch0061.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0061.rows BesselBatch0061.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0061.rows BesselBatch0061.accepted ⟨5,by decide⟩
]
theorem rightAccepted : besselPointCheck (1357352303659611265202277730003261227747/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1357352303659611265202277730003261227747/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0519.rows BesselBatch0519.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0519.rows BesselBatch0519.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0519.rows BesselBatch0519.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0519.rows BesselBatch0519.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0519.rows BesselBatch0519.accepted ⟨23,by decide⟩
]
theorem midAccepted : besselPointCheck (542529804853296437785706708215462000067/4000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (542529804853296437785706708215462000067/4000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0048.rows ScalarLogs0048.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0048.rows ScalarLogs0048.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0048.rows ScalarLogs0048.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0048.rows ScalarLogs0048.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0048.rows ScalarLogs0048.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0048.rows ScalarLogs0048.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0048.rows ScalarLogs0048.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0048.rows ScalarLogs0048.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0048.rows ScalarLogs0048.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0048.rows ScalarLogs0048.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0048.rows ScalarLogs0048.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0048.rows ScalarLogs0048.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0048.rows ScalarLogs0048.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0048.rows ScalarLogs0048.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0048.rows ScalarLogs0048.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0048.rows ScalarLogs0048.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0024.bracket0389 BracketBatch0024.bracket0390 (542529804853296437785706708215462000067/4000000000000000000000000000000000000000) (63717901252795044916209180531572489/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0024.bracket0389 BracketBatch0024.bracket0390
  (542529804853296437785706708215462000067/4000000000000000000000000000000000000000) (63717901252795044916209180531572489/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0389
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0390
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0060.rows BesselBatch0060.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0060.rows BesselBatch0060.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0060.rows BesselBatch0060.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0060.rows BesselBatch0060.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0061.rows BesselBatch0061.accepted ⟨0,by decide⟩
]
theorem leftAccepted : besselPointCheck (42417259489362852037571179062601913367/312500000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (42417259489362852037571179062601913367/312500000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0061.rows BesselBatch0061.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0061.rows BesselBatch0061.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0061.rows BesselBatch0061.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0061.rows BesselBatch0061.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0061.rows BesselBatch0061.accepted ⟨15,by decide⟩
]
theorem rightAccepted : besselPointCheck (54376322260996267875431662233248344351/400000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (54376322260996267875431662233248344351/400000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0519.rows BesselBatch0519.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0519.rows BesselBatch0519.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0519.rows BesselBatch0519.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0519.rows BesselBatch0519.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0519.rows BesselBatch0519.accepted ⟨28,by decide⟩
]
theorem midAccepted : besselPointCheck (2716760360184517962088069285834469836519/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (2716760360184517962088069285834469836519/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0048.rows ScalarLogs0048.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0048.rows ScalarLogs0048.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0048.rows ScalarLogs0048.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0048.rows ScalarLogs0048.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0048.rows ScalarLogs0048.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0048.rows ScalarLogs0048.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0048.rows ScalarLogs0048.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0048.rows ScalarLogs0048.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0048.rows ScalarLogs0048.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0048.rows ScalarLogs0048.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0048.rows ScalarLogs0048.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0048.rows ScalarLogs0048.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0048.rows ScalarLogs0048.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0048.rows ScalarLogs0048.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0048.rows ScalarLogs0048.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0048.rows ScalarLogs0048.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0024.bracket0390 BracketBatch0024.bracket0391 (2716760360184517962088069285834469836519/20000000000000000000000000000000000000000) (12820065139147464244603995595426827/500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0024.bracket0390 BracketBatch0024.bracket0391
  (2716760360184517962088069285834469836519/20000000000000000000000000000000000000000) (12820065139147464244603995595426827/500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0390
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0391
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0061.rows BesselBatch0061.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0061.rows BesselBatch0061.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0061.rows BesselBatch0061.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0061.rows BesselBatch0061.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0061.rows BesselBatch0061.accepted ⟨10,by decide⟩
]
theorem leftAccepted : besselPointCheck (339852014131226674221447888957802152193/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (339852014131226674221447888957802152193/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0061.rows BesselBatch0061.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0061.rows BesselBatch0061.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0061.rows BesselBatch0061.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0061.rows BesselBatch0061.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0061.rows BesselBatch0061.accepted ⟨25,by decide⟩
]
theorem rightAccepted : besselPointCheck (1361463979481273159659988638061062751767/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1361463979481273159659988638061062751767/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0519.rows BesselBatch0519.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0519.rows BesselBatch0519.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0519.rows BesselBatch0519.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0519.rows BesselBatch0519.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0519.rows BesselBatch0519.accepted ⟨33,by decide⟩
]
theorem midAccepted : besselPointCheck (2720872036006179856545780193892271360539/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (2720872036006179856545780193892271360539/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0048.rows ScalarLogs0048.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0048.rows ScalarLogs0048.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0048.rows ScalarLogs0048.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0048.rows ScalarLogs0048.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0048.rows ScalarLogs0048.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0048.rows ScalarLogs0048.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0048.rows ScalarLogs0048.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0048.rows ScalarLogs0048.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0048.rows ScalarLogs0048.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0048.rows ScalarLogs0048.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0048.rows ScalarLogs0048.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0048.rows ScalarLogs0048.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0048.rows ScalarLogs0048.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0048.rows ScalarLogs0048.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0048.rows ScalarLogs0048.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0048.rows ScalarLogs0048.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0024.bracket0391 BracketBatch0024.bracket0392 (2720872036006179856545780193892271360539/20000000000000000000000000000000000000000) (257937890522679583744369610019642203/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0024.bracket0391 BracketBatch0024.bracket0392
  (2720872036006179856545780193892271360539/20000000000000000000000000000000000000000) (257937890522679583744369610019642203/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0391
