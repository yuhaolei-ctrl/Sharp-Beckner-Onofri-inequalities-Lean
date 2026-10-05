import BecknerOnofri.EntropyScalarCertificate.Bessel0147
import BecknerOnofri.EntropyScalarCertificate.Bessel0148
import BecknerOnofri.EntropyScalarCertificate.Bessel0562
import BecknerOnofri.EntropyScalarCertificate.Bessel0563
import BecknerOnofri.EntropyScalarCertificate.Brackets0059
import BecknerOnofri.EntropyScalarCertificate.Logs0118
import BecknerOnofri.ScalarElementaryComposition
import BecknerOnofri.ScalarGammaEnclosure
import BecknerOnofri.ScalarLogBesselEndpoints
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0944
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0147.rows BesselBatch0147.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0147.rows BesselBatch0147.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0147.rows BesselBatch0147.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0147.rows BesselBatch0147.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0147.rows BesselBatch0147.accepted ⟨36,by decide⟩
]
theorem leftAccepted : besselPointCheck (4717338253557195017403220642717745432083/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (4717338253557195017403220642717745432083/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0147.rows BesselBatch0147.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0147.rows BesselBatch0147.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0147.rows BesselBatch0147.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0147.rows BesselBatch0147.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0147.rows BesselBatch0147.accepted ⟨51,by decide⟩
]
theorem rightAccepted : besselPointCheck (2365486801230867565269726936659488095217/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (2365486801230867565269726936659488095217/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0562.rows BesselBatch0562.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0562.rows BesselBatch0562.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0562.rows BesselBatch0562.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0562.rows BesselBatch0562.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0562.rows BesselBatch0562.accepted ⟨46,by decide⟩
]
theorem midAccepted : besselPointCheck (9448311856018930147942674516036721622517/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (9448311856018930147942674516036721622517/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0118.rows ScalarLogs0118.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0118.rows ScalarLogs0118.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0118.rows ScalarLogs0118.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0118.rows ScalarLogs0118.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0118.rows ScalarLogs0118.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0118.rows ScalarLogs0118.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0118.rows ScalarLogs0118.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0118.rows ScalarLogs0118.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0118.rows ScalarLogs0118.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0118.rows ScalarLogs0118.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0118.rows ScalarLogs0118.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0118.rows ScalarLogs0118.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0118.rows ScalarLogs0118.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0118.rows ScalarLogs0118.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0118.rows ScalarLogs0118.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0118.rows ScalarLogs0118.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0059.bracket0944 BracketBatch0059.bracket0945 (9448311856018930147942674516036721622517/20000000000000000000000000000000000000000) (1387330747242160662152311544360743291/500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0059.bracket0944 BracketBatch0059.bracket0945
  (9448311856018930147942674516036721622517/20000000000000000000000000000000000000000) (1387330747242160662152311544360743291/500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0944
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0945
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0147.rows BesselBatch0147.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0147.rows BesselBatch0147.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0147.rows BesselBatch0147.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0147.rows BesselBatch0147.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0147.rows BesselBatch0147.accepted ⟨46,by decide⟩
]
theorem leftAccepted : besselPointCheck (4730973602461735130539453873318976190431/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (4730973602461735130539453873318976190431/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0147.rows BesselBatch0147.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0147.rows BesselBatch0147.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0147.rows BesselBatch0147.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0147.rows BesselBatch0147.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0147.rows BesselBatch0147.accepted ⟨61,by decide⟩
]
theorem rightAccepted : besselPointCheck (4744631639173953951103589567092038286583/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (4744631639173953951103589567092038286583/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0562.rows BesselBatch0562.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0562.rows BesselBatch0562.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0562.rows BesselBatch0562.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0562.rows BesselBatch0562.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0562.rows BesselBatch0562.accepted ⟨51,by decide⟩
]
theorem midAccepted : besselPointCheck (4737802620817844540821521720205507238507/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (4737802620817844540821521720205507238507/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0118.rows ScalarLogs0118.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0118.rows ScalarLogs0118.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0118.rows ScalarLogs0118.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0118.rows ScalarLogs0118.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0118.rows ScalarLogs0118.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0118.rows ScalarLogs0118.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0118.rows ScalarLogs0118.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0118.rows ScalarLogs0118.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0118.rows ScalarLogs0118.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0118.rows ScalarLogs0118.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0118.rows ScalarLogs0118.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0118.rows ScalarLogs0118.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0118.rows ScalarLogs0118.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0118.rows ScalarLogs0118.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0118.rows ScalarLogs0118.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0118.rows ScalarLogs0118.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0059.bracket0945 BracketBatch0059.bracket0946 (4737802620817844540821521720205507238507/10000000000000000000000000000000000000000) (7004938599826621045182281512205729671/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0059.bracket0945 BracketBatch0059.bracket0946
  (4737802620817844540821521720205507238507/10000000000000000000000000000000000000000) (7004938599826621045182281512205729671/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0945
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0946
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0147.rows BesselBatch0147.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0147.rows BesselBatch0147.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0147.rows BesselBatch0147.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0147.rows BesselBatch0147.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0147.rows BesselBatch0147.accepted ⟨56,by decide⟩
]
theorem leftAccepted : besselPointCheck (237231581958697697555179478354601914329/500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (237231581958697697555179478354601914329/500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0148.rows BesselBatch0148.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0148.rows BesselBatch0148.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0148.rows BesselBatch0148.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0148.rows BesselBatch0148.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0148.rows BesselBatch0148.accepted ⟨7,by decide⟩
]
theorem rightAccepted : besselPointCheck (951662497205289501267890386376931984651/2000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (951662497205289501267890386376931984651/2000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0562.rows BesselBatch0562.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0562.rows BesselBatch0562.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0562.rows BesselBatch0562.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0562.rows BesselBatch0562.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0562.rows BesselBatch0562.accepted ⟨56,by decide⟩
]
theorem midAccepted : besselPointCheck (1900588825040080291488608299795339641967/4000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1900588825040080291488608299795339641967/4000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0118.rows ScalarLogs0118.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0118.rows ScalarLogs0118.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0118.rows ScalarLogs0118.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0118.rows ScalarLogs0118.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0118.rows ScalarLogs0118.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0118.rows ScalarLogs0118.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0118.rows ScalarLogs0118.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0118.rows ScalarLogs0118.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0118.rows ScalarLogs0118.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0118.rows ScalarLogs0118.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0118.rows ScalarLogs0118.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0118.rows ScalarLogs0118.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0118.rows ScalarLogs0118.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0118.rows ScalarLogs0118.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0118.rows ScalarLogs0118.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0118.rows ScalarLogs0118.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0059.bracket0946 BracketBatch0059.bracket0947 (1900588825040080291488608299795339641967/4000000000000000000000000000000000000000) (7073750207919810308438352277642050503/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0059.bracket0946 BracketBatch0059.bracket0947
  (1900588825040080291488608299795339641967/4000000000000000000000000000000000000000) (7073750207919810308438352277642050503/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0946
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0947
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0147.rows BesselBatch0147.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0147.rows BesselBatch0147.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0148.rows BesselBatch0148.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0148.rows BesselBatch0148.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0148.rows BesselBatch0148.accepted ⟨2,by decide⟩
]
theorem leftAccepted : besselPointCheck (1189578121506611876584862982971164980813/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1189578121506611876584862982971164980813/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0148.rows BesselBatch0148.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0148.rows BesselBatch0148.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0148.rows BesselBatch0148.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0148.rows BesselBatch0148.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0148.rows BesselBatch0148.accepted ⟨17,by decide⟩
]
theorem rightAccepted : besselPointCheck (2386008133069556760584846565771363859733/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (2386008133069556760584846565771363859733/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0562.rows BesselBatch0562.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0562.rows BesselBatch0562.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0562.rows BesselBatch0562.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0562.rows BesselBatch0562.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0562.rows BesselBatch0562.accepted ⟨61,by decide⟩
]
theorem midAccepted : besselPointCheck (4765164376082780513754572531713693821359/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (4765164376082780513754572531713693821359/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0118.rows ScalarLogs0118.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0118.rows ScalarLogs0118.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0118.rows ScalarLogs0118.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0118.rows ScalarLogs0118.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0118.rows ScalarLogs0118.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0118.rows ScalarLogs0118.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0118.rows ScalarLogs0118.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0118.rows ScalarLogs0118.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0118.rows ScalarLogs0118.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0118.rows ScalarLogs0118.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0118.rows ScalarLogs0118.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0118.rows ScalarLogs0118.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0118.rows ScalarLogs0118.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0118.rows ScalarLogs0118.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0118.rows ScalarLogs0118.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0118.rows ScalarLogs0118.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0059.bracket0947 BracketBatch0059.bracket0948 (4765164376082780513754572531713693821359/10000000000000000000000000000000000000000) (28572366628438147565689035592268607421/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0059.bracket0947 BracketBatch0059.bracket0948
  (4765164376082780513754572531713693821359/10000000000000000000000000000000000000000) (28572366628438147565689035592268607421/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0947
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0948
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0148.rows BesselBatch0148.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0148.rows BesselBatch0148.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0148.rows BesselBatch0148.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0148.rows BesselBatch0148.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0148.rows BesselBatch0148.accepted ⟨12,by decide⟩
]
theorem leftAccepted : besselPointCheck (4772016266139113521169693131542727719463/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (4772016266139113521169693131542727719463/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0148.rows BesselBatch0148.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0148.rows BesselBatch0148.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0148.rows BesselBatch0148.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0148.rows BesselBatch0148.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0148.rows BesselBatch0148.accepted ⟨27,by decide⟩
]
theorem rightAccepted : besselPointCheck (2392871551713105827337996538093931167951/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (2392871551713105827337996538093931167951/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0562.rows BesselBatch0562.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0562.rows BesselBatch0562.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0563.rows BesselBatch0563.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0563.rows BesselBatch0563.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0563.rows BesselBatch0563.accepted ⟨2,by decide⟩
]
theorem midAccepted : besselPointCheck (1911551873913065035169137241546118011073/4000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1911551873913065035169137241546118011073/4000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0118.rows ScalarLogs0118.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0118.rows ScalarLogs0118.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0118.rows ScalarLogs0118.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0118.rows ScalarLogs0118.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0118.rows ScalarLogs0118.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0118.rows ScalarLogs0118.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0118.rows ScalarLogs0118.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0118.rows ScalarLogs0118.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0118.rows ScalarLogs0118.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0118.rows ScalarLogs0118.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0118.rows ScalarLogs0118.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0118.rows ScalarLogs0118.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0118.rows ScalarLogs0118.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0118.rows ScalarLogs0118.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0118.rows ScalarLogs0118.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0118.rows ScalarLogs0118.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0059.bracket0948 BracketBatch0059.bracket0949 (1911551873913065035169137241546118011073/4000000000000000000000000000000000000000) (1442593211808894118650340662741894691/500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0059.bracket0948 BracketBatch0059.bracket0949
  (1911551873913065035169137241546118011073/4000000000000000000000000000000000000000) (1442593211808894118650340662741894691/500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0948
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0949
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0148.rows BesselBatch0148.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0148.rows BesselBatch0148.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0148.rows BesselBatch0148.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0148.rows BesselBatch0148.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0148.rows BesselBatch0148.accepted ⟨22,by decide⟩
]
theorem leftAccepted : besselPointCheck (4785743103426211654675993076187862335899/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (4785743103426211654675993076187862335899/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0148.rows BesselBatch0148.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0148.rows BesselBatch0148.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0148.rows BesselBatch0148.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0148.rows BesselBatch0148.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0148.rows BesselBatch0148.accepted ⟨37,by decide⟩
]
theorem rightAccepted : besselPointCheck (4799493122603499618851579143190053866797/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (4799493122603499618851579143190053866797/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0563.rows BesselBatch0563.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0563.rows BesselBatch0563.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0563.rows BesselBatch0563.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0563.rows BesselBatch0563.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0563.rows BesselBatch0563.accepted ⟨7,by decide⟩
]
theorem midAccepted : besselPointCheck (1198154528253713909190946527422239525337/2500000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1198154528253713909190946527422239525337/2500000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0118.rows ScalarLogs0118.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0118.rows ScalarLogs0118.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0118.rows ScalarLogs0118.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0118.rows ScalarLogs0118.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0118.rows ScalarLogs0118.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0118.rows ScalarLogs0118.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0118.rows ScalarLogs0118.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0118.rows ScalarLogs0118.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0118.rows ScalarLogs0118.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0118.rows ScalarLogs0118.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0118.rows ScalarLogs0118.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0118.rows ScalarLogs0118.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0118.rows ScalarLogs0118.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0118.rows ScalarLogs0118.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0118.rows ScalarLogs0118.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0118.rows ScalarLogs0118.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0059.bracket0949 BracketBatch0059.bracket0950 (1198154528253713909190946527422239525337/2500000000000000000000000000000000000000) (29133506161976315408587433807824110473/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0059.bracket0949 BracketBatch0059.bracket0950
  (1198154528253713909190946527422239525337/2500000000000000000000000000000000000000) (29133506161976315408587433807824110473/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0949
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0950
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0148.rows BesselBatch0148.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0148.rows BesselBatch0148.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0148.rows BesselBatch0148.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0148.rows BesselBatch0148.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0148.rows BesselBatch0148.accepted ⟨32,by decide⟩
]
theorem leftAccepted : besselPointCheck (2399746561301749809425789571595026933397/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (2399746561301749809425789571595026933397/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0148.rows BesselBatch0148.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0148.rows BesselBatch0148.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0148.rows BesselBatch0148.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0148.rows BesselBatch0148.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0148.rows BesselBatch0148.accepted ⟨47,by decide⟩
]
theorem rightAccepted : besselPointCheck (240663322459772307608830889357560631689/500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (240663322459772307608830889357560631689/500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0563.rows BesselBatch0563.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0563.rows BesselBatch0563.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0563.rows BesselBatch0563.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0563.rows BesselBatch0563.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0563.rows BesselBatch0563.accepted ⟨12,by decide⟩
]
theorem midAccepted : besselPointCheck (4806379785899472885514098465170633250287/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (4806379785899472885514098465170633250287/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0118.rows ScalarLogs0118.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0118.rows ScalarLogs0118.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0118.rows ScalarLogs0118.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0118.rows ScalarLogs0118.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0118.rows ScalarLogs0118.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0118.rows ScalarLogs0118.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0118.rows ScalarLogs0118.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0118.rows ScalarLogs0118.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0118.rows ScalarLogs0118.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0118.rows ScalarLogs0118.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0118.rows ScalarLogs0118.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0118.rows ScalarLogs0118.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0118.rows ScalarLogs0118.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0118.rows ScalarLogs0118.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0118.rows ScalarLogs0118.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0118.rows ScalarLogs0118.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0059.bracket0950 BracketBatch0059.bracket0951 (4806379785899472885514098465170633250287/10000000000000000000000000000000000000000) (14708652486881629014927699501918058807/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0059.bracket0950 BracketBatch0059.bracket0951
  (4806379785899472885514098465170633250287/10000000000000000000000000000000000000000) (14708652486881629014927699501918058807/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0950
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0951
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0148.rows BesselBatch0148.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0148.rows BesselBatch0148.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0148.rows BesselBatch0148.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0148.rows BesselBatch0148.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0148.rows BesselBatch0148.accepted ⟨42,by decide⟩
]
theorem leftAccepted : besselPointCheck (4813266449195446152176617787151212633777/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (4813266449195446152176617787151212633777/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0148.rows BesselBatch0148.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0148.rows BesselBatch0148.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0148.rows BesselBatch0148.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0148.rows BesselBatch0148.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0148.rows BesselBatch0148.accepted ⟨57,by decide⟩
]
theorem rightAccepted : besselPointCheck (241353160477126091743867865964076725421/500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (241353160477126091743867865964076725421/500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0563.rows BesselBatch0563.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0563.rows BesselBatch0563.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0563.rows BesselBatch0563.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0563.rows BesselBatch0563.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0563.rows BesselBatch0563.accepted ⟨17,by decide⟩
]
theorem midAccepted : besselPointCheck (9640329658737967987053975106432747142197/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (9640329658737967987053975106432747142197/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0118.rows ScalarLogs0118.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0118.rows ScalarLogs0118.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0118.rows ScalarLogs0118.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0118.rows ScalarLogs0118.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0118.rows ScalarLogs0118.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0118.rows ScalarLogs0118.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0118.rows ScalarLogs0118.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0118.rows ScalarLogs0118.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0118.rows ScalarLogs0118.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0118.rows ScalarLogs0118.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0118.rows ScalarLogs0118.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0118.rows ScalarLogs0118.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0118.rows ScalarLogs0118.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0118.rows ScalarLogs0118.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0118.rows ScalarLogs0118.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0118.rows ScalarLogs0118.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0059.bracket0951 BracketBatch0059.bracket0952 (9640329658737967987053975106432747142197/20000000000000000000000000000000000000000) (14851636650346417389005011781293124967/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0059.bracket0951 BracketBatch0059.bracket0952
  (9640329658737967987053975106432747142197/20000000000000000000000000000000000000000) (14851636650346417389005011781293124967/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0951
