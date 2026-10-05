import BecknerOnofri.EntropyScalarCertificate.Bessel0140
import BecknerOnofri.EntropyScalarCertificate.Bessel0141
import BecknerOnofri.EntropyScalarCertificate.Bessel0558
import BecknerOnofri.EntropyScalarCertificate.Bessel0559
import BecknerOnofri.EntropyScalarCertificate.Brackets0056
import BecknerOnofri.EntropyScalarCertificate.Logs0112
import BecknerOnofri.ScalarElementaryComposition
import BecknerOnofri.ScalarGammaEnclosure
import BecknerOnofri.ScalarLogBesselEndpoints
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0896
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0140.rows BesselBatch0140.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0140.rows BesselBatch0140.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0140.rows BesselBatch0140.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0140.rows BesselBatch0140.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0140.rows BesselBatch0140.accepted ⟨4,by decide⟩
]
theorem leftAccepted : besselPointCheck (31932067438494668026290223871895879121/78125000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (31932067438494668026290223871895879121/78125000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0140.rows BesselBatch0140.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0140.rows BesselBatch0140.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0140.rows BesselBatch0140.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0140.rows BesselBatch0140.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0140.rows BesselBatch0140.accepted ⟨19,by decide⟩
]
theorem rightAccepted : besselPointCheck (2049990492737010349199348504034116502449/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (2049990492737010349199348504034116502449/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0558.rows BesselBatch0558.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0558.rows BesselBatch0558.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0558.rows BesselBatch0558.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0558.rows BesselBatch0558.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0558.rows BesselBatch0558.accepted ⟨62,by decide⟩
]
theorem midAccepted : besselPointCheck (4093642808800669102881922831835452766193/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (4093642808800669102881922831835452766193/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0112.rows ScalarLogs0112.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0112.rows ScalarLogs0112.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0112.rows ScalarLogs0112.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0112.rows ScalarLogs0112.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0112.rows ScalarLogs0112.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0112.rows ScalarLogs0112.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0112.rows ScalarLogs0112.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0112.rows ScalarLogs0112.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0112.rows ScalarLogs0112.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0112.rows ScalarLogs0112.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0112.rows ScalarLogs0112.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0112.rows ScalarLogs0112.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0112.rows ScalarLogs0112.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0112.rows ScalarLogs0112.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0112.rows ScalarLogs0112.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0112.rows ScalarLogs0112.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0056.bracket0896 BracketBatch0056.bracket0897 (4093642808800669102881922831835452766193/10000000000000000000000000000000000000000) (4220958891239937916900479006942673687/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0056.bracket0896 BracketBatch0056.bracket0897
  (4093642808800669102881922831835452766193/10000000000000000000000000000000000000000) (4220958891239937916900479006942673687/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0896
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0897
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0140.rows BesselBatch0140.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0140.rows BesselBatch0140.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0140.rows BesselBatch0140.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0140.rows BesselBatch0140.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0140.rows BesselBatch0140.accepted ⟨14,by decide⟩
]
theorem leftAccepted : besselPointCheck (819996197094804139679739401613646600979/2000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (819996197094804139679739401613646600979/2000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0140.rows BesselBatch0140.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0140.rows BesselBatch0140.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0140.rows BesselBatch0140.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0140.rows BesselBatch0140.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0140.rows BesselBatch0140.accepted ⟨29,by decide⟩
]
theorem rightAccepted : besselPointCheck (411267495887643073997971776012998290939/1000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (411267495887643073997971776012998290939/1000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0558.rows BesselBatch0558.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0559.rows BesselBatch0559.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0559.rows BesselBatch0559.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0559.rows BesselBatch0559.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0559.rows BesselBatch0559.accepted ⟨3,by decide⟩
]
theorem midAccepted : besselPointCheck (1642531188870090287675682953639643182857/4000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1642531188870090287675682953639643182857/4000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0112.rows ScalarLogs0112.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0112.rows ScalarLogs0112.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0112.rows ScalarLogs0112.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0112.rows ScalarLogs0112.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0112.rows ScalarLogs0112.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0112.rows ScalarLogs0112.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0112.rows ScalarLogs0112.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0112.rows ScalarLogs0112.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0112.rows ScalarLogs0112.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0112.rows ScalarLogs0112.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0112.rows ScalarLogs0112.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0112.rows ScalarLogs0112.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0112.rows ScalarLogs0112.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0112.rows ScalarLogs0112.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0112.rows ScalarLogs0112.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0112.rows ScalarLogs0112.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0056.bracket0897 BracketBatch0056.bracket0898 (1642531188870090287675682953639643182857/4000000000000000000000000000000000000000) (3413864875024470273288942089484862701/2000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0056.bracket0897 BracketBatch0056.bracket0898
  (1642531188870090287675682953639643182857/4000000000000000000000000000000000000000) (3413864875024470273288942089484862701/2000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0897
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0898
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0140.rows BesselBatch0140.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0140.rows BesselBatch0140.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0140.rows BesselBatch0140.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0140.rows BesselBatch0140.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0140.rows BesselBatch0140.accepted ⟨24,by decide⟩
]
theorem leftAccepted : besselPointCheck (4112674958876430739979717760129982909387/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (4112674958876430739979717760129982909387/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0140.rows BesselBatch0140.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0140.rows BesselBatch0140.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0140.rows BesselBatch0140.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0140.rows BesselBatch0140.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0140.rows BesselBatch0140.accepted ⟨39,by decide⟩
]
theorem rightAccepted : besselPointCheck (4125386643902838777379970484582687341027/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (4125386643902838777379970484582687341027/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0559.rows BesselBatch0559.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0559.rows BesselBatch0559.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0559.rows BesselBatch0559.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0559.rows BesselBatch0559.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0559.rows BesselBatch0559.accepted ⟨8,by decide⟩
]
theorem midAccepted : besselPointCheck (4119030801389634758679844122356335125207/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (4119030801389634758679844122356335125207/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0112.rows ScalarLogs0112.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0112.rows ScalarLogs0112.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0112.rows ScalarLogs0112.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0112.rows ScalarLogs0112.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0112.rows ScalarLogs0112.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0112.rows ScalarLogs0112.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0112.rows ScalarLogs0112.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0112.rows ScalarLogs0112.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0112.rows ScalarLogs0112.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0112.rows ScalarLogs0112.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0112.rows ScalarLogs0112.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0112.rows ScalarLogs0112.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0112.rows ScalarLogs0112.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0112.rows ScalarLogs0112.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0112.rows ScalarLogs0112.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0112.rows ScalarLogs0112.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0056.bracket0898 BracketBatch0056.bracket0899 (4119030801389634758679844122356335125207/10000000000000000000000000000000000000000) (8628195198901173241725166736057786823/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0056.bracket0898 BracketBatch0056.bracket0899
  (4119030801389634758679844122356335125207/10000000000000000000000000000000000000000) (8628195198901173241725166736057786823/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0898
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0899
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0140.rows BesselBatch0140.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0140.rows BesselBatch0140.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0140.rows BesselBatch0140.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0140.rows BesselBatch0140.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0140.rows BesselBatch0140.accepted ⟨34,by decide⟩
]
theorem leftAccepted : besselPointCheck (128918332621963711793124077643208979407/312500000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (128918332621963711793124077643208979407/312500000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0140.rows BesselBatch0140.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0140.rows BesselBatch0140.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0140.rows BesselBatch0140.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0140.rows BesselBatch0140.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0140.rows BesselBatch0140.accepted ⟨49,by decide⟩
]
theorem rightAccepted : besselPointCheck (4138116132643166491419567696144669972001/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (4138116132643166491419567696144669972001/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0559.rows BesselBatch0559.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0559.rows BesselBatch0559.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0559.rows BesselBatch0559.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0559.rows BesselBatch0559.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0559.rows BesselBatch0559.accepted ⟨13,by decide⟩
]
theorem midAccepted : besselPointCheck (330540111061840210751981527229094292521/800000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (330540111061840210751981527229094292521/800000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0112.rows ScalarLogs0112.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0112.rows ScalarLogs0112.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0112.rows ScalarLogs0112.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0112.rows ScalarLogs0112.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0112.rows ScalarLogs0112.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0112.rows ScalarLogs0112.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0112.rows ScalarLogs0112.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0112.rows ScalarLogs0112.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0112.rows ScalarLogs0112.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0112.rows ScalarLogs0112.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0112.rows ScalarLogs0112.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0112.rows ScalarLogs0112.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0112.rows ScalarLogs0112.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0112.rows ScalarLogs0112.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0112.rows ScalarLogs0112.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0112.rows ScalarLogs0112.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0056.bracket0899 BracketBatch0056.bracket0900 (330540111061840210751981527229094292521/800000000000000000000000000000000000000) (2180630438688543354832531424751180497/1250000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0056.bracket0899 BracketBatch0056.bracket0900
  (330540111061840210751981527229094292521/800000000000000000000000000000000000000) (2180630438688543354832531424751180497/1250000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0899
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0900
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0140.rows BesselBatch0140.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0140.rows BesselBatch0140.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0140.rows BesselBatch0140.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0140.rows BesselBatch0140.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0140.rows BesselBatch0140.accepted ⟨44,by decide⟩
]
theorem leftAccepted : besselPointCheck (2069058066321583245709783848072334985999/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (2069058066321583245709783848072334985999/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0140.rows BesselBatch0140.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0140.rows BesselBatch0140.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0140.rows BesselBatch0140.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0140.rows BesselBatch0140.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0140.rows BesselBatch0140.accepted ⟨59,by decide⟩
]
theorem rightAccepted : besselPointCheck (830172703542659407412069503577095577633/2000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (830172703542659407412069503577095577633/2000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0559.rows BesselBatch0559.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0559.rows BesselBatch0559.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0559.rows BesselBatch0559.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0559.rows BesselBatch0559.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0559.rows BesselBatch0559.accepted ⟨18,by decide⟩
]
theorem midAccepted : besselPointCheck (8288979650356463528479915214030147860163/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (8288979650356463528479915214030147860163/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0112.rows ScalarLogs0112.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0112.rows ScalarLogs0112.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0112.rows ScalarLogs0112.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0112.rows ScalarLogs0112.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0112.rows ScalarLogs0112.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0112.rows ScalarLogs0112.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0112.rows ScalarLogs0112.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0112.rows ScalarLogs0112.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0112.rows ScalarLogs0112.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0112.rows ScalarLogs0112.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0112.rows ScalarLogs0112.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0112.rows ScalarLogs0112.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0112.rows ScalarLogs0112.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0112.rows ScalarLogs0112.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0112.rows ScalarLogs0112.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0112.rows ScalarLogs0112.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0056.bracket0900 BracketBatch0056.bracket0901 (8288979650356463528479915214030147860163/20000000000000000000000000000000000000000) (17635293632892843745260231116550797929/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0056.bracket0900 BracketBatch0056.bracket0901
  (8288979650356463528479915214030147860163/20000000000000000000000000000000000000000) (17635293632892843745260231116550797929/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0900
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0901
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0140.rows BesselBatch0140.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0140.rows BesselBatch0140.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0140.rows BesselBatch0140.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0140.rows BesselBatch0140.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0140.rows BesselBatch0140.accepted ⟨54,by decide⟩
]
theorem leftAccepted : besselPointCheck (2075431758856648518530173758942738944081/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (2075431758856648518530173758942738944081/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0141.rows BesselBatch0141.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0141.rows BesselBatch0141.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0141.rows BesselBatch0141.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0141.rows BesselBatch0141.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0141.rows BesselBatch0141.accepted ⟨5,by decide⟩
]
theorem rightAccepted : besselPointCheck (130113402883107757813202564316467744921/312500000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (130113402883107757813202564316467744921/312500000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0559.rows BesselBatch0559.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0559.rows BesselBatch0559.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0559.rows BesselBatch0559.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0559.rows BesselBatch0559.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0559.rows BesselBatch0559.accepted ⟨23,by decide⟩
]
theorem midAccepted : besselPointCheck (4157246204986372643541414788006222862817/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (4157246204986372643541414788006222862817/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0112.rows ScalarLogs0112.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0112.rows ScalarLogs0112.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0112.rows ScalarLogs0112.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0112.rows ScalarLogs0112.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0112.rows ScalarLogs0112.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0112.rows ScalarLogs0112.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0112.rows ScalarLogs0112.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0112.rows ScalarLogs0112.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0112.rows ScalarLogs0112.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0112.rows ScalarLogs0112.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0112.rows ScalarLogs0112.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0112.rows ScalarLogs0112.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0112.rows ScalarLogs0112.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0112.rows ScalarLogs0112.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0112.rows ScalarLogs0112.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0112.rows ScalarLogs0112.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0056.bracket0901 BracketBatch0056.bracket0902 (4157246204986372643541414788006222862817/10000000000000000000000000000000000000000) (1782715073698765249249203674659427279/1000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0056.bracket0901 BracketBatch0056.bracket0902
  (4157246204986372643541414788006222862817/10000000000000000000000000000000000000000) (1782715073698765249249203674659427279/1000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0901
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0902
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0140.rows BesselBatch0140.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0140.rows BesselBatch0140.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0140.rows BesselBatch0140.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0140.rows BesselBatch0140.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0141.rows BesselBatch0141.accepted ⟨0,by decide⟩
]
theorem leftAccepted : besselPointCheck (4163628892259448250022482058126967837469/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (4163628892259448250022482058126967837469/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0141.rows BesselBatch0141.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0141.rows BesselBatch0141.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0141.rows BesselBatch0141.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0141.rows BesselBatch0141.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0141.rows BesselBatch0141.accepted ⟨15,by decide⟩
]
theorem rightAccepted : besselPointCheck (4176412349962588618901970758929861447853/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (4176412349962588618901970758929861447853/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0559.rows BesselBatch0559.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0559.rows BesselBatch0559.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0559.rows BesselBatch0559.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0559.rows BesselBatch0559.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0559.rows BesselBatch0559.accepted ⟨28,by decide⟩
]
theorem midAccepted : besselPointCheck (4170020621111018434462226408528414642661/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (4170020621111018434462226408528414642661/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0112.rows ScalarLogs0112.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0112.rows ScalarLogs0112.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0112.rows ScalarLogs0112.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0112.rows ScalarLogs0112.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0112.rows ScalarLogs0112.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0112.rows ScalarLogs0112.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0112.rows ScalarLogs0112.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0112.rows ScalarLogs0112.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0112.rows ScalarLogs0112.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0112.rows ScalarLogs0112.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0112.rows ScalarLogs0112.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0112.rows ScalarLogs0112.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0112.rows ScalarLogs0112.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0112.rows ScalarLogs0112.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0112.rows ScalarLogs0112.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0112.rows ScalarLogs0112.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0056.bracket0902 BracketBatch0056.bracket0903 (4170020621111018434462226408528414642661/10000000000000000000000000000000000000000) (2252578104680177015476934342674380789/1250000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0056.bracket0902 BracketBatch0056.bracket0903
  (4170020621111018434462226408528414642661/10000000000000000000000000000000000000000) (2252578104680177015476934342674380789/1250000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0902
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0903
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0141.rows BesselBatch0141.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0141.rows BesselBatch0141.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0141.rows BesselBatch0141.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0141.rows BesselBatch0141.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0141.rows BesselBatch0141.accepted ⟨10,by decide⟩
]
theorem leftAccepted : besselPointCheck (83528246999251772378039415178597228957/200000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (83528246999251772378039415178597228957/200000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0141.rows BesselBatch0141.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0141.rows BesselBatch0141.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0141.rows BesselBatch0141.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0141.rows BesselBatch0141.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0141.rows BesselBatch0141.accepted ⟨25,by decide⟩
]
theorem rightAccepted : besselPointCheck (4189213985042896526967908040244751101209/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (4189213985042896526967908040244751101209/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0559.rows BesselBatch0559.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0559.rows BesselBatch0559.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0559.rows BesselBatch0559.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0559.rows BesselBatch0559.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0559.rows BesselBatch0559.accepted ⟨33,by decide⟩
]
theorem midAccepted : besselPointCheck (8365626335005485145869878799174612549059/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (8365626335005485145869878799174612549059/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0112.rows ScalarLogs0112.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0112.rows ScalarLogs0112.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0112.rows ScalarLogs0112.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0112.rows ScalarLogs0112.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0112.rows ScalarLogs0112.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0112.rows ScalarLogs0112.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0112.rows ScalarLogs0112.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0112.rows ScalarLogs0112.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0112.rows ScalarLogs0112.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0112.rows ScalarLogs0112.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0112.rows ScalarLogs0112.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0112.rows ScalarLogs0112.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0112.rows ScalarLogs0112.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0112.rows ScalarLogs0112.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0112.rows ScalarLogs0112.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0112.rows ScalarLogs0112.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0056.bracket0903 BracketBatch0056.bracket0904 (8365626335005485145869878799174612549059/20000000000000000000000000000000000000000) (18215725996759193037297444663204901557/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0056.bracket0903 BracketBatch0056.bracket0904
  (8365626335005485145869878799174612549059/20000000000000000000000000000000000000000) (18215725996759193037297444663204901557/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0903
