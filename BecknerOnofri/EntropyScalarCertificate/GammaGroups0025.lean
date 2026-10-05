import BecknerOnofri.EntropyScalarCertificate.Bessel0031
import BecknerOnofri.EntropyScalarCertificate.Bessel0032
import BecknerOnofri.EntropyScalarCertificate.Bessel0504
import BecknerOnofri.EntropyScalarCertificate.Bessel0505
import BecknerOnofri.EntropyScalarCertificate.Brackets0012
import BecknerOnofri.EntropyScalarCertificate.Brackets0013
import BecknerOnofri.EntropyScalarCertificate.Logs0025
import BecknerOnofri.ScalarElementaryComposition
import BecknerOnofri.ScalarGammaEnclosure
import BecknerOnofri.ScalarLogBesselEndpoints
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0200
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0031.rows BesselBatch0031.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0031.rows BesselBatch0031.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0031.rows BesselBatch0031.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0031.rows BesselBatch0031.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0031.rows BesselBatch0031.accepted ⟨20,by decide⟩
]
theorem leftAccepted : besselPointCheck (242382084965344048667115747175696062539/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (242382084965344048667115747175696062539/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0031.rows BesselBatch0031.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0031.rows BesselBatch0031.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0031.rows BesselBatch0031.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0031.rows BesselBatch0031.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0031.rows BesselBatch0031.accepted ⟨35,by decide⟩
]
theorem rightAccepted : besselPointCheck (971556701935101517634238685008119893909/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (971556701935101517634238685008119893909/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0504.rows BesselBatch0504.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0504.rows BesselBatch0504.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0504.rows BesselBatch0504.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0504.rows BesselBatch0504.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0504.rows BesselBatch0504.accepted ⟨38,by decide⟩
]
theorem midAccepted : besselPointCheck (388217008359295542460540334742180828813/4000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (388217008359295542460540334742180828813/4000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0025.rows ScalarLogs0025.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0025.rows ScalarLogs0025.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0025.rows ScalarLogs0025.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0025.rows ScalarLogs0025.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0025.rows ScalarLogs0025.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0025.rows ScalarLogs0025.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0025.rows ScalarLogs0025.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0025.rows ScalarLogs0025.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0025.rows ScalarLogs0025.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0025.rows ScalarLogs0025.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0025.rows ScalarLogs0025.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0025.rows ScalarLogs0025.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0025.rows ScalarLogs0025.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0025.rows ScalarLogs0025.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0025.rows ScalarLogs0025.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0025.rows ScalarLogs0025.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0012.bracket0200 BracketBatch0012.bracket0201 (388217008359295542460540334742180828813/4000000000000000000000000000000000000000) (67399985669102802940855489828584619/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0012.bracket0200 BracketBatch0012.bracket0201
  (388217008359295542460540334742180828813/4000000000000000000000000000000000000000) (67399985669102802940855489828584619/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0200
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0201
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0031.rows BesselBatch0031.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0031.rows BesselBatch0031.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0031.rows BesselBatch0031.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0031.rows BesselBatch0031.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0031.rows BesselBatch0031.accepted ⟨30,by decide⟩
]
theorem leftAccepted : besselPointCheck (485778350967550758817119342504059946953/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (485778350967550758817119342504059946953/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0031.rows BesselBatch0031.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0031.rows BesselBatch0031.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0031.rows BesselBatch0031.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0031.rows BesselBatch0031.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0031.rows BesselBatch0031.accepted ⟨45,by decide⟩
]
theorem rightAccepted : besselPointCheck (97358518312008343781317145746695141701/1000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (97358518312008343781317145746695141701/1000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0504.rows BesselBatch0504.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0504.rows BesselBatch0504.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0504.rows BesselBatch0504.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0504.rows BesselBatch0504.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0504.rows BesselBatch0504.accepted ⟨43,by decide⟩
]
theorem midAccepted : besselPointCheck (486285471263796238861852535618767827729/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (486285471263796238861852535618767827729/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0025.rows ScalarLogs0025.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0025.rows ScalarLogs0025.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0025.rows ScalarLogs0025.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0025.rows ScalarLogs0025.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0025.rows ScalarLogs0025.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0025.rows ScalarLogs0025.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0025.rows ScalarLogs0025.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0025.rows ScalarLogs0025.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0025.rows ScalarLogs0025.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0025.rows ScalarLogs0025.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0025.rows ScalarLogs0025.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0025.rows ScalarLogs0025.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0025.rows ScalarLogs0025.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0025.rows ScalarLogs0025.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0025.rows ScalarLogs0025.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0025.rows ScalarLogs0025.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0012.bracket0201 BracketBatch0012.bracket0202 (486285471263796238861852535618767827729/5000000000000000000000000000000000000000) (16991232958379448399925657663351173/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0012.bracket0201 BracketBatch0012.bracket0202
  (486285471263796238861852535618767827729/5000000000000000000000000000000000000000) (16991232958379448399925657663351173/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0201
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0202
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0031.rows BesselBatch0031.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0031.rows BesselBatch0031.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0031.rows BesselBatch0031.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0031.rows BesselBatch0031.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0031.rows BesselBatch0031.accepted ⟨40,by decide⟩
]
theorem leftAccepted : besselPointCheck (973585183120083437813171457466951417007/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (973585183120083437813171457466951417007/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0031.rows BesselBatch0031.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0031.rows BesselBatch0031.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0031.rows BesselBatch0031.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0031.rows BesselBatch0031.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0031.rows BesselBatch0031.accepted ⟨55,by decide⟩
]
theorem rightAccepted : besselPointCheck (975613783675659769473638434777508939427/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (975613783675659769473638434777508939427/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0504.rows BesselBatch0504.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0504.rows BesselBatch0504.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0504.rows BesselBatch0504.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0504.rows BesselBatch0504.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0504.rows BesselBatch0504.accepted ⟨48,by decide⟩
]
theorem midAccepted : besselPointCheck (974599483397871603643404946122230178217/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (974599483397871603643404946122230178217/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0025.rows ScalarLogs0025.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0025.rows ScalarLogs0025.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0025.rows ScalarLogs0025.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0025.rows ScalarLogs0025.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0025.rows ScalarLogs0025.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0025.rows ScalarLogs0025.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0025.rows ScalarLogs0025.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0025.rows ScalarLogs0025.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0025.rows ScalarLogs0025.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0025.rows ScalarLogs0025.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0025.rows ScalarLogs0025.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0025.rows ScalarLogs0025.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0025.rows ScalarLogs0025.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0025.rows ScalarLogs0025.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0025.rows ScalarLogs0025.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0025.rows ScalarLogs0025.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0012.bracket0202 BracketBatch0012.bracket0203 (974599483397871603643404946122230178217/10000000000000000000000000000000000000000) (68533407845971396497077535330696647/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0012.bracket0202 BracketBatch0012.bracket0203
  (974599483397871603643404946122230178217/10000000000000000000000000000000000000000) (68533407845971396497077535330696647/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0202
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0203
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0031.rows BesselBatch0031.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0031.rows BesselBatch0031.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0031.rows BesselBatch0031.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0031.rows BesselBatch0031.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0031.rows BesselBatch0031.accepted ⟨50,by decide⟩
]
theorem leftAccepted : besselPointCheck (30487930739864367796051201086797154357/312500000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (30487930739864367796051201086797154357/312500000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0031.rows BesselBatch0031.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0031.rows BesselBatch0031.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0031.rows BesselBatch0031.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0032.rows BesselBatch0032.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0032.rows BesselBatch0032.accepted ⟨1,by decide⟩
]
theorem rightAccepted : besselPointCheck (244410625965312713942931151221406726803/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (244410625965312713942931151221406726803/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0504.rows BesselBatch0504.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0504.rows BesselBatch0504.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0504.rows BesselBatch0504.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0504.rows BesselBatch0504.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0504.rows BesselBatch0504.accepted ⟨53,by decide⟩
]
theorem midAccepted : besselPointCheck (488314071884227656311340759915783961659/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (488314071884227656311340759915783961659/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0025.rows ScalarLogs0025.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0025.rows ScalarLogs0025.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0025.rows ScalarLogs0025.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0025.rows ScalarLogs0025.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0025.rows ScalarLogs0025.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0025.rows ScalarLogs0025.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0025.rows ScalarLogs0025.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0025.rows ScalarLogs0025.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0025.rows ScalarLogs0025.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0025.rows ScalarLogs0025.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0025.rows ScalarLogs0025.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0025.rows ScalarLogs0025.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0025.rows ScalarLogs0025.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0025.rows ScalarLogs0025.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0025.rows ScalarLogs0025.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0025.rows ScalarLogs0025.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0012.bracket0203 BracketBatch0012.bracket0204 (488314071884227656311340759915783961659/5000000000000000000000000000000000000000) (13821085692475910449489765703534297/2000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0012.bracket0203 BracketBatch0012.bracket0204
  (488314071884227656311340759915783961659/5000000000000000000000000000000000000000) (13821085692475910449489765703534297/2000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0203
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0204
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0031.rows BesselBatch0031.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0031.rows BesselBatch0031.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0031.rows BesselBatch0031.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0031.rows BesselBatch0031.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0031.rows BesselBatch0031.accepted ⟨60,by decide⟩
]
theorem leftAccepted : besselPointCheck (977642503861250855771724604885626907209/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (977642503861250855771724604885626907209/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0032.rows BesselBatch0032.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0032.rows BesselBatch0032.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0032.rows BesselBatch0032.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0032.rows BesselBatch0032.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0032.rows BesselBatch0032.accepted ⟨11,by decide⟩
]
theorem rightAccepted : besselPointCheck (122458917992044970068561938177165613001/1250000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (122458917992044970068561938177165613001/1250000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0504.rows BesselBatch0504.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0504.rows BesselBatch0504.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0504.rows BesselBatch0504.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0504.rows BesselBatch0504.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0504.rows BesselBatch0504.accepted ⟨58,by decide⟩
]
theorem midAccepted : besselPointCheck (1957313847797610616320220110302951811217/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1957313847797610616320220110302951811217/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0025.rows ScalarLogs0025.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0025.rows ScalarLogs0025.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0025.rows ScalarLogs0025.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0025.rows ScalarLogs0025.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0025.rows ScalarLogs0025.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0025.rows ScalarLogs0025.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0025.rows ScalarLogs0025.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0025.rows ScalarLogs0025.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0025.rows ScalarLogs0025.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0025.rows ScalarLogs0025.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0025.rows ScalarLogs0025.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0025.rows ScalarLogs0025.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0025.rows ScalarLogs0025.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0025.rows ScalarLogs0025.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0025.rows ScalarLogs0025.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0025.rows ScalarLogs0025.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0012.bracket0204 BracketBatch0012.bracket0205 (1957313847797610616320220110302951811217/20000000000000000000000000000000000000000) (69681008470306341454261551865332301/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0012.bracket0204 BracketBatch0012.bracket0205
  (1957313847797610616320220110302951811217/20000000000000000000000000000000000000000) (69681008470306341454261551865332301/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0204
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0205
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0032.rows BesselBatch0032.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0032.rows BesselBatch0032.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0032.rows BesselBatch0032.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0032.rows BesselBatch0032.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0032.rows BesselBatch0032.accepted ⟨6,by decide⟩
]
theorem leftAccepted : besselPointCheck (195934268787271952109699101083464980801/2000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (195934268787271952109699101083464980801/2000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0032.rows BesselBatch0032.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0032.rows BesselBatch0032.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0032.rows BesselBatch0032.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0032.rows BesselBatch0032.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0032.rows BesselBatch0032.accepted ⟨21,by decide⟩
]
theorem rightAccepted : besselPointCheck (30678134505017889383315758165210689433/312500000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (30678134505017889383315758165210689433/312500000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0504.rows BesselBatch0504.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0504.rows BesselBatch0504.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0504.rows BesselBatch0504.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0504.rows BesselBatch0504.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0504.rows BesselBatch0504.accepted ⟨63,by decide⟩
]
theorem midAccepted : besselPointCheck (1961371648096932220814599766704066965861/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1961371648096932220814599766704066965861/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0025.rows ScalarLogs0025.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0025.rows ScalarLogs0025.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0025.rows ScalarLogs0025.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0025.rows ScalarLogs0025.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0025.rows ScalarLogs0025.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0025.rows ScalarLogs0025.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0025.rows ScalarLogs0025.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0025.rows ScalarLogs0025.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0025.rows ScalarLogs0025.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0025.rows ScalarLogs0025.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0025.rows ScalarLogs0025.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0025.rows ScalarLogs0025.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0025.rows ScalarLogs0025.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0025.rows ScalarLogs0025.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0025.rows ScalarLogs0025.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0025.rows ScalarLogs0025.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0012.bracket0205 BracketBatch0012.bracket0206 (1961371648096932220814599766704066965861/20000000000000000000000000000000000000000) (70260162688971313049248653259533389/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0012.bracket0205 BracketBatch0012.bracket0206
  (1961371648096932220814599766704066965861/20000000000000000000000000000000000000000) (70260162688971313049248653259533389/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0205
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0206
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0032.rows BesselBatch0032.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0032.rows BesselBatch0032.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0032.rows BesselBatch0032.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0032.rows BesselBatch0032.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0032.rows BesselBatch0032.accepted ⟨16,by decide⟩
]
theorem leftAccepted : besselPointCheck (981700304160572460266104261286742061853/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (981700304160572460266104261286742061853/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0032.rows BesselBatch0032.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0032.rows BesselBatch0032.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0032.rows BesselBatch0032.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0032.rows BesselBatch0032.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0032.rows BesselBatch0032.accepted ⟨31,by decide⟩
]
theorem rightAccepted : besselPointCheck (983729384793558036083083684631986168383/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (983729384793558036083083684631986168383/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0505.rows BesselBatch0505.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0505.rows BesselBatch0505.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0505.rows BesselBatch0505.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0505.rows BesselBatch0505.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0505.rows BesselBatch0505.accepted ⟨4,by decide⟩
]
theorem midAccepted : besselPointCheck (491357422238532624087296986479682057559/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (491357422238532624087296986479682057559/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0025.rows ScalarLogs0025.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0025.rows ScalarLogs0025.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0025.rows ScalarLogs0025.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0025.rows ScalarLogs0025.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0025.rows ScalarLogs0025.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0025.rows ScalarLogs0025.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0025.rows ScalarLogs0025.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0025.rows ScalarLogs0025.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0025.rows ScalarLogs0025.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0025.rows ScalarLogs0025.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0025.rows ScalarLogs0025.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0025.rows ScalarLogs0025.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0025.rows ScalarLogs0025.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0025.rows ScalarLogs0025.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0025.rows ScalarLogs0025.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0025.rows ScalarLogs0025.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0012.bracket0206 BracketBatch0012.bracket0207 (491357422238532624087296986479682057559/5000000000000000000000000000000000000000) (70842905969256829294132397240613337/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0012.bracket0206 BracketBatch0012.bracket0207
  (491357422238532624087296986479682057559/5000000000000000000000000000000000000000) (70842905969256829294132397240613337/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0206
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0207
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0032.rows BesselBatch0032.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0032.rows BesselBatch0032.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0032.rows BesselBatch0032.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0032.rows BesselBatch0032.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0032.rows BesselBatch0032.accepted ⟨26,by decide⟩
]
theorem leftAccepted : besselPointCheck (49186469239677901804154184231599308419/500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (49186469239677901804154184231599308419/500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0032.rows BesselBatch0032.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0032.rows BesselBatch0032.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0032.rows BesselBatch0032.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0032.rows BesselBatch0032.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0032.rows BesselBatch0032.accepted ⟨41,by decide⟩
]
theorem rightAccepted : besselPointCheck (492879293047534433034587290367922376561/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (492879293047534433034587290367922376561/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0505.rows BesselBatch0505.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0505.rows BesselBatch0505.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0505.rows BesselBatch0505.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0505.rows BesselBatch0505.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0505.rows BesselBatch0505.accepted ⟨9,by decide⟩
]
theorem midAccepted : besselPointCheck (984743985444313451076129132683915460751/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (984743985444313451076129132683915460751/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0025.rows ScalarLogs0025.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0025.rows ScalarLogs0025.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0025.rows ScalarLogs0025.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0025.rows ScalarLogs0025.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0025.rows ScalarLogs0025.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0025.rows ScalarLogs0025.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0025.rows ScalarLogs0025.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0025.rows ScalarLogs0025.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0025.rows ScalarLogs0025.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0025.rows ScalarLogs0025.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0025.rows ScalarLogs0025.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0025.rows ScalarLogs0025.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0025.rows ScalarLogs0025.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0025.rows ScalarLogs0025.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0025.rows ScalarLogs0025.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0025.rows ScalarLogs0025.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0012.bracket0207 BracketBatch0013.bracket0208 (984743985444313451076129132683915460751/10000000000000000000000000000000000000000) (71429253193715427454747912769190163/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0012.bracket0207 BracketBatch0013.bracket0208
  (984743985444313451076129132683915460751/10000000000000000000000000000000000000000) (71429253193715427454747912769190163/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0207
