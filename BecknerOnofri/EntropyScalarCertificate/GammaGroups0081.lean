module

public import BecknerOnofri.EntropyScalarCertificate.Bessel0101
public import BecknerOnofri.EntropyScalarCertificate.Bessel0102
public import BecknerOnofri.EntropyScalarCertificate.Bessel0539
public import BecknerOnofri.EntropyScalarCertificate.Bessel0540
public import BecknerOnofri.EntropyScalarCertificate.Brackets0040
public import BecknerOnofri.EntropyScalarCertificate.Brackets0041
public import BecknerOnofri.EntropyScalarCertificate.Logs0081
public import BecknerOnofri.ScalarElementaryComposition
public import BecknerOnofri.ScalarGammaEnclosure
public import BecknerOnofri.ScalarLogBesselEndpoints

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0648
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0101.rows BesselBatch0101.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0101.rows BesselBatch0101.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0101.rows BesselBatch0101.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0101.rows BesselBatch0101.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0101.rows BesselBatch0101.accepted ⟨20,by decide⟩
]
theorem leftAccepted : besselPointCheck (1894187986612834537212138444399060764039/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1894187986612834537212138444399060764039/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0101.rows BesselBatch0101.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0101.rows BesselBatch0101.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0101.rows BesselBatch0101.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0101.rows BesselBatch0101.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0101.rows BesselBatch0101.accepted ⟨35,by decide⟩
]
theorem rightAccepted : besselPointCheck (474074312049097468813358818805314483241/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (474074312049097468813358818805314483241/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0539.rows BesselBatch0539.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0539.rows BesselBatch0539.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0539.rows BesselBatch0539.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0539.rows BesselBatch0539.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0539.rows BesselBatch0539.accepted ⟨38,by decide⟩
]
theorem midAccepted : besselPointCheck (3790485234809224412465573719620318697003/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (3790485234809224412465573719620318697003/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0081.rows ScalarLogs0081.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0081.rows ScalarLogs0081.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0081.rows ScalarLogs0081.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0081.rows ScalarLogs0081.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0081.rows ScalarLogs0081.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0081.rows ScalarLogs0081.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0081.rows ScalarLogs0081.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0081.rows ScalarLogs0081.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0081.rows ScalarLogs0081.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0081.rows ScalarLogs0081.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0081.rows ScalarLogs0081.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0081.rows ScalarLogs0081.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0081.rows ScalarLogs0081.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0081.rows ScalarLogs0081.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0081.rows ScalarLogs0081.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0081.rows ScalarLogs0081.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0040.bracket0648 BracketBatch0040.bracket0649 (3790485234809224412465573719620318697003/20000000000000000000000000000000000000000) (236812179583170951868934791062559711/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0040.bracket0648 BracketBatch0040.bracket0649
  (3790485234809224412465573719620318697003/20000000000000000000000000000000000000000) (236812179583170951868934791062559711/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0648
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0649
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0101.rows BesselBatch0101.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0101.rows BesselBatch0101.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0101.rows BesselBatch0101.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0101.rows BesselBatch0101.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0101.rows BesselBatch0101.accepted ⟨30,by decide⟩
]
theorem leftAccepted : besselPointCheck (1896297248196389875253435275221257932961/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1896297248196389875253435275221257932961/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0101.rows BesselBatch0101.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0101.rows BesselBatch0101.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0101.rows BesselBatch0101.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0101.rows BesselBatch0101.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0101.rows BesselBatch0101.accepted ⟨45,by decide⟩
]
theorem rightAccepted : besselPointCheck (1898406756480081043846995696483975641021/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1898406756480081043846995696483975641021/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0539.rows BesselBatch0539.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0539.rows BesselBatch0539.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0539.rows BesselBatch0539.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0539.rows BesselBatch0539.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0539.rows BesselBatch0539.accepted ⟨43,by decide⟩
]
theorem midAccepted : besselPointCheck (1897352002338235459550215485852616786991/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1897352002338235459550215485852616786991/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0081.rows ScalarLogs0081.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0081.rows ScalarLogs0081.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0081.rows ScalarLogs0081.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0081.rows ScalarLogs0081.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0081.rows ScalarLogs0081.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0081.rows ScalarLogs0081.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0081.rows ScalarLogs0081.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0081.rows ScalarLogs0081.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0081.rows ScalarLogs0081.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0081.rows ScalarLogs0081.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0081.rows ScalarLogs0081.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0081.rows ScalarLogs0081.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0081.rows ScalarLogs0081.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0081.rows ScalarLogs0081.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0081.rows ScalarLogs0081.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0081.rows ScalarLogs0081.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0040.bracket0649 BracketBatch0040.bracket0650 (1897352002338235459550215485852616786991/10000000000000000000000000000000000000000) (951358223000293722899841085367166929/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0040.bracket0649 BracketBatch0040.bracket0650
  (1897352002338235459550215485852616786991/10000000000000000000000000000000000000000) (951358223000293722899841085367166929/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0649
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0650
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0101.rows BesselBatch0101.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0101.rows BesselBatch0101.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0101.rows BesselBatch0101.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0101.rows BesselBatch0101.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0101.rows BesselBatch0101.accepted ⟨40,by decide⟩
]
theorem leftAccepted : besselPointCheck (949203378240040521923497848241987820509/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (949203378240040521923497848241987820509/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0101.rows BesselBatch0101.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0101.rows BesselBatch0101.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0101.rows BesselBatch0101.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0101.rows BesselBatch0101.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0101.rows BesselBatch0101.accepted ⟨55,by decide⟩
]
theorem rightAccepted : besselPointCheck (380103302356429633654194855420278944073/2000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (380103302356429633654194855420278944073/2000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0539.rows BesselBatch0539.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0539.rows BesselBatch0539.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0539.rows BesselBatch0539.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0539.rows BesselBatch0539.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0539.rows BesselBatch0539.accepted ⟨48,by decide⟩
]
theorem midAccepted : besselPointCheck (3798923268262229212117969973585370361383/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (3798923268262229212117969973585370361383/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0081.rows ScalarLogs0081.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0081.rows ScalarLogs0081.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0081.rows ScalarLogs0081.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0081.rows ScalarLogs0081.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0081.rows ScalarLogs0081.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0081.rows ScalarLogs0081.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0081.rows ScalarLogs0081.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0081.rows ScalarLogs0081.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0081.rows ScalarLogs0081.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0081.rows ScalarLogs0081.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0081.rows ScalarLogs0081.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0081.rows ScalarLogs0081.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0081.rows ScalarLogs0081.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0081.rows ScalarLogs0081.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0081.rows ScalarLogs0081.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0081.rows ScalarLogs0081.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0040.bracket0650 BracketBatch0040.bracket0651 (3798923268262229212117969973585370361383/20000000000000000000000000000000000000000) (955481174893717009242688987131042949/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0040.bracket0650 BracketBatch0040.bracket0651
  (3798923268262229212117969973585370361383/20000000000000000000000000000000000000000) (955481174893717009242688987131042949/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0650
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0651
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0101.rows BesselBatch0101.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0101.rows BesselBatch0101.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0101.rows BesselBatch0101.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0101.rows BesselBatch0101.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0101.rows BesselBatch0101.accepted ⟨50,by decide⟩
]
theorem leftAccepted : besselPointCheck (950258255891074084135487138550697360181/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (950258255891074084135487138550697360181/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0101.rows BesselBatch0101.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0101.rows BesselBatch0101.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0101.rows BesselBatch0101.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0102.rows BesselBatch0102.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0102.rows BesselBatch0102.accepted ⟨1,by decide⟩
]
theorem rightAccepted : besselPointCheck (1902626514421019862219878256420123190263/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1902626514421019862219878256420123190263/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0539.rows BesselBatch0539.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0539.rows BesselBatch0539.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0539.rows BesselBatch0539.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0539.rows BesselBatch0539.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0539.rows BesselBatch0539.accepted ⟨53,by decide⟩
]
theorem midAccepted : besselPointCheck (6085028841925068848785364053634428657/32000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (6085028841925068848785364053634428657/32000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0081.rows ScalarLogs0081.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0081.rows ScalarLogs0081.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0081.rows ScalarLogs0081.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0081.rows ScalarLogs0081.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0081.rows ScalarLogs0081.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0081.rows ScalarLogs0081.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0081.rows ScalarLogs0081.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0081.rows ScalarLogs0081.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0081.rows ScalarLogs0081.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0081.rows ScalarLogs0081.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0081.rows ScalarLogs0081.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0081.rows ScalarLogs0081.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0081.rows ScalarLogs0081.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0081.rows ScalarLogs0081.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0081.rows ScalarLogs0081.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0081.rows ScalarLogs0081.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0040.bracket0651 BracketBatch0040.bracket0652 (6085028841925068848785364053634428657/32000000000000000000000000000000000000) (959617603947766739356231626360688427/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0040.bracket0651 BracketBatch0040.bracket0652
  (6085028841925068848785364053634428657/32000000000000000000000000000000000000) (959617603947766739356231626360688427/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0651
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0652
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0101.rows BesselBatch0101.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0101.rows BesselBatch0101.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0101.rows BesselBatch0101.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0101.rows BesselBatch0101.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0101.rows BesselBatch0101.accepted ⟨60,by decide⟩
]
theorem leftAccepted : besselPointCheck (95131325721050993110993912821006159513/500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (95131325721050993110993912821006159513/500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0102.rows BesselBatch0102.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0102.rows BesselBatch0102.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0102.rows BesselBatch0102.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0102.rows BesselBatch0102.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0102.rows BesselBatch0102.accepted ⟨11,by decide⟩
]
theorem rightAccepted : besselPointCheck (952368382357656762828307234754395948743/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (952368382357656762828307234754395948743/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0539.rows BesselBatch0539.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0539.rows BesselBatch0539.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0539.rows BesselBatch0539.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0539.rows BesselBatch0539.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0539.rows BesselBatch0539.accepted ⟨58,by decide⟩
]
theorem midAccepted : besselPointCheck (1903681639568166693938246362964457543873/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1903681639568166693938246362964457543873/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0081.rows ScalarLogs0081.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0081.rows ScalarLogs0081.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0081.rows ScalarLogs0081.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0081.rows ScalarLogs0081.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0081.rows ScalarLogs0081.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0081.rows ScalarLogs0081.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0081.rows ScalarLogs0081.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0081.rows ScalarLogs0081.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0081.rows ScalarLogs0081.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0081.rows ScalarLogs0081.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0081.rows ScalarLogs0081.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0081.rows ScalarLogs0081.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0081.rows ScalarLogs0081.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0081.rows ScalarLogs0081.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0081.rows ScalarLogs0081.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0081.rows ScalarLogs0081.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0040.bracket0652 BracketBatch0040.bracket0653 (1903681639568166693938246362964457543873/10000000000000000000000000000000000000000) (481883770067024173667090009234490013/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0040.bracket0652 BracketBatch0040.bracket0653
  (1903681639568166693938246362964457543873/10000000000000000000000000000000000000000) (481883770067024173667090009234490013/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0652
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0653
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0102.rows BesselBatch0102.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0102.rows BesselBatch0102.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0102.rows BesselBatch0102.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0102.rows BesselBatch0102.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0102.rows BesselBatch0102.accepted ⟨6,by decide⟩
]
theorem leftAccepted : besselPointCheck (1904736764715313525656614469508791897483/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1904736764715313525656614469508791897483/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0102.rows BesselBatch0102.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0102.rows BesselBatch0102.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0102.rows BesselBatch0102.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0102.rows BesselBatch0102.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0102.rows BesselBatch0102.accepted ⟨21,by decide⟩
]
theorem rightAccepted : besselPointCheck (1906847262983835643025740357528834364097/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1906847262983835643025740357528834364097/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0539.rows BesselBatch0539.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0539.rows BesselBatch0539.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0539.rows BesselBatch0539.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0539.rows BesselBatch0539.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0539.rows BesselBatch0539.accepted ⟨63,by decide⟩
]
theorem midAccepted : besselPointCheck (190579201384957458434117741351881313079/1000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (190579201384957458434117741351881313079/1000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0081.rows ScalarLogs0081.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0081.rows ScalarLogs0081.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0081.rows ScalarLogs0081.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0081.rows ScalarLogs0081.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0081.rows ScalarLogs0081.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0081.rows ScalarLogs0081.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0081.rows ScalarLogs0081.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0081.rows ScalarLogs0081.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0081.rows ScalarLogs0081.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0081.rows ScalarLogs0081.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0081.rows ScalarLogs0081.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0081.rows ScalarLogs0081.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0081.rows ScalarLogs0081.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0081.rows ScalarLogs0081.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0081.rows ScalarLogs0081.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0081.rows ScalarLogs0081.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0040.bracket0653 BracketBatch0040.bracket0654 (190579201384957458434117741351881313079/1000000000000000000000000000000000000000) (967931013460975864293336796941087833/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0040.bracket0653 BracketBatch0040.bracket0654
  (190579201384957458434117741351881313079/1000000000000000000000000000000000000000) (967931013460975864293336796941087833/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0653
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0654
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0102.rows BesselBatch0102.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0102.rows BesselBatch0102.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0102.rows BesselBatch0102.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0102.rows BesselBatch0102.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0102.rows BesselBatch0102.accepted ⟨16,by decide⟩
]
theorem leftAccepted : besselPointCheck (953423631491917821512870178764417182047/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (953423631491917821512870178764417182047/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0102.rows BesselBatch0102.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0102.rows BesselBatch0102.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0102.rows BesselBatch0102.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0102.rows BesselBatch0102.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0102.rows BesselBatch0102.accepted ⟨31,by decide⟩
]
theorem rightAccepted : besselPointCheck (477239502386395520457156430175128598039/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (477239502386395520457156430175128598039/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0540.rows BesselBatch0540.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0540.rows BesselBatch0540.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0540.rows BesselBatch0540.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0540.rows BesselBatch0540.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0540.rows BesselBatch0540.accepted ⟨4,by decide⟩
]
theorem midAccepted : besselPointCheck (610528843604706835976698572516695801/3200000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (610528843604706835976698572516695801/3200000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0081.rows ScalarLogs0081.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0081.rows ScalarLogs0081.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0081.rows ScalarLogs0081.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0081.rows ScalarLogs0081.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0081.rows ScalarLogs0081.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0081.rows ScalarLogs0081.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0081.rows ScalarLogs0081.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0081.rows ScalarLogs0081.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0081.rows ScalarLogs0081.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0081.rows ScalarLogs0081.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0081.rows ScalarLogs0081.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0081.rows ScalarLogs0081.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0081.rows ScalarLogs0081.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0081.rows ScalarLogs0081.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0081.rows ScalarLogs0081.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0081.rows ScalarLogs0081.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0040.bracket0654 BracketBatch0040.bracket0655 (610528843604706835976698572516695801/3200000000000000000000000000000000000) (243027013493447044620248473481029051/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0040.bracket0654 BracketBatch0040.bracket0655
  (610528843604706835976698572516695801/3200000000000000000000000000000000000) (243027013493447044620248473481029051/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0654
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0655
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0102.rows BesselBatch0102.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0102.rows BesselBatch0102.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0102.rows BesselBatch0102.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0102.rows BesselBatch0102.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0102.rows BesselBatch0102.accepted ⟨26,by decide⟩
]
theorem leftAccepted : besselPointCheck (1908958009545582081828625720700514392153/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1908958009545582081828625720700514392153/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0102.rows BesselBatch0102.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0102.rows BesselBatch0102.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0102.rows BesselBatch0102.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0102.rows BesselBatch0102.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0102.rows BesselBatch0102.accepted ⟨41,by decide⟩
]
theorem rightAccepted : besselPointCheck (1911069004719738391561233173612595177513/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1911069004719738391561233173612595177513/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0540.rows BesselBatch0540.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0540.rows BesselBatch0540.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0540.rows BesselBatch0540.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0540.rows BesselBatch0540.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0540.rows BesselBatch0540.accepted ⟨9,by decide⟩
]
theorem midAccepted : besselPointCheck (1910013507132660236694929447156554784833/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1910013507132660236694929447156554784833/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0081.rows ScalarLogs0081.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0081.rows ScalarLogs0081.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0081.rows ScalarLogs0081.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0081.rows ScalarLogs0081.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0081.rows ScalarLogs0081.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0081.rows ScalarLogs0081.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0081.rows ScalarLogs0081.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0081.rows ScalarLogs0081.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0081.rows ScalarLogs0081.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0081.rows ScalarLogs0081.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0081.rows ScalarLogs0081.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0081.rows ScalarLogs0081.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0081.rows ScalarLogs0081.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0081.rows ScalarLogs0081.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0081.rows ScalarLogs0081.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0081.rows ScalarLogs0081.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0040.bracket0655 BracketBatch0041.bracket0656 (1910013507132660236694929447156554784833/10000000000000000000000000000000000000000) (122037336469320664966823692187021669/1250000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0040.bracket0655 BracketBatch0041.bracket0656
  (1910013507132660236694929447156554784833/10000000000000000000000000000000000000000) (122037336469320664966823692187021669/1250000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0655
