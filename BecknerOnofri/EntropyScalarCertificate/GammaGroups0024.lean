module

public import BecknerOnofri.EntropyScalarCertificate.Bessel0030
public import BecknerOnofri.EntropyScalarCertificate.Bessel0031
public import BecknerOnofri.EntropyScalarCertificate.Bessel0503
public import BecknerOnofri.EntropyScalarCertificate.Bessel0504
public import BecknerOnofri.EntropyScalarCertificate.Brackets0012
public import BecknerOnofri.EntropyScalarCertificate.Logs0024
public import BecknerOnofri.ScalarElementaryComposition
public import BecknerOnofri.ScalarGammaEnclosure
public import BecknerOnofri.ScalarLogBesselEndpoints

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0192
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0030.rows BesselBatch0030.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0030.rows BesselBatch0030.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0030.rows BesselBatch0030.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0030.rows BesselBatch0030.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0030.rows BesselBatch0030.accepted ⟨4,by decide⟩
]
theorem leftAccepted : besselPointCheck (29790803130729883279784645254738758077/312500000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (29790803130729883279784645254738758077/312500000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0030.rows BesselBatch0030.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0030.rows BesselBatch0030.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0030.rows BesselBatch0030.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0030.rows BesselBatch0030.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0030.rows BesselBatch0030.accepted ⟨19,by decide⟩
]
theorem rightAccepted : besselPointCheck (238833279673337460273452586617775932331/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (238833279673337460273452586617775932331/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0503.rows BesselBatch0503.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0503.rows BesselBatch0503.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0503.rows BesselBatch0503.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0503.rows BesselBatch0503.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0503.rows BesselBatch0503.accepted ⟨62,by decide⟩
]
theorem midAccepted : besselPointCheck (477159704719176526511729748655685996947/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (477159704719176526511729748655685996947/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0024.rows ScalarLogs0024.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0024.rows ScalarLogs0024.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0024.rows ScalarLogs0024.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0024.rows ScalarLogs0024.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0024.rows ScalarLogs0024.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0024.rows ScalarLogs0024.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0024.rows ScalarLogs0024.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0024.rows ScalarLogs0024.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0024.rows ScalarLogs0024.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0024.rows ScalarLogs0024.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0024.rows ScalarLogs0024.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0024.rows ScalarLogs0024.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0024.rows ScalarLogs0024.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0024.rows ScalarLogs0024.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0024.rows ScalarLogs0024.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0024.rows ScalarLogs0024.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0012.bracket0192 BracketBatch0012.bracket0193 (477159704719176526511729748655685996947/5000000000000000000000000000000000000000) (3937858163210672158926269545480133/625000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0012.bracket0192 BracketBatch0012.bracket0193
  (477159704719176526511729748655685996947/5000000000000000000000000000000000000000) (3937858163210672158926269545480133/625000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0192
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0193
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0030.rows BesselBatch0030.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0030.rows BesselBatch0030.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0030.rows BesselBatch0030.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0030.rows BesselBatch0030.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0030.rows BesselBatch0030.accepted ⟨14,by decide⟩
]
theorem leftAccepted : besselPointCheck (955333118693349841093810346471103729321/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (955333118693349841093810346471103729321/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0030.rows BesselBatch0030.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0030.rows BesselBatch0030.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0030.rows BesselBatch0030.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0030.rows BesselBatch0030.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0030.rows BesselBatch0030.accepted ⟨29,by decide⟩
]
theorem rightAccepted : besselPointCheck (95736065424284557012371158257859946807/1000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (95736065424284557012371158257859946807/1000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0503.rows BesselBatch0503.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0504.rows BesselBatch0504.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0504.rows BesselBatch0504.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0504.rows BesselBatch0504.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0504.rows BesselBatch0504.accepted ⟨3,by decide⟩
]
theorem midAccepted : besselPointCheck (1912693772936195411217521929049703197391/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1912693772936195411217521929049703197391/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0024.rows ScalarLogs0024.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0024.rows ScalarLogs0024.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0024.rows ScalarLogs0024.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0024.rows ScalarLogs0024.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0024.rows ScalarLogs0024.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0024.rows ScalarLogs0024.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0024.rows ScalarLogs0024.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0024.rows ScalarLogs0024.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0024.rows ScalarLogs0024.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0024.rows ScalarLogs0024.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0024.rows ScalarLogs0024.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0024.rows ScalarLogs0024.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0024.rows ScalarLogs0024.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0024.rows ScalarLogs0024.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0024.rows ScalarLogs0024.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0024.rows ScalarLogs0024.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0012.bracket0193 BracketBatch0012.bracket0194 (1912693772936195411217521929049703197391/20000000000000000000000000000000000000000) (31771482704539541612519061318897409/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0012.bracket0193 BracketBatch0012.bracket0194
  (1912693772936195411217521929049703197391/20000000000000000000000000000000000000000) (31771482704539541612519061318897409/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0193
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0194
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0030.rows BesselBatch0030.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0030.rows BesselBatch0030.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0030.rows BesselBatch0030.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0030.rows BesselBatch0030.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0030.rows BesselBatch0030.accepted ⟨24,by decide⟩
]
theorem leftAccepted : besselPointCheck (957360654242845570123711582578599468067/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (957360654242845570123711582578599468067/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0030.rows BesselBatch0030.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0030.rows BesselBatch0030.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0030.rows BesselBatch0030.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0030.rows BesselBatch0030.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0030.rows BesselBatch0030.accepted ⟨39,by decide⟩
]
theorem rightAccepted : besselPointCheck (959388307090527923366620465321596396683/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (959388307090527923366620465321596396683/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0504.rows BesselBatch0504.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0504.rows BesselBatch0504.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0504.rows BesselBatch0504.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0504.rows BesselBatch0504.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0504.rows BesselBatch0504.accepted ⟨8,by decide⟩
]
theorem midAccepted : besselPointCheck (7666995845333493973961328191600783459/80000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (7666995845333493973961328191600783459/80000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0024.rows ScalarLogs0024.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0024.rows ScalarLogs0024.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0024.rows ScalarLogs0024.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0024.rows ScalarLogs0024.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0024.rows ScalarLogs0024.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0024.rows ScalarLogs0024.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0024.rows ScalarLogs0024.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0024.rows ScalarLogs0024.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0024.rows ScalarLogs0024.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0024.rows ScalarLogs0024.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0024.rows ScalarLogs0024.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0024.rows ScalarLogs0024.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0024.rows ScalarLogs0024.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0024.rows ScalarLogs0024.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0024.rows ScalarLogs0024.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0024.rows ScalarLogs0024.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0012.bracket0194 BracketBatch0012.bracket0195 (7666995845333493973961328191600783459/80000000000000000000000000000000000000) (12816722629191525760522770256972223/2000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0012.bracket0194 BracketBatch0012.bracket0195
  (7666995845333493973961328191600783459/80000000000000000000000000000000000000) (12816722629191525760522770256972223/2000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0194
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0195
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0030.rows BesselBatch0030.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0030.rows BesselBatch0030.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0030.rows BesselBatch0030.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0030.rows BesselBatch0030.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0030.rows BesselBatch0030.accepted ⟨34,by decide⟩
]
theorem leftAccepted : besselPointCheck (23984707677263198084165511633039909917/250000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (23984707677263198084165511633039909917/250000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0030.rows BesselBatch0030.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0030.rows BesselBatch0030.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0030.rows BesselBatch0030.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0030.rows BesselBatch0030.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0030.rows BesselBatch0030.accepted ⟨49,by decide⟩
]
theorem rightAccepted : besselPointCheck (480708038747581185805981293478171361389/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (480708038747581185805981293478171361389/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0504.rows BesselBatch0504.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0504.rows BesselBatch0504.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0504.rows BesselBatch0504.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0504.rows BesselBatch0504.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0504.rows BesselBatch0504.accepted ⟨13,by decide⟩
]
theorem midAccepted : besselPointCheck (960402192292845147489291526138969559729/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (960402192292845147489291526138969559729/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0024.rows ScalarLogs0024.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0024.rows ScalarLogs0024.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0024.rows ScalarLogs0024.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0024.rows ScalarLogs0024.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0024.rows ScalarLogs0024.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0024.rows ScalarLogs0024.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0024.rows ScalarLogs0024.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0024.rows ScalarLogs0024.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0024.rows ScalarLogs0024.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0024.rows ScalarLogs0024.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0024.rows ScalarLogs0024.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0024.rows ScalarLogs0024.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0024.rows ScalarLogs0024.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0024.rows ScalarLogs0024.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0024.rows ScalarLogs0024.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0024.rows ScalarLogs0024.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0012.bracket0195 BracketBatch0012.bracket0196 (960402192292845147489291526138969559729/10000000000000000000000000000000000000000) (6462768832499903599713228093841101/1000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0012.bracket0195 BracketBatch0012.bracket0196
  (960402192292845147489291526138969559729/10000000000000000000000000000000000000000) (6462768832499903599713228093841101/1000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0195
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0196
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0030.rows BesselBatch0030.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0030.rows BesselBatch0030.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0030.rows BesselBatch0030.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0030.rows BesselBatch0030.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0030.rows BesselBatch0030.accepted ⟨44,by decide⟩
]
theorem leftAccepted : besselPointCheck (38456643099806494864478503478253708911/400000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (38456643099806494864478503478253708911/400000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0030.rows BesselBatch0030.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0030.rows BesselBatch0030.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0030.rows BesselBatch0030.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0030.rows BesselBatch0030.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0030.rows BesselBatch0030.accepted ⟨59,by decide⟩
]
theorem rightAccepted : besselPointCheck (963443965715595575813953652163134624767/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (963443965715595575813953652163134624767/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0504.rows BesselBatch0504.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0504.rows BesselBatch0504.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0504.rows BesselBatch0504.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0504.rows BesselBatch0504.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0504.rows BesselBatch0504.accepted ⟨18,by decide⟩
]
theorem midAccepted : besselPointCheck (962430021605378973712958119559738673771/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (962430021605378973712958119559738673771/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0024.rows ScalarLogs0024.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0024.rows ScalarLogs0024.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0024.rows ScalarLogs0024.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0024.rows ScalarLogs0024.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0024.rows ScalarLogs0024.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0024.rows ScalarLogs0024.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0024.rows ScalarLogs0024.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0024.rows ScalarLogs0024.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0024.rows ScalarLogs0024.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0024.rows ScalarLogs0024.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0024.rows ScalarLogs0024.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0024.rows ScalarLogs0024.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0024.rows ScalarLogs0024.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0024.rows ScalarLogs0024.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0024.rows ScalarLogs0024.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0024.rows ScalarLogs0024.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0012.bracket0196 BracketBatch0012.bracket0197 (962430021605378973712958119559738673771/10000000000000000000000000000000000000000) (16293801370196515363802759563005089/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0012.bracket0196 BracketBatch0012.bracket0197
  (962430021605378973712958119559738673771/10000000000000000000000000000000000000000) (16293801370196515363802759563005089/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0196
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0197
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0030.rows BesselBatch0030.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0030.rows BesselBatch0030.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0030.rows BesselBatch0030.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0030.rows BesselBatch0030.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0030.rows BesselBatch0030.accepted ⟨54,by decide⟩
]
theorem leftAccepted : besselPointCheck (240860991428898893953488413040783656191/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (240860991428898893953488413040783656191/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0031.rows BesselBatch0031.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0031.rows BesselBatch0031.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0031.rows BesselBatch0031.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0031.rows BesselBatch0031.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0031.rows BesselBatch0031.accepted ⟨5,by decide⟩
]
theorem rightAccepted : besselPointCheck (965471972010755577926816017072544106189/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (965471972010755577926816017072544106189/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0504.rows BesselBatch0504.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0504.rows BesselBatch0504.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0504.rows BesselBatch0504.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0504.rows BesselBatch0504.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0504.rows BesselBatch0504.accepted ⟨23,by decide⟩
]
theorem midAccepted : besselPointCheck (1928915937726351153740769669235678730953/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1928915937726351153740769669235678730953/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0024.rows ScalarLogs0024.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0024.rows ScalarLogs0024.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0024.rows ScalarLogs0024.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0024.rows ScalarLogs0024.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0024.rows ScalarLogs0024.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0024.rows ScalarLogs0024.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0024.rows ScalarLogs0024.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0024.rows ScalarLogs0024.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0024.rows ScalarLogs0024.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0024.rows ScalarLogs0024.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0024.rows ScalarLogs0024.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0024.rows ScalarLogs0024.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0024.rows ScalarLogs0024.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0024.rows ScalarLogs0024.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0024.rows ScalarLogs0024.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0024.rows ScalarLogs0024.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0012.bracket0197 BracketBatch0012.bracket0198 (1928915937726351153740769669235678730953/20000000000000000000000000000000000000000) (6572617917949876914681032689876529/1000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0012.bracket0197 BracketBatch0012.bracket0198
  (1928915937726351153740769669235678730953/20000000000000000000000000000000000000000) (6572617917949876914681032689876529/1000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0197
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0198
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0030.rows BesselBatch0030.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0030.rows BesselBatch0030.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0030.rows BesselBatch0030.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0030.rows BesselBatch0030.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0031.rows BesselBatch0031.accepted ⟨0,by decide⟩
]
theorem leftAccepted : besselPointCheck (482735986005377788963408008536272053093/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (482735986005377788963408008536272053093/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0031.rows BesselBatch0031.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0031.rows BesselBatch0031.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0031.rows BesselBatch0031.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0031.rows BesselBatch0031.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0031.rows BesselBatch0031.accepted ⟨15,by decide⟩
]
theorem rightAccepted : besselPointCheck (483750048319825995938193234003547141741/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (483750048319825995938193234003547141741/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0504.rows BesselBatch0504.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0504.rows BesselBatch0504.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0504.rows BesselBatch0504.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0504.rows BesselBatch0504.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0504.rows BesselBatch0504.accepted ⟨28,by decide⟩
]
theorem midAccepted : besselPointCheck (483243017162601892450800621269909597417/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (483243017162601892450800621269909597417/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0024.rows ScalarLogs0024.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0024.rows ScalarLogs0024.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0024.rows ScalarLogs0024.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0024.rows ScalarLogs0024.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0024.rows ScalarLogs0024.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0024.rows ScalarLogs0024.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0024.rows ScalarLogs0024.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0024.rows ScalarLogs0024.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0024.rows ScalarLogs0024.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0024.rows ScalarLogs0024.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0024.rows ScalarLogs0024.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0024.rows ScalarLogs0024.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0024.rows ScalarLogs0024.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0024.rows ScalarLogs0024.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0024.rows ScalarLogs0024.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0024.rows ScalarLogs0024.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0012.bracket0198 BracketBatch0012.bracket0199 (483243017162601892450800621269909597417/5000000000000000000000000000000000000000) (2071269500591304448330811870013989/312500000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0012.bracket0198 BracketBatch0012.bracket0199
  (483243017162601892450800621269909597417/5000000000000000000000000000000000000000) (2071269500591304448330811870013989/312500000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0198
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0199
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0031.rows BesselBatch0031.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0031.rows BesselBatch0031.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0031.rows BesselBatch0031.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0031.rows BesselBatch0031.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0031.rows BesselBatch0031.accepted ⟨10,by decide⟩
]
theorem leftAccepted : besselPointCheck (967500096639651991876386468007094283479/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (967500096639651991876386468007094283479/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0031.rows BesselBatch0031.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0031.rows BesselBatch0031.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0031.rows BesselBatch0031.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0031.rows BesselBatch0031.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0031.rows BesselBatch0031.accepted ⟨25,by decide⟩
]
theorem rightAccepted : besselPointCheck (969528339861376194668462988702784250159/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (969528339861376194668462988702784250159/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0504.rows BesselBatch0504.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0504.rows BesselBatch0504.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0504.rows BesselBatch0504.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0504.rows BesselBatch0504.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0504.rows BesselBatch0504.accepted ⟨33,by decide⟩
]
theorem midAccepted : besselPointCheck (968514218250514093272424728354939266819/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (968514218250514093272424728354939266819/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0024.rows ScalarLogs0024.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0024.rows ScalarLogs0024.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0024.rows ScalarLogs0024.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0024.rows ScalarLogs0024.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0024.rows ScalarLogs0024.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0024.rows ScalarLogs0024.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0024.rows ScalarLogs0024.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0024.rows ScalarLogs0024.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0024.rows ScalarLogs0024.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0024.rows ScalarLogs0024.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0024.rows ScalarLogs0024.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0024.rows ScalarLogs0024.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0024.rows ScalarLogs0024.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0024.rows ScalarLogs0024.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0024.rows ScalarLogs0024.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0024.rows ScalarLogs0024.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0012.bracket0199 BracketBatch0012.bracket0200 (968514218250514093272424728354939266819/10000000000000000000000000000000000000000) (668385546284513122081158964874029/100000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0012.bracket0199 BracketBatch0012.bracket0200
  (968514218250514093272424728354939266819/10000000000000000000000000000000000000000) (668385546284513122081158964874029/100000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0199
