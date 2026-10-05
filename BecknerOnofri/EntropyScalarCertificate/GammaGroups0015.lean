module

public import BecknerOnofri.EntropyScalarCertificate.Bessel0018
public import BecknerOnofri.EntropyScalarCertificate.Bessel0019
public import BecknerOnofri.EntropyScalarCertificate.Bessel0020
public import BecknerOnofri.EntropyScalarCertificate.Bessel0498
public import BecknerOnofri.EntropyScalarCertificate.Brackets0007
public import BecknerOnofri.EntropyScalarCertificate.Brackets0008
public import BecknerOnofri.EntropyScalarCertificate.Logs0015
public import BecknerOnofri.ScalarElementaryComposition
public import BecknerOnofri.ScalarGammaEnclosure
public import BecknerOnofri.ScalarLogBesselEndpoints

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0120
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0018.rows BesselBatch0018.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0018.rows BesselBatch0018.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0018.rows BesselBatch0018.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0018.rows BesselBatch0018.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0018.rows BesselBatch0018.accepted ⟨52,by decide⟩
]
theorem leftAccepted : besselPointCheck (807622473272319481635162539220557939531/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (807622473272319481635162539220557939531/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0018.rows BesselBatch0018.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0019.rows BesselBatch0019.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0019.rows BesselBatch0019.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0019.rows BesselBatch0019.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0019.rows BesselBatch0019.accepted ⟨3,by decide⟩
]
theorem rightAccepted : besselPointCheck (202410534934898130544901999340407468557/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (202410534934898130544901999340407468557/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0498.rows BesselBatch0498.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0498.rows BesselBatch0498.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0498.rows BesselBatch0498.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0498.rows BesselBatch0498.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0498.rows BesselBatch0498.accepted ⟨22,by decide⟩
]
theorem midAccepted : besselPointCheck (1617264613011912003814770536582187813759/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1617264613011912003814770536582187813759/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0015.rows ScalarLogs0015.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0015.rows ScalarLogs0015.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0015.rows ScalarLogs0015.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0015.rows ScalarLogs0015.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0015.rows ScalarLogs0015.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0015.rows ScalarLogs0015.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0015.rows ScalarLogs0015.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0015.rows ScalarLogs0015.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0015.rows ScalarLogs0015.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0015.rows ScalarLogs0015.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0015.rows ScalarLogs0015.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0015.rows ScalarLogs0015.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0015.rows ScalarLogs0015.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0015.rows ScalarLogs0015.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0015.rows ScalarLogs0015.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0015.rows ScalarLogs0015.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0007.bracket0120 BracketBatch0007.bracket0121 (1617264613011912003814770536582187813759/20000000000000000000000000000000000000000) (506127409098883374680044674410167/156250000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0007.bracket0120 BracketBatch0007.bracket0121
  (1617264613011912003814770536582187813759/20000000000000000000000000000000000000000) (506127409098883374680044674410167/156250000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0120
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0121
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0018.rows BesselBatch0018.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0018.rows BesselBatch0018.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0018.rows BesselBatch0018.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0018.rows BesselBatch0018.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0018.rows BesselBatch0018.accepted ⟨62,by decide⟩
]
theorem leftAccepted : besselPointCheck (32385685589583700887184319894465194969/400000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (32385685589583700887184319894465194969/400000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0019.rows BesselBatch0019.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0019.rows BesselBatch0019.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0019.rows BesselBatch0019.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0019.rows BesselBatch0019.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0019.rows BesselBatch0019.accepted ⟨13,by decide⟩
]
theorem rightAccepted : besselPointCheck (405830952410874763396850673477599284067/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (405830952410874763396850673477599284067/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0498.rows BesselBatch0498.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0498.rows BesselBatch0498.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0498.rows BesselBatch0498.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0498.rows BesselBatch0498.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0498.rows BesselBatch0498.accepted ⟨27,by decide⟩
]
theorem midAccepted : besselPointCheck (1621304044561342048973309344316828442359/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1621304044561342048973309344316828442359/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0015.rows ScalarLogs0015.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0015.rows ScalarLogs0015.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0015.rows ScalarLogs0015.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0015.rows ScalarLogs0015.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0015.rows ScalarLogs0015.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0015.rows ScalarLogs0015.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0015.rows ScalarLogs0015.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0015.rows ScalarLogs0015.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0015.rows ScalarLogs0015.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0015.rows ScalarLogs0015.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0015.rows ScalarLogs0015.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0015.rows ScalarLogs0015.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0015.rows ScalarLogs0015.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0015.rows ScalarLogs0015.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0015.rows ScalarLogs0015.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0015.rows ScalarLogs0015.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0007.bracket0121 BracketBatch0007.bracket0122 (1621304044561342048973309344316828442359/20000000000000000000000000000000000000000) (32719731882910021502434043160528701/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0007.bracket0121 BracketBatch0007.bracket0122
  (1621304044561342048973309344316828442359/20000000000000000000000000000000000000000) (32719731882910021502434043160528701/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0121
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0122
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0019.rows BesselBatch0019.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0019.rows BesselBatch0019.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0019.rows BesselBatch0019.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0019.rows BesselBatch0019.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0019.rows BesselBatch0019.accepted ⟨8,by decide⟩
]
theorem leftAccepted : besselPointCheck (811661904821749526793701346955198568131/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (811661904821749526793701346955198568131/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0019.rows BesselBatch0019.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0019.rows BesselBatch0019.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0019.rows BesselBatch0019.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0019.rows BesselBatch0019.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0019.rows BesselBatch0019.accepted ⟨23,by decide⟩
]
theorem rightAccepted : besselPointCheck (101710221096516969810600133055341433027/1250000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (101710221096516969810600133055341433027/1250000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0498.rows BesselBatch0498.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0498.rows BesselBatch0498.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0498.rows BesselBatch0498.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0498.rows BesselBatch0498.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0498.rows BesselBatch0498.accepted ⟨32,by decide⟩
]
theorem midAccepted : besselPointCheck (1625343673593885285278502411397930032347/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1625343673593885285278502411397930032347/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0015.rows ScalarLogs0015.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0015.rows ScalarLogs0015.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0015.rows ScalarLogs0015.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0015.rows ScalarLogs0015.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0015.rows ScalarLogs0015.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0015.rows ScalarLogs0015.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0015.rows ScalarLogs0015.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0015.rows ScalarLogs0015.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0015.rows ScalarLogs0015.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0015.rows ScalarLogs0015.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0015.rows ScalarLogs0015.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0015.rows ScalarLogs0015.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0015.rows ScalarLogs0015.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0015.rows ScalarLogs0015.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0015.rows ScalarLogs0015.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0015.rows ScalarLogs0015.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0007.bracket0122 BracketBatch0007.bracket0123 (1625343673593885285278502411397930032347/20000000000000000000000000000000000000000) (6609952175941334295350327311094967/2000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0007.bracket0122 BracketBatch0007.bracket0123
  (1625343673593885285278502411397930032347/20000000000000000000000000000000000000000) (6609952175941334295350327311094967/2000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0122
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0123
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0019.rows BesselBatch0019.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0019.rows BesselBatch0019.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0019.rows BesselBatch0019.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0019.rows BesselBatch0019.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0019.rows BesselBatch0019.accepted ⟨18,by decide⟩
]
theorem leftAccepted : besselPointCheck (813681768772135758484801064442731464213/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (813681768772135758484801064442731464213/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0019.rows BesselBatch0019.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0019.rows BesselBatch0019.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0019.rows BesselBatch0019.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0019.rows BesselBatch0019.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0019.rows BesselBatch0019.accepted ⟨33,by decide⟩
]
theorem rightAccepted : besselPointCheck (815701731844164084881687300808533152691/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (815701731844164084881687300808533152691/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0498.rows BesselBatch0498.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0498.rows BesselBatch0498.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0498.rows BesselBatch0498.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0498.rows BesselBatch0498.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0498.rows BesselBatch0498.accepted ⟨37,by decide⟩
]
theorem midAccepted : besselPointCheck (203672937577037480420811045656408077113/2500000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (203672937577037480420811045656408077113/2500000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0015.rows ScalarLogs0015.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0015.rows ScalarLogs0015.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0015.rows ScalarLogs0015.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0015.rows ScalarLogs0015.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0015.rows ScalarLogs0015.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0015.rows ScalarLogs0015.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0015.rows ScalarLogs0015.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0015.rows ScalarLogs0015.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0015.rows ScalarLogs0015.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0015.rows ScalarLogs0015.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0015.rows ScalarLogs0015.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0015.rows ScalarLogs0015.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0015.rows ScalarLogs0015.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0015.rows ScalarLogs0015.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0015.rows ScalarLogs0015.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0015.rows ScalarLogs0015.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0007.bracket0123 BracketBatch0007.bracket0124 (203672937577037480420811045656408077113/2500000000000000000000000000000000000000) (33382253419069941607270564366453563/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0007.bracket0123 BracketBatch0007.bracket0124
  (203672937577037480420811045656408077113/2500000000000000000000000000000000000000) (33382253419069941607270564366453563/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0123
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0124
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0019.rows BesselBatch0019.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0019.rows BesselBatch0019.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0019.rows BesselBatch0019.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0019.rows BesselBatch0019.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0019.rows BesselBatch0019.accepted ⟨28,by decide⟩
]
theorem leftAccepted : besselPointCheck (50981358240260255305105456300533322043/625000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (50981358240260255305105456300533322043/625000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0019.rows BesselBatch0019.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0019.rows BesselBatch0019.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0019.rows BesselBatch0019.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0019.rows BesselBatch0019.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0019.rows BesselBatch0019.accepted ⟨43,by decide⟩
]
theorem rightAccepted : besselPointCheck (817721794291315160025580043888214318617/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (817721794291315160025580043888214318617/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0498.rows BesselBatch0498.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0498.rows BesselBatch0498.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0498.rows BesselBatch0498.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0498.rows BesselBatch0498.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0498.rows BesselBatch0498.accepted ⟨42,by decide⟩
]
theorem midAccepted : besselPointCheck (326684705227095848981453468939349494261/4000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (326684705227095848981453468939349494261/4000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0015.rows ScalarLogs0015.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0015.rows ScalarLogs0015.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0015.rows ScalarLogs0015.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0015.rows ScalarLogs0015.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0015.rows ScalarLogs0015.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0015.rows ScalarLogs0015.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0015.rows ScalarLogs0015.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0015.rows ScalarLogs0015.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0015.rows ScalarLogs0015.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0015.rows ScalarLogs0015.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0015.rows ScalarLogs0015.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0015.rows ScalarLogs0015.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0015.rows ScalarLogs0015.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0015.rows ScalarLogs0015.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0015.rows ScalarLogs0015.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0015.rows ScalarLogs0015.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0007.bracket0124 BracketBatch0007.bracket0125 (326684705227095848981453468939349494261/4000000000000000000000000000000000000000) (6743444355693261329721887290126263/2000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0007.bracket0124 BracketBatch0007.bracket0125
  (326684705227095848981453468939349494261/4000000000000000000000000000000000000000) (6743444355693261329721887290126263/2000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0124
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0125
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0019.rows BesselBatch0019.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0019.rows BesselBatch0019.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0019.rows BesselBatch0019.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0019.rows BesselBatch0019.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0019.rows BesselBatch0019.accepted ⟨38,by decide⟩
]
theorem leftAccepted : besselPointCheck (408860897145657580012790021944107159307/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (408860897145657580012790021944107159307/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0019.rows BesselBatch0019.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0019.rows BesselBatch0019.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0019.rows BesselBatch0019.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0019.rows BesselBatch0019.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0019.rows BesselBatch0019.accepted ⟨53,by decide⟩
]
theorem rightAccepted : besselPointCheck (409870978183568803136610529302321092791/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (409870978183568803136610529302321092791/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0498.rows BesselBatch0498.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0498.rows BesselBatch0498.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0498.rows BesselBatch0498.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0498.rows BesselBatch0498.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0498.rows BesselBatch0498.accepted ⟨47,by decide⟩
]
theorem midAccepted : besselPointCheck (409365937664613191574700275623214126049/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (409365937664613191574700275623214126049/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0015.rows ScalarLogs0015.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0015.rows ScalarLogs0015.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0015.rows ScalarLogs0015.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0015.rows ScalarLogs0015.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0015.rows ScalarLogs0015.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0015.rows ScalarLogs0015.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0015.rows ScalarLogs0015.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0015.rows ScalarLogs0015.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0015.rows ScalarLogs0015.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0015.rows ScalarLogs0015.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0015.rows ScalarLogs0015.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0015.rows ScalarLogs0015.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0015.rows ScalarLogs0015.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0015.rows ScalarLogs0015.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0015.rows ScalarLogs0015.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0015.rows ScalarLogs0015.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0007.bracket0125 BracketBatch0007.bracket0126 (409365937664613191574700275623214126049/5000000000000000000000000000000000000000) (34054678266483286072897823988655859/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0007.bracket0125 BracketBatch0007.bracket0126
  (409365937664613191574700275623214126049/5000000000000000000000000000000000000000) (34054678266483286072897823988655859/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0125
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0126
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0019.rows BesselBatch0019.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0019.rows BesselBatch0019.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0019.rows BesselBatch0019.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0019.rows BesselBatch0019.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0019.rows BesselBatch0019.accepted ⟨48,by decide⟩
]
theorem leftAccepted : besselPointCheck (819741956367137606273221058604642185579/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (819741956367137606273221058604642185579/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0019.rows BesselBatch0019.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0019.rows BesselBatch0019.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0019.rows BesselBatch0019.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0019.rows BesselBatch0019.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0019.rows BesselBatch0019.accepted ⟨63,by decide⟩
]
theorem rightAccepted : besselPointCheck (821762218325248196312339720620703128649/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (821762218325248196312339720620703128649/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0498.rows BesselBatch0498.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0498.rows BesselBatch0498.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0498.rows BesselBatch0498.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0498.rows BesselBatch0498.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0498.rows BesselBatch0498.accepted ⟨52,by decide⟩
]
theorem midAccepted : besselPointCheck (410376043673096450646390194806336328557/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (410376043673096450646390194806336328557/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0015.rows ScalarLogs0015.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0015.rows ScalarLogs0015.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0015.rows ScalarLogs0015.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0015.rows ScalarLogs0015.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0015.rows ScalarLogs0015.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0015.rows ScalarLogs0015.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0015.rows ScalarLogs0015.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0015.rows ScalarLogs0015.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0015.rows ScalarLogs0015.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0015.rows ScalarLogs0015.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0015.rows ScalarLogs0015.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0015.rows ScalarLogs0015.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0015.rows ScalarLogs0015.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0015.rows ScalarLogs0015.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0015.rows ScalarLogs0015.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0015.rows ScalarLogs0015.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0007.bracket0126 BracketBatch0007.bracket0127 (410376043673096450646390194806336328557/5000000000000000000000000000000000000000) (34394635222835485676816504705757669/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0007.bracket0126 BracketBatch0007.bracket0127
  (410376043673096450646390194806336328557/5000000000000000000000000000000000000000) (34394635222835485676816504705757669/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0126
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0127
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0019.rows BesselBatch0019.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0019.rows BesselBatch0019.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0019.rows BesselBatch0019.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0019.rows BesselBatch0019.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0019.rows BesselBatch0019.accepted ⟨58,by decide⟩
]
theorem leftAccepted : besselPointCheck (410881109162624098156169860310351564323/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (410881109162624098156169860310351564323/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0020.rows BesselBatch0020.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0020.rows BesselBatch0020.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0020.rows BesselBatch0020.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0020.rows BesselBatch0020.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0020.rows BesselBatch0020.accepted ⟨9,by decide⟩
]
theorem rightAccepted : besselPointCheck (25743205638104126102806974952217819791/312500000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (25743205638104126102806974952217819791/312500000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0498.rows BesselBatch0498.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0498.rows BesselBatch0498.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0498.rows BesselBatch0498.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0498.rows BesselBatch0498.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0498.rows BesselBatch0498.accepted ⟨57,by decide⟩
]
theorem midAccepted : besselPointCheck (822772399372290115801081459545836680979/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (822772399372290115801081459545836680979/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0015.rows ScalarLogs0015.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0015.rows ScalarLogs0015.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0015.rows ScalarLogs0015.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0015.rows ScalarLogs0015.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0015.rows ScalarLogs0015.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0015.rows ScalarLogs0015.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0015.rows ScalarLogs0015.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0015.rows ScalarLogs0015.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0015.rows ScalarLogs0015.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0015.rows ScalarLogs0015.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0015.rows ScalarLogs0015.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0015.rows ScalarLogs0015.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0015.rows ScalarLogs0015.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0015.rows ScalarLogs0015.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0015.rows ScalarLogs0015.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0015.rows ScalarLogs0015.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0007.bracket0127 BracketBatch0008.bracket0128 (822772399372290115801081459545836680979/10000000000000000000000000000000000000000) (17368552509185327568044532897277681/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0007.bracket0127 BracketBatch0008.bracket0128
  (822772399372290115801081459545836680979/10000000000000000000000000000000000000000) (17368552509185327568044532897277681/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0127
