module

public import BecknerOnofri.EntropyScalarCertificate.Bessel0123
public import BecknerOnofri.EntropyScalarCertificate.Bessel0124
public import BecknerOnofri.EntropyScalarCertificate.Bessel0125
public import BecknerOnofri.EntropyScalarCertificate.Bessel0550
public import BecknerOnofri.EntropyScalarCertificate.Bessel0551
public import BecknerOnofri.EntropyScalarCertificate.Brackets0049
public import BecknerOnofri.EntropyScalarCertificate.Brackets0050
public import BecknerOnofri.EntropyScalarCertificate.Logs0099
public import BecknerOnofri.ScalarElementaryComposition
public import BecknerOnofri.ScalarGammaEnclosure
public import BecknerOnofri.ScalarLogBesselEndpoints

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0792
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0123.rows BesselBatch0123.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0123.rows BesselBatch0123.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0123.rows BesselBatch0123.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0123.rows BesselBatch0123.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0123.rows BesselBatch0123.accepted ⟨52,by decide⟩
]
theorem leftAccepted : besselPointCheck (712446362193587942158815282669602841871/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (712446362193587942158815282669602841871/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0123.rows BesselBatch0123.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0124.rows BesselBatch0124.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0124.rows BesselBatch0124.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0124.rows BesselBatch0124.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0124.rows BesselBatch0124.accepted ⟨3,by decide⟩
]
theorem rightAccepted : besselPointCheck (715261779105501423927752110144374008089/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (715261779105501423927752110144374008089/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0550.rows BesselBatch0550.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0550.rows BesselBatch0550.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0550.rows BesselBatch0550.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0550.rows BesselBatch0550.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0550.rows BesselBatch0550.accepted ⟨54,by decide⟩
]
theorem midAccepted : besselPointCheck (35692703532477234152164184820349421249/125000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (35692703532477234152164184820349421249/125000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0099.rows ScalarLogs0099.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0099.rows ScalarLogs0099.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0099.rows ScalarLogs0099.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0099.rows ScalarLogs0099.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0099.rows ScalarLogs0099.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0099.rows ScalarLogs0099.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0099.rows ScalarLogs0099.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0099.rows ScalarLogs0099.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0099.rows ScalarLogs0099.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0099.rows ScalarLogs0099.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0099.rows ScalarLogs0099.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0099.rows ScalarLogs0099.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0099.rows ScalarLogs0099.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0099.rows ScalarLogs0099.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0099.rows ScalarLogs0099.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0099.rows ScalarLogs0099.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0049.bracket0792 BracketBatch0049.bracket0793 (35692703532477234152164184820349421249/125000000000000000000000000000000000000) (4514659577462601665135411179824420407/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0049.bracket0792 BracketBatch0049.bracket0793
  (35692703532477234152164184820349421249/125000000000000000000000000000000000000) (4514659577462601665135411179824420407/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0792
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0793
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0123.rows BesselBatch0123.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0123.rows BesselBatch0123.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0123.rows BesselBatch0123.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0123.rows BesselBatch0123.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0123.rows BesselBatch0123.accepted ⟨62,by decide⟩
]
theorem leftAccepted : besselPointCheck (2861047116422005695711008440577496032353/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (2861047116422005695711008440577496032353/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0124.rows BesselBatch0124.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0124.rows BesselBatch0124.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0124.rows BesselBatch0124.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0124.rows BesselBatch0124.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0124.rows BesselBatch0124.accepted ⟨13,by decide⟩
]
theorem rightAccepted : besselPointCheck (1436159533605345505977290929159624737353/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1436159533605345505977290929159624737353/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0550.rows BesselBatch0550.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0550.rows BesselBatch0550.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0550.rows BesselBatch0550.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0550.rows BesselBatch0550.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0550.rows BesselBatch0550.accepted ⟨59,by decide⟩
]
theorem midAccepted : besselPointCheck (5733366183632696707665590298896745507059/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (5733366183632696707665590298896745507059/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0099.rows ScalarLogs0099.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0099.rows ScalarLogs0099.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0099.rows ScalarLogs0099.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0099.rows ScalarLogs0099.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0099.rows ScalarLogs0099.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0099.rows ScalarLogs0099.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0099.rows ScalarLogs0099.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0099.rows ScalarLogs0099.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0099.rows ScalarLogs0099.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0099.rows ScalarLogs0099.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0099.rows ScalarLogs0099.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0099.rows ScalarLogs0099.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0099.rows ScalarLogs0099.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0099.rows ScalarLogs0099.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0099.rows ScalarLogs0099.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0099.rows ScalarLogs0099.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0049.bracket0793 BracketBatch0049.bracket0794 (5733366183632696707665590298896745507059/20000000000000000000000000000000000000000) (286385303078683337199892978423101489/625000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0049.bracket0793 BracketBatch0049.bracket0794
  (5733366183632696707665590298896745507059/20000000000000000000000000000000000000000) (286385303078683337199892978423101489/625000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0793
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0794
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0124.rows BesselBatch0124.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0124.rows BesselBatch0124.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0124.rows BesselBatch0124.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0124.rows BesselBatch0124.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0124.rows BesselBatch0124.accepted ⟨8,by decide⟩
]
theorem leftAccepted : besselPointCheck (2872319067210691011954581858319249474703/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (2872319067210691011954581858319249474703/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0124.rows BesselBatch0124.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0124.rows BesselBatch0124.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0124.rows BesselBatch0124.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0124.rows BesselBatch0124.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0124.rows BesselBatch0124.accepted ⟨23,by decide⟩
]
theorem rightAccepted : besselPointCheck (2883601355935473650373240345768673082299/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (2883601355935473650373240345768673082299/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0550.rows BesselBatch0550.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0550.rows BesselBatch0550.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0550.rows BesselBatch0550.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0550.rows BesselBatch0550.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0551.rows BesselBatch0551.accepted ⟨0,by decide⟩
]
theorem midAccepted : besselPointCheck (2877960211573082331163911102043961278501/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (2877960211573082331163911102043961278501/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0099.rows ScalarLogs0099.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0099.rows ScalarLogs0099.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0099.rows ScalarLogs0099.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0099.rows ScalarLogs0099.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0099.rows ScalarLogs0099.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0099.rows ScalarLogs0099.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0099.rows ScalarLogs0099.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0099.rows ScalarLogs0099.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0099.rows ScalarLogs0099.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0099.rows ScalarLogs0099.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0099.rows ScalarLogs0099.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0099.rows ScalarLogs0099.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0099.rows ScalarLogs0099.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0099.rows ScalarLogs0099.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0099.rows ScalarLogs0099.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0099.rows ScalarLogs0099.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0049.bracket0794 BracketBatch0049.bracket0795 (2877960211573082331163911102043961278501/10000000000000000000000000000000000000000) (1162608830633274805539177215550068529/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0049.bracket0794 BracketBatch0049.bracket0795
  (2877960211573082331163911102043961278501/10000000000000000000000000000000000000000) (1162608830633274805539177215550068529/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0794
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0795
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0124.rows BesselBatch0124.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0124.rows BesselBatch0124.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0124.rows BesselBatch0124.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0124.rows BesselBatch0124.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0124.rows BesselBatch0124.accepted ⟨18,by decide⟩
]
theorem leftAccepted : besselPointCheck (360450169491934206296655043221084135287/1250000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (360450169491934206296655043221084135287/1250000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0124.rows BesselBatch0124.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0124.rows BesselBatch0124.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0124.rows BesselBatch0124.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0124.rows BesselBatch0124.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0124.rows BesselBatch0124.accepted ⟨33,by decide⟩
]
theorem rightAccepted : besselPointCheck (180930877351457942509175839074228285141/625000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (180930877351457942509175839074228285141/625000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0551.rows BesselBatch0551.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0551.rows BesselBatch0551.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0551.rows BesselBatch0551.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0551.rows BesselBatch0551.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0551.rows BesselBatch0551.accepted ⟨5,by decide⟩
]
theorem midAccepted : besselPointCheck (722311924194850091315006721369540705569/2500000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (722311924194850091315006721369540705569/2500000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0099.rows ScalarLogs0099.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0099.rows ScalarLogs0099.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0099.rows ScalarLogs0099.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0099.rows ScalarLogs0099.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0099.rows ScalarLogs0099.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0099.rows ScalarLogs0099.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0099.rows ScalarLogs0099.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0099.rows ScalarLogs0099.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0099.rows ScalarLogs0099.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0099.rows ScalarLogs0099.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0099.rows ScalarLogs0099.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0099.rows ScalarLogs0099.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0099.rows ScalarLogs0099.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0099.rows ScalarLogs0099.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0099.rows ScalarLogs0099.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0099.rows ScalarLogs0099.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0049.bracket0795 BracketBatch0049.bracket0796 (722311924194850091315006721369540705569/2500000000000000000000000000000000000000) (589934631562305812376455327517921639/1250000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0049.bracket0795 BracketBatch0049.bracket0796
  (722311924194850091315006721369540705569/2500000000000000000000000000000000000000) (589934631562305812376455327517921639/1250000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0795
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0796
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0124.rows BesselBatch0124.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0124.rows BesselBatch0124.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0124.rows BesselBatch0124.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0124.rows BesselBatch0124.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0124.rows BesselBatch0124.accepted ⟨28,by decide⟩
]
theorem leftAccepted : besselPointCheck (2894894037623327080146813425187652562253/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (2894894037623327080146813425187652562253/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0124.rows BesselBatch0124.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0124.rows BesselBatch0124.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0124.rows BesselBatch0124.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0124.rows BesselBatch0124.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0124.rows BesselBatch0124.accepted ⟨43,by decide⟩
]
theorem rightAccepted : besselPointCheck (363274645941859386240844055541698245787/1250000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (363274645941859386240844055541698245787/1250000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0551.rows BesselBatch0551.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0551.rows BesselBatch0551.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0551.rows BesselBatch0551.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0551.rows BesselBatch0551.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0551.rows BesselBatch0551.accepted ⟨10,by decide⟩
]
theorem midAccepted : besselPointCheck (5801091205158202170073565869521238528549/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (5801091205158202170073565869521238528549/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0099.rows ScalarLogs0099.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0099.rows ScalarLogs0099.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0099.rows ScalarLogs0099.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0099.rows ScalarLogs0099.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0099.rows ScalarLogs0099.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0099.rows ScalarLogs0099.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0099.rows ScalarLogs0099.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0099.rows ScalarLogs0099.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0099.rows ScalarLogs0099.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0099.rows ScalarLogs0099.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0099.rows ScalarLogs0099.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0099.rows ScalarLogs0099.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0099.rows ScalarLogs0099.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0099.rows ScalarLogs0099.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0099.rows ScalarLogs0099.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0099.rows ScalarLogs0099.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0049.bracket0796 BracketBatch0049.bracket0797 (5801091205158202170073565869521238528549/20000000000000000000000000000000000000000) (2394648062053834246985638471792897011/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0049.bracket0796 BracketBatch0049.bracket0797
  (5801091205158202170073565869521238528549/20000000000000000000000000000000000000000) (2394648062053834246985638471792897011/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0796
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0797
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0124.rows BesselBatch0124.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0124.rows BesselBatch0124.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0124.rows BesselBatch0124.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0124.rows BesselBatch0124.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0124.rows BesselBatch0124.accepted ⟨38,by decide⟩
]
theorem leftAccepted : besselPointCheck (2906197167534875089926752444333585966293/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (2906197167534875089926752444333585966293/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0124.rows BesselBatch0124.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0124.rows BesselBatch0124.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0124.rows BesselBatch0124.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0124.rows BesselBatch0124.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0124.rows BesselBatch0124.accepted ⟨53,by decide⟩
]
theorem rightAccepted : besselPointCheck (583502160233229656064318763415115059273/2000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (583502160233229656064318763415115059273/2000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0551.rows BesselBatch0551.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0551.rows BesselBatch0551.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0551.rows BesselBatch0551.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0551.rows BesselBatch0551.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0551.rows BesselBatch0551.accepted ⟨15,by decide⟩
]
theorem midAccepted : besselPointCheck (2911853984350511685124173130704580631329/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (2911853984350511685124173130704580631329/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0099.rows ScalarLogs0099.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0099.rows ScalarLogs0099.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0099.rows ScalarLogs0099.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0099.rows ScalarLogs0099.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0099.rows ScalarLogs0099.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0099.rows ScalarLogs0099.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0099.rows ScalarLogs0099.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0099.rows ScalarLogs0099.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0099.rows ScalarLogs0099.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0099.rows ScalarLogs0099.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0099.rows ScalarLogs0099.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0099.rows ScalarLogs0099.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0099.rows ScalarLogs0099.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0099.rows ScalarLogs0099.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0099.rows ScalarLogs0099.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0099.rows ScalarLogs0099.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0049.bracket0797 BracketBatch0049.bracket0798 (2911853984350511685124173130704580631329/10000000000000000000000000000000000000000) (971979730431141091517893027070892299/2000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0049.bracket0797 BracketBatch0049.bracket0798
  (2911853984350511685124173130704580631329/10000000000000000000000000000000000000000) (971979730431141091517893027070892299/2000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0797
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0798
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0124.rows BesselBatch0124.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0124.rows BesselBatch0124.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0124.rows BesselBatch0124.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0124.rows BesselBatch0124.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0124.rows BesselBatch0124.accepted ⟨48,by decide⟩
]
theorem leftAccepted : besselPointCheck (1458755400583074140160796908537787648181/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1458755400583074140160796908537787648181/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0124.rows BesselBatch0124.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0124.rows BesselBatch0124.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0124.rows BesselBatch0124.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0124.rows BesselBatch0124.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0124.rows BesselBatch0124.accepted ⟨63,by decide⟩
]
theorem rightAccepted : besselPointCheck (732208748562588601259019181925979528659/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (732208748562588601259019181925979528659/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0551.rows BesselBatch0551.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0551.rows BesselBatch0551.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0551.rows BesselBatch0551.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0551.rows BesselBatch0551.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0551.rows BesselBatch0551.accepted ⟨20,by decide⟩
]
theorem midAccepted : besselPointCheck (2923172897708251342678835272389746705499/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (2923172897708251342678835272389746705499/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0099.rows ScalarLogs0099.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0099.rows ScalarLogs0099.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0099.rows ScalarLogs0099.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0099.rows ScalarLogs0099.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0099.rows ScalarLogs0099.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0099.rows ScalarLogs0099.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0099.rows ScalarLogs0099.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0099.rows ScalarLogs0099.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0099.rows ScalarLogs0099.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0099.rows ScalarLogs0099.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0099.rows ScalarLogs0099.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0099.rows ScalarLogs0099.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0099.rows ScalarLogs0099.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0099.rows ScalarLogs0099.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0099.rows ScalarLogs0099.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0099.rows ScalarLogs0099.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0049.bracket0798 BracketBatch0049.bracket0799 (2923172897708251342678835272389746705499/10000000000000000000000000000000000000000) (2465645390691707313809753891476814661/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0049.bracket0798 BracketBatch0049.bracket0799
  (2923172897708251342678835272389746705499/10000000000000000000000000000000000000000) (2465645390691707313809753891476814661/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0798
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0799
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0124.rows BesselBatch0124.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0124.rows BesselBatch0124.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0124.rows BesselBatch0124.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0124.rows BesselBatch0124.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0124.rows BesselBatch0124.accepted ⟨58,by decide⟩
]
theorem leftAccepted : besselPointCheck (2928834994250354405036076727703918114633/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (2928834994250354405036076727703918114633/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0125.rows BesselBatch0125.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0125.rows BesselBatch0125.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0125.rows BesselBatch0125.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0125.rows BesselBatch0125.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0125.rows BesselBatch0125.accepted ⟨9,by decide⟩
]
theorem rightAccepted : besselPointCheck (2940169802759662701697027755097534972413/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (2940169802759662701697027755097534972413/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0551.rows BesselBatch0551.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0551.rows BesselBatch0551.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0551.rows BesselBatch0551.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0551.rows BesselBatch0551.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0551.rows BesselBatch0551.accepted ⟨25,by decide⟩
]
theorem midAccepted : besselPointCheck (2934502398505008553366552241400726543523/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (2934502398505008553366552241400726543523/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0099.rows ScalarLogs0099.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0099.rows ScalarLogs0099.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0099.rows ScalarLogs0099.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0099.rows ScalarLogs0099.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0099.rows ScalarLogs0099.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0099.rows ScalarLogs0099.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0099.rows ScalarLogs0099.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0099.rows ScalarLogs0099.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0099.rows ScalarLogs0099.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0099.rows ScalarLogs0099.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0099.rows ScalarLogs0099.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0099.rows ScalarLogs0099.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0099.rows ScalarLogs0099.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0099.rows ScalarLogs0099.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0099.rows ScalarLogs0099.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0099.rows ScalarLogs0099.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0049.bracket0799 BracketBatch0050.bracket0800 (2934502398505008553366552241400726543523/10000000000000000000000000000000000000000) (1250869671645503865380097192013775269/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0049.bracket0799 BracketBatch0050.bracket0800
  (2934502398505008553366552241400726543523/10000000000000000000000000000000000000000) (1250869671645503865380097192013775269/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0799
