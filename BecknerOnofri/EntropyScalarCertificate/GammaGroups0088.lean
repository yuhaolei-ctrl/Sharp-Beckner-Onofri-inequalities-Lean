module

public import BecknerOnofri.EntropyScalarCertificate.Bessel0110
public import BecknerOnofri.EntropyScalarCertificate.Bessel0111
public import BecknerOnofri.EntropyScalarCertificate.Bessel0543
public import BecknerOnofri.EntropyScalarCertificate.Bessel0544
public import BecknerOnofri.EntropyScalarCertificate.Brackets0044
public import BecknerOnofri.EntropyScalarCertificate.Logs0088
public import BecknerOnofri.ScalarElementaryComposition
public import BecknerOnofri.ScalarGammaEnclosure
public import BecknerOnofri.ScalarLogBesselEndpoints

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0704
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0110.rows BesselBatch0110.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0110.rows BesselBatch0110.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0110.rows BesselBatch0110.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0110.rows BesselBatch0110.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0110.rows BesselBatch0110.accepted ⟨4,by decide⟩
]
theorem leftAccepted : besselPointCheck (2012695445496929176670589178607789805513/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (2012695445496929176670589178607789805513/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0110.rows BesselBatch0110.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0110.rows BesselBatch0110.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0110.rows BesselBatch0110.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0110.rows BesselBatch0110.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0110.rows BesselBatch0110.accepted ⟨19,by decide⟩
]
theorem rightAccepted : besselPointCheck (201481901771358391730643737110145183433/1000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (201481901771358391730643737110145183433/1000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0543.rows BesselBatch0543.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0543.rows BesselBatch0543.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0543.rows BesselBatch0543.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0543.rows BesselBatch0543.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0543.rows BesselBatch0543.accepted ⟨62,by decide⟩
]
theorem midAccepted : besselPointCheck (4027514463210513093977026549709241639843/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (4027514463210513093977026549709241639843/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0088.rows ScalarLogs0088.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0088.rows ScalarLogs0088.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0088.rows ScalarLogs0088.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0088.rows ScalarLogs0088.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0088.rows ScalarLogs0088.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0088.rows ScalarLogs0088.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0088.rows ScalarLogs0088.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0088.rows ScalarLogs0088.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0088.rows ScalarLogs0088.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0088.rows ScalarLogs0088.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0088.rows ScalarLogs0088.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0088.rows ScalarLogs0088.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0088.rows ScalarLogs0088.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0088.rows ScalarLogs0088.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0088.rows ScalarLogs0088.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0088.rows ScalarLogs0088.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0044.bracket0704 BracketBatch0044.bracket0705 (4027514463210513093977026549709241639843/20000000000000000000000000000000000000000) (239786615353969092916790830677100047/2000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0044.bracket0704 BracketBatch0044.bracket0705
  (4027514463210513093977026549709241639843/20000000000000000000000000000000000000000) (239786615353969092916790830677100047/2000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0704
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0705
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0110.rows BesselBatch0110.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0110.rows BesselBatch0110.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0110.rows BesselBatch0110.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0110.rows BesselBatch0110.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0110.rows BesselBatch0110.accepted ⟨14,by decide⟩
]
theorem leftAccepted : besselPointCheck (2014819017713583917306437371101451834327/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (2014819017713583917306437371101451834327/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0110.rows BesselBatch0110.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0110.rows BesselBatch0110.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0110.rows BesselBatch0110.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0110.rows BesselBatch0110.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0110.rows BesselBatch0110.accepted ⟨29,by decide⟩
]
theorem rightAccepted : besselPointCheck (504235713687621383239887672049553067997/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (504235713687621383239887672049553067997/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0543.rows BesselBatch0543.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0544.rows BesselBatch0544.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0544.rows BesselBatch0544.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0544.rows BesselBatch0544.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0544.rows BesselBatch0544.accepted ⟨3,by decide⟩
]
theorem midAccepted : besselPointCheck (806352374492813890053197611859932821263/4000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (806352374492813890053197611859932821263/4000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0088.rows ScalarLogs0088.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0088.rows ScalarLogs0088.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0088.rows ScalarLogs0088.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0088.rows ScalarLogs0088.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0088.rows ScalarLogs0088.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0088.rows ScalarLogs0088.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0088.rows ScalarLogs0088.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0088.rows ScalarLogs0088.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0088.rows ScalarLogs0088.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0088.rows ScalarLogs0088.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0088.rows ScalarLogs0088.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0088.rows ScalarLogs0088.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0088.rows ScalarLogs0088.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0088.rows ScalarLogs0088.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0088.rows ScalarLogs0088.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0088.rows ScalarLogs0088.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0044.bracket0705 BracketBatch0044.bracket0706 (806352374492813890053197611859932821263/4000000000000000000000000000000000000000) (601921375818206870507420929002070243/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0044.bracket0705 BracketBatch0044.bracket0706
  (806352374492813890053197611859932821263/4000000000000000000000000000000000000000) (601921375818206870507420929002070243/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0705
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0706
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0110.rows BesselBatch0110.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0110.rows BesselBatch0110.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0110.rows BesselBatch0110.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0110.rows BesselBatch0110.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0110.rows BesselBatch0110.accepted ⟨24,by decide⟩
]
theorem leftAccepted : besselPointCheck (403388570950097106591910137639642454397/2000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (403388570950097106591910137639642454397/2000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0110.rows BesselBatch0110.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0110.rows BesselBatch0110.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0110.rows BesselBatch0110.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0110.rows BesselBatch0110.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0110.rows BesselBatch0110.accepted ⟨39,by decide⟩
]
theorem rightAccepted : besselPointCheck (252383369617112308697341304416002313137/1250000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (252383369617112308697341304416002313137/1250000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0544.rows BesselBatch0544.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0544.rows BesselBatch0544.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0544.rows BesselBatch0544.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0544.rows BesselBatch0544.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0544.rows BesselBatch0544.accepted ⟨8,by decide⟩
]
theorem midAccepted : besselPointCheck (4036009811687384002538281123526230777081/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (4036009811687384002538281123526230777081/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0088.rows ScalarLogs0088.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0088.rows ScalarLogs0088.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0088.rows ScalarLogs0088.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0088.rows ScalarLogs0088.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0088.rows ScalarLogs0088.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0088.rows ScalarLogs0088.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0088.rows ScalarLogs0088.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0088.rows ScalarLogs0088.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0088.rows ScalarLogs0088.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0088.rows ScalarLogs0088.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0088.rows ScalarLogs0088.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0088.rows ScalarLogs0088.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0088.rows ScalarLogs0088.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0088.rows ScalarLogs0088.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0088.rows ScalarLogs0088.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0088.rows ScalarLogs0088.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0044.bracket0706 BracketBatch0044.bracket0707 (4036009811687384002538281123526230777081/20000000000000000000000000000000000000000) (302191901799414027958021813879250079/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0044.bracket0706 BracketBatch0044.bracket0707
  (4036009811687384002538281123526230777081/20000000000000000000000000000000000000000) (302191901799414027958021813879250079/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0706
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0707
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0110.rows BesselBatch0110.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0110.rows BesselBatch0110.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0110.rows BesselBatch0110.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0110.rows BesselBatch0110.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0110.rows BesselBatch0110.accepted ⟨34,by decide⟩
]
theorem leftAccepted : besselPointCheck (2019066956936898469578730435328018505093/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (2019066956936898469578730435328018505093/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0110.rows BesselBatch0110.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0110.rows BesselBatch0110.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0110.rows BesselBatch0110.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0110.rows BesselBatch0110.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0110.rows BesselBatch0110.accepted ⟨49,by decide⟩
]
theorem rightAccepted : besselPointCheck (404238264920458583515407069313256922557/2000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (404238264920458583515407069313256922557/2000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0544.rows BesselBatch0544.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0544.rows BesselBatch0544.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0544.rows BesselBatch0544.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0544.rows BesselBatch0544.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0544.rows BesselBatch0544.accepted ⟨13,by decide⟩
]
theorem midAccepted : besselPointCheck (2020129140769595693577882890947151558939/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (2020129140769595693577882890947151558939/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0088.rows ScalarLogs0088.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0088.rows ScalarLogs0088.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0088.rows ScalarLogs0088.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0088.rows ScalarLogs0088.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0088.rows ScalarLogs0088.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0088.rows ScalarLogs0088.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0088.rows ScalarLogs0088.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0088.rows ScalarLogs0088.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0088.rows ScalarLogs0088.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0088.rows ScalarLogs0088.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0088.rows ScalarLogs0088.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0088.rows ScalarLogs0088.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0088.rows ScalarLogs0088.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0088.rows ScalarLogs0088.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0088.rows ScalarLogs0088.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0088.rows ScalarLogs0088.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0044.bracket0707 BracketBatch0044.bracket0708 (2020129140769595693577882890947151558939/10000000000000000000000000000000000000000) (4741045607322051258913019561087029/39062500000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0044.bracket0707 BracketBatch0044.bracket0708
  (2020129140769595693577882890947151558939/10000000000000000000000000000000000000000) (4741045607322051258913019561087029/39062500000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0707
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0708
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0110.rows BesselBatch0110.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0110.rows BesselBatch0110.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0110.rows BesselBatch0110.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0110.rows BesselBatch0110.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0110.rows BesselBatch0110.accepted ⟨44,by decide⟩
]
theorem leftAccepted : besselPointCheck (1010595662301146458788517673283142306391/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1010595662301146458788517673283142306391/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0110.rows BesselBatch0110.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0110.rows BesselBatch0110.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0110.rows BesselBatch0110.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0110.rows BesselBatch0110.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0110.rows BesselBatch0110.accepted ⟨59,by decide⟩
]
theorem rightAccepted : besselPointCheck (1011657979038172565518390403404584965257/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1011657979038172565518390403404584965257/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0544.rows BesselBatch0544.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0544.rows BesselBatch0544.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0544.rows BesselBatch0544.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0544.rows BesselBatch0544.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0544.rows BesselBatch0544.accepted ⟨18,by decide⟩
]
theorem midAccepted : besselPointCheck (63195426291853719509590877396491477239/312500000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (63195426291853719509590877396491477239/312500000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0088.rows ScalarLogs0088.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0088.rows ScalarLogs0088.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0088.rows ScalarLogs0088.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0088.rows ScalarLogs0088.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0088.rows ScalarLogs0088.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0088.rows ScalarLogs0088.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0088.rows ScalarLogs0088.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0088.rows ScalarLogs0088.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0088.rows ScalarLogs0088.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0088.rows ScalarLogs0088.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0088.rows ScalarLogs0088.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0088.rows ScalarLogs0088.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0088.rows ScalarLogs0088.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0088.rows ScalarLogs0088.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0088.rows ScalarLogs0088.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0088.rows ScalarLogs0088.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0044.bracket0708 BracketBatch0044.bracket0709 (63195426291853719509590877396491477239/312500000000000000000000000000000000000) (243732597705078618038678696080938793/2000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0044.bracket0708 BracketBatch0044.bracket0709
  (63195426291853719509590877396491477239/312500000000000000000000000000000000000) (243732597705078618038678696080938793/2000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0708
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0709
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0110.rows BesselBatch0110.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0110.rows BesselBatch0110.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0110.rows BesselBatch0110.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0110.rows BesselBatch0110.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0110.rows BesselBatch0110.accepted ⟨54,by decide⟩
]
theorem leftAccepted : besselPointCheck (2023315958076345131036780806809169930511/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (2023315958076345131036780806809169930511/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0111.rows BesselBatch0111.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0111.rows BesselBatch0111.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0111.rows BesselBatch0111.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0111.rows BesselBatch0111.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0111.rows BesselBatch0111.accepted ⟨5,by decide⟩
]
theorem rightAccepted : besselPointCheck (1012720428844468873658704790796484054431/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1012720428844468873658704790796484054431/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0544.rows BesselBatch0544.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0544.rows BesselBatch0544.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0544.rows BesselBatch0544.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0544.rows BesselBatch0544.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0544.rows BesselBatch0544.accepted ⟨23,by decide⟩
]
theorem midAccepted : besselPointCheck (4048756815765282878354190388402138039373/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (4048756815765282878354190388402138039373/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0088.rows ScalarLogs0088.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0088.rows ScalarLogs0088.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0088.rows ScalarLogs0088.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0088.rows ScalarLogs0088.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0088.rows ScalarLogs0088.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0088.rows ScalarLogs0088.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0088.rows ScalarLogs0088.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0088.rows ScalarLogs0088.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0088.rows ScalarLogs0088.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0088.rows ScalarLogs0088.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0088.rows ScalarLogs0088.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0088.rows ScalarLogs0088.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0088.rows ScalarLogs0088.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0088.rows ScalarLogs0088.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0088.rows ScalarLogs0088.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0088.rows ScalarLogs0088.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0044.bracket0709 BracketBatch0044.bracket0710 (4048756815765282878354190388402138039373/20000000000000000000000000000000000000000) (611816789223434872914975387159713493/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0044.bracket0709 BracketBatch0044.bracket0710
  (4048756815765282878354190388402138039373/20000000000000000000000000000000000000000) (611816789223434872914975387159713493/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0709
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0710
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0110.rows BesselBatch0110.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0110.rows BesselBatch0110.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0110.rows BesselBatch0110.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0110.rows BesselBatch0110.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0111.rows BesselBatch0111.accepted ⟨0,by decide⟩
]
theorem leftAccepted : besselPointCheck (2025440857688937747317409581592968108859/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (2025440857688937747317409581592968108859/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0111.rows BesselBatch0111.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0111.rows BesselBatch0111.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0111.rows BesselBatch0111.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0111.rows BesselBatch0111.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0111.rows BesselBatch0111.accepted ⟨15,by decide⟩
]
theorem rightAccepted : besselPointCheck (2027566023770160107067018649634342187891/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (2027566023770160107067018649634342187891/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0544.rows BesselBatch0544.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0544.rows BesselBatch0544.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0544.rows BesselBatch0544.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0544.rows BesselBatch0544.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0544.rows BesselBatch0544.accepted ⟨28,by decide⟩
]
theorem midAccepted : besselPointCheck (16212027525836391417537712924909241187/80000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (16212027525836391417537712924909241187/80000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0088.rows ScalarLogs0088.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0088.rows ScalarLogs0088.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0088.rows ScalarLogs0088.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0088.rows ScalarLogs0088.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0088.rows ScalarLogs0088.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0088.rows ScalarLogs0088.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0088.rows ScalarLogs0088.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0088.rows ScalarLogs0088.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0088.rows ScalarLogs0088.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0088.rows ScalarLogs0088.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0088.rows ScalarLogs0088.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0088.rows ScalarLogs0088.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0088.rows ScalarLogs0088.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0088.rows ScalarLogs0088.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0088.rows ScalarLogs0088.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0088.rows ScalarLogs0088.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0044.bracket0710 BracketBatch0044.bracket0711 (16212027525836391417537712924909241187/80000000000000000000000000000000000000) (1228619477373019897612689336430147943/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0044.bracket0710 BracketBatch0044.bracket0711
  (16212027525836391417537712924909241187/80000000000000000000000000000000000000) (1228619477373019897612689336430147943/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0710
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0711
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0111.rows BesselBatch0111.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0111.rows BesselBatch0111.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0111.rows BesselBatch0111.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0111.rows BesselBatch0111.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0111.rows BesselBatch0111.accepted ⟨10,by decide⟩
]
theorem leftAccepted : besselPointCheck (126722876485635006691688665602146386743/625000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (126722876485635006691688665602146386743/625000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0111.rows BesselBatch0111.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0111.rows BesselBatch0111.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0111.rows BesselBatch0111.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0111.rows BesselBatch0111.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0111.rows BesselBatch0111.accepted ⟨25,by decide⟩
]
theorem rightAccepted : besselPointCheck (2029691456650308574638328222040634127117/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (2029691456650308574638328222040634127117/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0544.rows BesselBatch0544.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0544.rows BesselBatch0544.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0544.rows BesselBatch0544.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0544.rows BesselBatch0544.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0544.rows BesselBatch0544.accepted ⟨33,by decide⟩
]
theorem midAccepted : besselPointCheck (811451496084093736341069374334995263001/4000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (811451496084093736341069374334995263001/4000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0088.rows ScalarLogs0088.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0088.rows ScalarLogs0088.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0088.rows ScalarLogs0088.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0088.rows ScalarLogs0088.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0088.rows ScalarLogs0088.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0088.rows ScalarLogs0088.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0088.rows ScalarLogs0088.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0088.rows ScalarLogs0088.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0088.rows ScalarLogs0088.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0088.rows ScalarLogs0088.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0088.rows ScalarLogs0088.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0088.rows ScalarLogs0088.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0088.rows ScalarLogs0088.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0088.rows ScalarLogs0088.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0088.rows ScalarLogs0088.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0088.rows ScalarLogs0088.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0044.bracket0711 BracketBatch0044.bracket0712 (811451496084093736341069374334995263001/4000000000000000000000000000000000000000) (123362071747578112375112239069206137/1000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0044.bracket0711 BracketBatch0044.bracket0712
  (811451496084093736341069374334995263001/4000000000000000000000000000000000000000) (123362071747578112375112239069206137/1000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0711
