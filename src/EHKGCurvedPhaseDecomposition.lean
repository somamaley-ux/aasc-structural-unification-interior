import EHKGWeightedPhaseContinuity
import EHKGCompactCauchyData

/-! Exact four-phase expression for the actual curved compact-data family.
The coefficients, Fourier normalization, auxiliary mass and coordinate map
are inherited; this is an equality of the constructed functions. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
open Set Filter MeasureTheory TopologicalSpace AASCSemanticExhaustion
open scoped SchwartzMap FourierTransform Topology
namespace AASCKleinGordon.CurvedKG

def realCoefficientCLM (c : ℂ) : ℂ →L[ℝ] ℝ :=
  Complex.reCLM.comp ((c • ContinuousLinearMap.id ℂ ℂ).restrictScalars ℝ)

theorem real_coefficient_apply (c z : ℂ) : realCoefficientCLM c z = (c * z).re := rfl

def coordinateSpacetimeCLM : CoordinatePoint →L[ℝ] Spacetime :=
  wickSpacetimeCoordinates.symm.toContinuousLinearMap

theorem spacetime_join_coordinate_split (p : CoordinatePoint) :
    spacetimeSpatialJoin (coordinateSpatialSplit p) = coordinateSpacetimeCLM p := by
  change spacetimeSpatialJoin (spacetimeSpatialJoin.symm (wickSpacetimeCoordinates.symm p)) = _
  exact spacetimeSpatialJoin.apply_symm_apply _

def curvedCosineWeight (a : Parameters) (p : CoordinatePoint) : ℝ :=
  Real.cos (conformalFrequency a * p 0)

theorem curved_cosine_weight_smooth (a : Parameters) :
    ContDiff ℝ (⊤ : ℕ∞) (curvedCosineWeight a) := by
  unfold curvedCosineWeight
  fun_prop

def compactFourierDataCLM (U : Opens KGSpatialSpace) :
    TestFunction U ℝ (⊤ : ℕ∞) →L[ℝ] 𝓢(KGSpatialSpace, ℂ) :=
  (FourierTransform.fourierCLM ℝ 𝓢(KGSpatialSpace, ℂ)).comp (compactCauchySchwartzCLM U)

def compactSineFourierDataCLM (a : Parameters) (U : Opens KGSpatialSpace) :
    TestFunction U ℝ (⊤ : ℕ∞) →L[ℝ] 𝓢(KGSpatialSpace, ℂ) :=
  ((spatialInverseOmegaMultiplierCLM (auxiliaryKGParameters a)).restrictScalars ℝ).comp
    (compactFourierDataCLM U)

def curvedWeightedPhase (a : Parameters) (sign : ℝ) (c : ℂ)
    (G : 𝓢(KGSpatialSpace, ℂ)) : CoordinatePoint → ℝ :=
  weightedPhaseField (homogeneousPhaseFrequency (auxiliaryKGParameters a) sign)
    coordinateSpacetimeCLM (realCoefficientCLM c) (curvedCosineWeight a) G

theorem curved_weighted_phase_smooth (a : Parameters) (sign : ℝ) (c : ℂ)
    (G : 𝓢(KGSpatialSpace, ℂ)) : ContDiff ℝ (⊤ : ℕ∞) (curvedWeightedPhase a sign c G) :=
  weighted_phase_smooth _ (homogeneous_phase_frequency_temperate _ _) _ _ _
    (curved_cosine_weight_smooth a) G

theorem compact_curved_four_phase (a : Parameters) (U : Opens KGSpatialSpace)
    (f h : TestFunction U ℝ (⊤ : ℕ∞)) :
    compactCurvedField a U f h =
      ((curvedWeightedPhase a 1 (1 / 2) (compactFourierDataCLM U f) +
        curvedWeightedPhase a (-1) (1 / 2) (compactFourierDataCLM U f)) +
        curvedWeightedPhase a 1 ((2 * Complex.I)⁻¹) (compactSineFourierDataCLM a U h)) +
        curvedWeightedPhase a (-1) (-((2 * Complex.I)⁻¹)) (compactSineFourierDataCLM a U h) := by
  funext p
  have cosine := cosine_phase_average (auxiliaryKGParameters a)
    (𝓕 (compactCauchySchwartzCLM U f)) (coordinateSpatialSplit p).1 (coordinateSpatialSplit p).2
  have sine := sine_phase_difference (auxiliaryKGParameters a)
    (𝓕 (compactCauchySchwartzCLM U h)) (coordinateSpatialSplit p).1 (coordinateSpatialSplit p).2
  have joinEq : spacetimeSpatialJoin ((coordinateSpatialSplit p).1, (coordinateSpatialSplit p).2) =
      coordinateSpacetimeCLM p := spacetime_join_coordinate_split p
  rw [joinEq] at cosine sine
  change curvedCosineWeight a p * Complex.re
    (spatialCosineSolutionCLM (auxiliaryKGParameters a) (coordinateSpatialSplit p).1
      (compactCauchySchwartzCLM U f) (coordinateSpatialSplit p).2 +
     spatialSineSolutionCLM (auxiliaryKGParameters a) (coordinateSpatialSplit p).1
      (compactCauchySchwartzCLM U h) (coordinateSpatialSplit p).2) = _
  change _ = _ at cosine sine
  rw [show spatialCosineSolutionCLM (auxiliaryKGParameters a) (coordinateSpatialSplit p).1
      (compactCauchySchwartzCLM U f) (coordinateSpatialSplit p).2 = _ from cosine.symm,
    show spatialSineSolutionCLM (auxiliaryKGParameters a) (coordinateSpatialSplit p).1
      (compactCauchySchwartzCLM U h) (coordinateSpatialSplit p).2 = _ from sine.symm]
  simp only [curvedWeightedPhase, weightedPhaseField, real_coefficient_apply,
    compactFourierDataCLM, compactSineFourierDataCLM,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_restrictScalars',
    FourierTransform.fourierCLM_apply, Pi.add_apply, mul_add, mul_sub, Complex.add_re,
    Complex.sub_re, neg_mul, Complex.neg_re]
  ring

end AASCKleinGordon.CurvedKG
