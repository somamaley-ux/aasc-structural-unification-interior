import EHKGConstructedCurvedField
import KGCompactTestSchwartz

/-! All compact smooth real data on a declared open spatial leaf, with their
actual LF-to-Schwartz inclusion. This does not assert Cauchy geometry or
LF-to-smooth-field continuity, which are separate downstream obligations. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
open Set Filter TopologicalSpace AASCSemanticExhaustion
open scoped SchwartzMap Topology
namespace AASCKleinGordon.CurvedKG

def compactCauchySchwartzCLM (U : Opens KGSpatialSpace) :
    TestFunction U ℝ (⊤ : ℕ∞) →L[ℝ] 𝓢(KGSpatialSpace, ℂ) :=
  (wickCompactTestToSchwartzCLM (F := ℂ) U).comp
    (TestFunction.postcompCLM Complex.ofRealCLM)

theorem compact_cauchy_schwartz_apply (U : Opens KGSpatialSpace)
    (f : TestFunction U ℝ (⊤ : ℕ∞)) (x : KGSpatialSpace) :
    compactCauchySchwartzCLM U f x = (f x : ℂ) := rfl

theorem compact_cauchy_initializer_lf_continuous (U : Opens KGSpatialSpace) :
    Continuous (compactCauchySchwartzCLM U) := (compactCauchySchwartzCLM U).continuous

def compactCurvedField (a : Parameters) (U : Opens KGSpatialSpace)
    (f h : TestFunction U ℝ (⊤ : ℕ∞)) : CoordinatePoint → ℝ :=
  curvedCoordinateField a (compactCauchySchwartzCLM U f) (compactCauchySchwartzCLM U h)
    Complex.reCLM

theorem compact_curved_field_smooth (a : Parameters) (U : Opens KGSpatialSpace)
    (f h : TestFunction U ℝ (⊤ : ℕ∞)) :
    ContDiff ℝ (⊤ : ℕ∞) (compactCurvedField a U f h) :=
  curved_coordinate_smooth _ _ _ _

theorem compact_curved_field_equation (a : Parameters) (U : Opens KGSpatialSpace)
    (f h : TestFunction U ℝ (⊤ : ℕ∞)) (p : CoordinatePoint)
    (inside : p ∈ protectedConformalBall (conformalFrequency a)) :
    scalarFieldWaveOperator (originalEHActMetric (conformalOperand (conformalFrequency a)))
      (compactCurvedField a U f h) p =
        (massWaveNumber a) ^ 2 * compactCurvedField a U f h p :=
  constructed_same_eh_curved_field_equation _ _ _ _ p inside

theorem compact_curved_initial_position (a : Parameters) (U : Opens KGSpatialSpace)
    (f h : TestFunction U ℝ (⊤ : ℕ∞)) (p : CoordinatePoint) (initialTime : p 0 = 0) :
    compactCurvedField a U f h p = f (coordinateSpatialSplit p).2 := by
  rw [compactCurvedField, constructed_curved_initial_position _ _ _ _ p initialTime]
  rfl

theorem compact_curved_initial_velocity (a : Parameters) (U : Opens KGSpatialSpace)
    (f h : TestFunction U ℝ (⊤ : ℕ∞)) (p : CoordinatePoint) (initialTime : p 0 = 0) :
    scalarPartial (compactCurvedField a U f h) p 0 = h (coordinateSpatialSplit p).2 := by
  rw [compactCurvedField, constructed_curved_initial_velocity _ _ _ _ p initialTime]
  rfl

theorem compact_cauchy_support_retained (U : Opens KGSpatialSpace)
    (f : TestFunction U ℝ (⊤ : ℕ∞)) :
    tsupport (compactCauchySchwartzCLM U f) = tsupport f := by
  change closure (Function.support (compactCauchySchwartzCLM U f)) = closure (Function.support f)
  congr 1
  ext x
  simp only [Function.mem_support, compact_cauchy_schwartz_apply, ne_eq,
    Complex.ofReal_eq_zero]

theorem compact_curved_field_add (a : Parameters) (U : Opens KGSpatialSpace)
    (f h f' h' : TestFunction U ℝ (⊤ : ℕ∞)) (p : CoordinatePoint) :
    compactCurvedField a U (f + f') (h + h') p =
      compactCurvedField a U f h p + compactCurvedField a U f' h' p := by
  simp only [compactCurvedField, curvedCoordinateField, flatCoordinateField,
    fullFlatPosition, map_add, SchwartzMap.add_apply]
  ring

theorem compact_curved_field_smul (a : Parameters) (U : Opens KGSpatialSpace)
    (f h : TestFunction U ℝ (⊤ : ℕ∞)) (r : ℝ) (p : CoordinatePoint) :
    compactCurvedField a U (r • f) (r • h) p = r * compactCurvedField a U f h p := by
  have cosineReal (t : ℝ) (F : 𝓢(KGSpatialSpace, ℂ)) :
      spatialCosineSolutionCLM (auxiliaryKGParameters a) t (r • F) =
        r • spatialCosineSolutionCLM (auxiliaryKGParameters a) t F :=
    ((spatialCosineSolutionCLM (auxiliaryKGParameters a) t).restrictScalars ℝ).map_smul r F
  have sineReal (t : ℝ) (F : 𝓢(KGSpatialSpace, ℂ)) :
      spatialSineSolutionCLM (auxiliaryKGParameters a) t (r • F) =
        r • spatialSineSolutionCLM (auxiliaryKGParameters a) t F :=
    ((spatialSineSolutionCLM (auxiliaryKGParameters a) t).restrictScalars ℝ).map_smul r F
  simp only [compactCurvedField, curvedCoordinateField, flatCoordinateField,
    fullFlatPosition, map_smul, cosineReal, sineReal, map_add, SchwartzMap.add_apply, SchwartzMap.smul_apply,
    smul_eq_mul]
  ring

end AASCKleinGordon.CurvedKG
