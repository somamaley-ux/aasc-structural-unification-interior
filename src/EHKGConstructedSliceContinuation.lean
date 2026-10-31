import EHKGContainedContinuation

/-! Nonvacuous continuation for every original compact Cauchy pair. The
restart data are actual evaluated Fourier Cauchy data; their physical value
and unit-normal traces match by calculation. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
open Set Filter TopologicalSpace AASCSemanticExhaustion
open scoped SchwartzMap Topology
namespace AASCKleinGordon.CurvedKG

theorem curved_coordinate_position_slice (a : Parameters) (f h : 𝓢(KGSpatialSpace, ℂ))
    (time : ℝ) (x : KGSpatialSpace) :
    curvedCoordinateField a f h Complex.reCLM (evolutionSlicePoint time x) =
      Real.cos (conformalFrequency a * time) * (fullFlatPosition (auxiliaryKGParameters a) f h time x).re := by
  simp only [curvedCoordinateField, flatCoordinateField, coordinate_split_time, evolution_slice_time, evolution_slice_space]
  rfl

theorem curved_coordinate_normal_slice (a : Parameters) (f h : 𝓢(KGSpatialSpace, ℂ))
    (time : ℝ) (x : KGSpatialSpace) :
    actualNormalDerivative (conformalFrequency a) (curvedCoordinateField a f h Complex.reCLM) (evolutionSlicePoint time x) =
      Real.cos (conformalFrequency a * time) *
        (-(conformalFrequency a) * Real.sin (conformalFrequency a * time) *
            (fullFlatPosition (auxiliaryKGParameters a) f h time x).re +
          Real.cos (conformalFrequency a * time) * (fullFlatVelocity (auxiliaryKGParameters a) f h time x).re) := by
  let p := evolutionSlicePoint time x
  have phase : HasFDerivAt (fun q : CoordinatePoint => conformalFrequency a * q 0)
      (conformalFrequency a • (ContinuousLinearMap.proj (0 : Fin 4) : CoordinatePoint →L[ℝ] ℝ)) p :=
    (ContinuousLinearMap.proj (0 : Fin 4) : CoordinatePoint →L[ℝ] ℝ).hasFDerivAt.const_mul (conformalFrequency a)
  have cosine := (Real.hasDerivAt_cos (conformalFrequency a * p 0)).comp_hasFDerivAt p phase
  have productDerivative := (cosine.mul ((flat_coordinate_smooth (auxiliaryKGParameters a) f h Complex.reCLM).differentiable (by simp) p).hasFDerivAt).fderiv
  change fderiv ℝ (fun q => Real.cos (conformalFrequency a * q 0) *
    flatCoordinateField (auxiliaryKGParameters a) f h Complex.reCLM q) p = _ at productDerivative
  have position : flatCoordinateField (auxiliaryKGParameters a) f h Complex.reCLM p =
      (fullFlatPosition (auxiliaryKGParameters a) f h time x).re := by
    simp only [flatCoordinateField, coordinate_split_time, p, evolution_slice_time, evolution_slice_space]
    rfl
  have velocity : scalarPartial (flatCoordinateField (auxiliaryKGParameters a) f h Complex.reCLM) p 0 =
      (fullFlatVelocity (auxiliaryKGParameters a) f h time x).re := by
    rw [flat_coordinate_time_partial, flatCoordinateField, coordinate_split_time]
    dsimp only [p]
    rw [evolution_slice_time, evolution_slice_space, ← full_flat_velocity_as_position]
    rfl
  rw [normal_derivative_is_cosine_partial, evolution_slice_time]
  change Real.cos (conformalFrequency a * time) *
    fderiv ℝ (fun q => Real.cos (conformalFrequency a * q 0) *
      flatCoordinateField (auxiliaryKGParameters a) f h Complex.reCLM q) p (Pi.single 0 1) = _
  rw [productDerivative]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul, Function.comp_apply]
  change Real.cos (conformalFrequency a * time) *
    (Real.cos (conformalFrequency a * p 0) * scalarPartial (flatCoordinateField (auxiliaryKGParameters a) f h Complex.reCLM) p 0 +
      flatCoordinateField (auxiliaryKGParameters a) f h Complex.reCLM p *
        (-Real.sin (conformalFrequency a * p 0) * (conformalFrequency a * 1))) = _
  rw [position, velocity]
  dsimp only [p]
  rw [evolution_slice_time]
  ring

def evaluatedScalarContinuation (a : Parameters)
    (f h : TestFunction (centralLeafDomain (conformalFrequency a)) ℝ (⊤ : ℕ∞))
    (time scale : ℝ) : ScalarContinuationRequest where
  time := time
  scale := scale
  position := fullFlatPosition (auxiliaryKGParameters a)
    (compactCauchySchwartzCLM _ f) (compactCauchySchwartzCLM _ h) time
  velocity := fullFlatVelocity (auxiliaryKGParameters a)
    (compactCauchySchwartzCLM _ f) (compactCauchySchwartzCLM _ h) time

theorem evaluated_scalar_continuation_matches (a : Parameters)
    (f h : TestFunction (centralLeafDomain (conformalFrequency a)) ℝ (⊤ : ℕ∞)) (time scale : ℝ) :
    scalarContinuationDataMatch a (initialCurvedScalarUseState a f h) (evaluatedScalarContinuation a f h time scale) := by
  intro x hx
  change shiftedCurvedSchwartzField a time _ _ (affineCauchyPoint time scale x) =
      curvedCoordinateField a _ _ Complex.reCLM (affineCauchyPoint time scale x) ∧
    actualNormalDerivative (conformalFrequency a) (shiftedCurvedSchwartzField a time _ _)
        (affineCauchyPoint time scale x) =
      actualNormalDerivative (conformalFrequency a) (curvedCoordinateField a _ _ Complex.reCLM)
        (affineCauchyPoint time scale x)
  rw [affine_cauchy_is_slice, shifted_curved_position, curved_coordinate_position_slice,
    shifted_curved_normal, curved_coordinate_normal_slice]
  exact ⟨rfl, rfl⟩

theorem all_compact_data_genuine_slice_continuation (a : Parameters)
    (f h : TestFunction (centralLeafDomain (conformalFrequency a)) ℝ (⊤ : ℕ∞)) :
    ∃ time : ℝ, time ≠ 0 ∧ ∃ scale : ℝ, 0 < scale ∧
      ∃ result : CurvedScalarUseState a,
        scalarContinue a (initialCurvedScalarUseState a f h) (evaluatedScalarContinuation a f h time scale) = .ok result ∧
        result.domain = scalarContinuationDomain a (evaluatedScalarContinuation a f h time scale) ∧
        EqOn result.field (initialCurvedScalarUseState a f h).field result.domain := by
  let time := protectedRadius (conformalFrequency a) / 4
  let scale : ℝ := 1 / 4
  have geometry := quarter_shifted_diamond (conformalFrequency a)
  have inside : scalarContinuationDomain a (evaluatedScalarContinuation a f h time scale) ≤
      (initialCurvedScalarUseState a f h).domain := geometry.2.2
  have matching := evaluated_scalar_continuation_matches a f h time scale
  let result := continuedCurvedScalarState a (initialCurvedScalarUseState a f h)
    (evaluatedScalarContinuation a f h time scale) inside
  refine ⟨time, geometry.1, scale, by norm_num [scale], result, ?_, rfl, ?_⟩
  · exact scalar_continue_success a _ _ (by norm_num [evaluatedScalarContinuation, scale]) inside matching
  · exact continued_state_agrees a _ _ (by norm_num [evaluatedScalarContinuation, scale]) inside matching

end AASCKleinGordon.CurvedKG
