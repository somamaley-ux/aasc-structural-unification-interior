import OccupiedMetricProfiles
import EHKGCurvedOperand
import PointNormalChartConstruction
import C2GeneralCurvatureJetCongruence
import CoordinateCovariantDivergence
import EHKGCompactSmoothLocalization

/-! A compact original metric operand can reproduce the complete germ of a
smooth Lorentz metric in coordinates with normalized point value. The fixed
entry bound is uniform, while the size of the coordinate ball is free. -/
noncomputable section
set_option autoImplicit false
open AASCSemanticExhaustion AASCKleinGordon Filter Set TopologicalSpace
open scoped Topology ContDiff Matrix.Norms.Elementwise

namespace AASCOccupiedProfiles

private def cutoffCoefficients (g : MetricField) (x : CoordinatePoint) : Fin 10 → ℝ :=
  tensorDecode (g x - metric)

private theorem coefficients_smooth (g : MetricField) (smooth : SmoothCoordinateMetric g) :
    ContDiff ℝ ∞ (cutoffCoefficients g) := by
  apply contDiff_pi.mpr
  intro i
  fin_cases i <;> apply ContDiff.sub (smooth _ _) contDiff_const

private theorem cutoff_decodes (g : MetricField) (symmetric : MetricFieldSymmetric g)
    (x : CoordinatePoint) :
    tensorEncode (cutoffCoefficients g x) = g x - metric := by
  apply tensor_encode_decode
  intro i j
  simp only [Matrix.sub_apply, symmetric x i j]
  congr 1
  fin_cases i <;> fin_cases j <;> rfl

/-- On every neighborhood of the tested point, use a compact bump supported
where the metric differs from the normalized value by less than 1/32.
This leaves a strict margin in the original 1/16 bounded-function norm. -/
theorem exists_admitted_operand_eq_germ (Ω : Opens CoordinatePoint) (p : CoordinatePoint)
    (hp : p ∈ Ω) (g : MetricField) (symmetric : MetricFieldSymmetric g)
    (smooth : SmoothCoordinateMetric g) (atPoint : g p = metric) :
    ∃ H : AdmittedOperand Ω, originalEHActMetric H.1 =ᶠ[𝓝 p] g := by
  have near (i j : Fin 4) : ∀ᶠ x in 𝓝 p, |g x i j - metric i j| < 1 / 32 := by
    have hc : Continuous (fun x => |g x i j - metric i j|) :=
      ((smooth i j).continuous.sub continuous_const).abs
    exact hc.continuousAt.eventually_lt continuousAt_const (by simp [atPoint])
  have allNear : ∀ᶠ x in 𝓝 p, ∀ i j : Fin 4, |g x i j - metric i j| < 1 / 32 :=
    Filter.eventually_all.mpr (fun i => Filter.eventually_all.mpr (near i))
  obtain ⟨r, hr, inside⟩ := Metric.mem_nhds_iff.mp
    (allNear.and (Ω.isOpen.mem_nhds hp))
  let b : ContDiffBump p := ⟨r / 4, r / 2, by positivity, by linarith⟩
  have inBall {x} (hx : x ∈ tsupport b) : x ∈ Metric.ball p r := by
    rw [b.tsupport_eq, Metric.mem_closedBall] at hx
    exact Metric.mem_ball.mpr (lt_of_le_of_lt hx (by change r / 2 < r; linarith))
  let f : CoordinatePoint → Fin 10 → ℝ := fun x => b x • cutoffCoefficients g x
  have hsupport : Function.support f ⊆ Function.support b := by
    intro x hx
    contrapose! hx
    simp only [Function.mem_support, not_not] at hx ⊢
    simp [f, hx]
  have hs : tsupport f ⊆ tsupport b := closure_mono hsupport
  let H : MetricSourceProbe Ω :=
    ⟨f, b.contDiff.smul (coefficients_smooth g smooth),
     b.hasCompactSupport.mono hsupport, fun _ hx => (inside (inBall (hs hx))).2⟩
  have entries (x : CoordinatePoint) : tensorEncode (H x) = b x • (g x - metric) := by
    change tensorEncodeLinear (b x • cutoffCoefficients g x) = _
    rw [map_smul]
    change b x • tensorEncode (cutoffCoefficients g x) = _
    rw [cutoff_decodes g symmetric x]
  have bounded : H ∈ wickOriginalMetricNeighborhood Ω := by
    intro i j
    apply lt_of_le_of_lt (b := (1 : ℝ) / 32) _ (by norm_num)
    apply (BoundedContinuousFunction.norm_le (by norm_num)).mpr
    intro x
    rw [wick_native_bounded_entry_apply, entries, Matrix.smul_apply, smul_eq_mul,
      Matrix.sub_apply, Real.norm_eq_abs, abs_mul, abs_of_nonneg b.nonneg]
    by_cases hx : b x = 0
    · simp [hx]
    · have inSupport : x ∈ tsupport b := subset_closure hx
      exact (mul_le_of_le_one_left (abs_nonneg _) b.le_one).trans
        (((inside (inBall inSupport)).1 i j).le)
  refine ⟨⟨H, bounded⟩, ?_⟩
  filter_upwards [b.eventuallyEq_one] with x hx
  change b x = 1 at hx
  ext i j
  change wickNativeFlatMetric x i j + tensorEncode (H x) i j = g x i j
  rw [original_eh_native_flat_value, entries, hx, one_smul, Matrix.sub_apply]
  ring

/-- A single scalar cutoff shared by all tensor entries preserves symmetry.
Only values on the open chart are used. The extension is a test field and is
allowed to be degenerate outside the original germ. -/
private theorem smooth_symmetric_chart_extension (V : Opens CoordinatePoint)
    (p : CoordinatePoint) (hp : p ∈ V) (g : MetricField)
    (symmetric : ∀ x ∈ V, ∀ i j, g x i j = g x j i)
    (regular : ∀ i j, ContDiffOn ℝ ∞ (fun x => g x i j) (V : Set CoordinatePoint)) :
    ∃ g' : MetricField, MetricFieldSymmetric g' ∧ SmoothCoordinateMetric g' ∧
      g' =ᶠ[𝓝 p] g := by
  obtain ⟨β, smooth, _, supported, one⟩ :=
    CurvedKG.exists_compact_smooth_cutoff {p} V isCompact_singleton V.isOpen
      (Set.singleton_subset_iff.mpr hp)
  let g' : MetricField := fun x i j => β x * g x i j
  refine ⟨g', ?_, ?_, ?_⟩
  · intro x i j
    by_cases hx : x ∈ tsupport β
    · change β x * g x i j = β x * g x j i
      rw [symmetric x (supported hx) i j]
    · simp [g', image_eq_zero_of_notMem_tsupport hx]
  · intro i j
    apply contDiff_iff_contDiffAt.mpr
    intro x
    by_cases hx : x ∈ tsupport β
    · exact smooth.contDiffAt.mul ((regular i j).contDiffAt (V.isOpen.mem_nhds (supported hx)))
    · apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
      filter_upwards [(isClosed_tsupport β).isOpen_compl.mem_nhds hx] with y hy
      simp [g', image_eq_zero_of_notMem_tsupport hy]
  · filter_upwards [one p (Set.mem_singleton p)] with x hx
    ext i j
    simp [g', hx]

/-- A smooth metric given on an open chart has a globally smooth symmetric
representative of its germ, without assuming any smoothness outside the chart. -/
theorem exists_smooth_symmetric_field_eq_germ_on_open (V : Opens CoordinatePoint)
    (p : CoordinatePoint) (hp : p ∈ V) (g : MetricField)
    (symmetric : MetricFieldSymmetric g)
    (regular : ∀ i j, ContDiffOn ℝ ∞ (fun x => g x i j) (V : Set CoordinatePoint)) :
    ∃ g' : MetricField, MetricFieldSymmetric g' ∧ SmoothCoordinateMetric g' ∧
      g' =ᶠ[𝓝 p] g :=
  smooth_symmetric_chart_extension V p hp g (fun x _ => symmetric x) regular

/-- Even when symmetry and smoothness are given only on a local chart V, a
normalized germ is represented by an original bounded operand on Ω. -/
theorem exists_admitted_operand_of_chart_germ (Ω V : Opens CoordinatePoint)
    (p : CoordinatePoint) (hp : p ∈ Ω) (hpV : p ∈ V) (g : MetricField)
    (symmetric : ∀ x ∈ V, ∀ i j, g x i j = g x j i)
    (regular : ∀ i j, ContDiffOn ℝ ∞ (fun x => g x i j) (V : Set CoordinatePoint))
    (atPoint : g p = metric) :
    ∃ H : AdmittedOperand Ω, originalEHActMetric H.1 =ᶠ[𝓝 p] g := by
  obtain ⟨g', hs, hreg, germ⟩ := smooth_symmetric_chart_extension V p hpV g symmetric regular
  obtain ⟨H, operand⟩ :=
    exists_admitted_operand_eq_germ Ω p hp g' hs hreg (germ.eq_of_nhds.trans atPoint)
  exact ⟨H, operand.trans germ⟩

private theorem smooth_chart_pullback (g : MetricField) (smooth : SmoothCoordinateMetric g)
    (F : CoordinatePoint → CoordinatePoint) (regular : ContDiff ℝ ⊤ F) :
    SmoothCoordinateMetric (coordinateMetricPullback g F) := by
  intro a b
  apply contDiff_iff_contDiffAt.mpr
  intro x
  unfold coordinateMetricPullback
  apply ContDiffAt.sum
  intro i _
  apply ContDiffAt.sum
  intro j _
  exact (((coordinateJacobian_contDiffAt F x regular.contDiffAt i a).of_le le_top).mul
    (((smooth i j).contDiffAt).comp x (regular.of_le le_top).contDiffAt)).mul
      ((coordinateJacobian_contDiffAt F x regular.contDiffAt j b).of_le le_top)

/-- The affine frame is the actual coordinate pullback of the original metric.
No coordinate smallness is assumed at its original point. -/
theorem exists_admitted_operand_eq_framed_germ (Ω : Opens CoordinatePoint)
    (hΩ : (0 : CoordinatePoint) ∈ Ω) (g : MetricField) (p : CoordinatePoint)
    (B : CoordinatePoint ≃L[ℝ] CoordinatePoint) (symmetric : MetricFieldSymmetric g)
    (smooth : SmoothCoordinateMetric g) (frame : LorentzFrameAt g p B) :
    ∃ H : AdmittedOperand Ω, originalEHActMetric H.1 =ᶠ[𝓝 (0 : CoordinatePoint)]
      framedMetricField g p B :=
  exists_admitted_operand_eq_germ Ω 0 hΩ _ (framedMetricField_symmetric g p B symmetric)
    (smooth_chart_pullback g smooth _ (affineCoordinateMap_smooth p B))
    (framedMetricField_value g p B frame)

/-- The same construction in the genuine normal chart also retains the full
metric germ there (including its vanishing first derivatives at the origin). -/
theorem exists_admitted_operand_eq_normal_chart_germ (Ω : Opens CoordinatePoint)
    (hΩ : (0 : CoordinatePoint) ∈ Ω) (g : MetricField) (p : CoordinatePoint)
    (B : CoordinatePoint ≃L[ℝ] CoordinatePoint) (symmetric : MetricFieldSymmetric g)
    (smooth : SmoothCoordinateMetric g) (frame : LorentzFrameAt g p B) :
    ∃ H : AdmittedOperand Ω, originalEHActMetric H.1 =ᶠ[𝓝 (0 : CoordinatePoint)]
      pointNormalizedMetric g p B := by
  have actual := c2_pointNormalizedMetric_germ g p B symmetric
    (fun a b => (smooth a b).contDiffAt.of_le
      (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤))) frame
  apply exists_admitted_operand_eq_germ Ω 0 hΩ _ actual.1 _ actual.2.2.1
  rw [← pointNormalChartMap_pullback]
  exact smooth_chart_pullback g smooth _
    ((affineCoordinateMap_smooth p B).comp (normalizingCoordinateMap_smooth _))

/-- An operator determined at each point by the metric germ agrees on a
whole neighborhood whenever the two metric fields agree on a neighborhood. -/
theorem local_response_germs (E : MetricFieldResponse)
    (locality : ∀ g h p, (g =ᶠ[𝓝 p] h) → E g p = E h p)
    {g h : MetricField} {p : CoordinatePoint} (metrics : g =ᶠ[𝓝 p] h) :
    E g =ᶠ[𝓝 p] E h :=
  (eventually_eventually_nhds.mpr metrics).mono fun x hx => locality g h x hx

/-- The divergence of a response uses first derivatives of the response
and the connection of its metric. Both are retained by equality of germs. -/
theorem coordinate_divergence_of_equal_germs {g h T U : MetricField} {p : CoordinatePoint}
    (metrics : g =ᶠ[𝓝 p] h) (tensors : T =ᶠ[𝓝 p] U) :
    coordinateDivergence g T p = coordinateDivergence h U p := by
  have jets := metric_twojet_of_eventuallyEq g h p metrics
  have derivative (a b : Fin 4) :
      fderiv ℝ (fun x => T x a b) p = fderiv ℝ (fun x => U x a b) p :=
    Filter.EventuallyEq.fderiv_eq (tensors.mono
      (fun x hx => congrArg (fun A : Tensor2 => A a b) hx))
  funext b
  simp only [coordinateDivergence, coordinateCovariantTensorDerivative, scalarPartial,
    jets.1, leviCivita_metric_twojet_congr g h p jets, tensors.eq_of_nhds, derivative]

end AASCOccupiedProfiles
