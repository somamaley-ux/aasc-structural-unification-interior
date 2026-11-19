import OccupiedSmoothMetricResponse

/-! Intrinsic differential order of a response on actual smooth metric germs.
All finite jet orders are candidates. The lower bound uses normal coordinates
and the stabilizer of the flat Lorentz metric, independently of conservation
or any assumption about the degree in curvature. -/
namespace AASCSemanticExhaustion
noncomputable section
open Filter
open scoped Topology ContDiff Matrix.Norms.Elementwise

def SmoothLorentzOperand (g : MetricField) (p : CoordinatePoint) : Prop :=
  MetricFieldSymmetric g ∧ (∀ a b, ContDiffAt ℝ ∞ (fun x => g x a b) p) ∧
    ∃ B : CoordinatePoint ≃L[ℝ] CoordinatePoint, LorentzFrameAt g p B

private theorem smooth_operand_regular {g : MetricField} {p : CoordinatePoint}
    (h : SmoothLorentzOperand g p) : C2LorentzMetricAt g p :=
  ⟨h.1, fun a b => (h.2.1 a b).of_le (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤)), h.2.2⟩

private theorem normalized_smooth_operand {g : MetricField} (h : NormalizedSmoothMetricGerm g) :
    SmoothLorentzOperand g 0 :=
  ⟨h.1, fun a b => (h.2.1 a b).of_le le_top, ContinuousLinearEquiv.refl ℝ CoordinatePoint,
    c2_normalizedMetric_identity_frame g (original_smooth_normalized_is_c2 g h)⟩

/-- Equality of the actual metric and all coordinate derivatives through n.
The second derivative is expressed in the coordinate basis used by the native
two-jet definition. Higher derivatives are compared as multilinear maps. -/
def SameMetricJetThrough : ℕ → MetricField → MetricField → CoordinatePoint → Prop
  | 0, g, h, p => g p = h p
  | 1, g, h, p => g p = h p ∧
      ∀ a b, fderiv ℝ (fun x => g x a b) p = fderiv ℝ (fun x => h x a b) p
  | n + 2, g, h, p => MetricTwoJetEqualAt g h p ∧
      ∀ k, 3 ≤ k → k ≤ n + 2 → ∀ a b,
        iteratedFDeriv ℝ k (fun x => g x a b) p = iteratedFDeriv ℝ k (fun x => h x a b) p

def SmoothMetricResponseOrderAtMost (E : MetricFieldResponse) (n : ℕ) : Prop :=
  ∀ g h p, SmoothLorentzOperand g p → SmoothLorentzOperand h p →
    SameMetricJetThrough n g h p → E g p = E h p

def SmoothMetricResponseActive (E : MetricFieldResponse) : Prop :=
  ¬ ∃ c : ℝ, ∀ g p, SmoothLorentzOperand g p → E g p = c • g p

/-- Naturality under all smooth local changes of coordinates with an invertible
derivative. Both the metrics and the chart maps may be nonanalytic. -/
def SmoothMetricResponseNatural (E : MetricFieldResponse) : Prop :=
  ∀ (F : CoordinatePoint → CoordinatePoint) (p : CoordinatePoint)
    (B : CoordinatePoint ≃L[ℝ] CoordinatePoint),
    ContDiffAt ℝ ∞ F p → HasFDerivAt F B.toContinuousLinearMap p →
    ∀ g, SmoothLorentzOperand g (F p) →
      E (coordinateMetricPullback g F) p =
        (coordinateJacobian F p).transpose * E g (F p) * coordinateJacobian F p

theorem original_eh_natural_under_smooth_coordinates (κ Λ : ℝ) (hk : κ ≠ 0) :
    SmoothMetricResponseNatural (originalEHGeometricResponse κ Λ) := by
  intro F p B smoothF derivative g domain
  obtain ⟨D, frame⟩ := domain.2.2
  exact eh_original_geometric_tensor_natural κ Λ hk g domain.1 F p (smooth_operand_regular domain).2.1
    (native_lorentz_frame_determinant_negative g (F p) D frame)
    (smoothF.of_le (WithTop.coe_le_coe.mpr (le_top : (3 : ℕ∞) ≤ ⊤))) B derivative

private theorem einstein_natural_under_smooth_coordinates : SmoothMetricResponseNatural actualEinsteinResponse := by
  intro F p B smoothF derivative g domain
  obtain ⟨D, frame⟩ := domain.2.2
  have nd := lorentz_frame_metric_nondegenerate g (F p) D frame
  have reg := (smooth_operand_regular domain).2.1
  have chart := smoothF.of_le (WithTop.coe_le_coe.mpr (le_top : (3 : ℕ∞) ≤ ⊤))
  have ricci := coordinate_ricci_regular_natural g domain.1 F p reg nd chart B derivative
  have scalar := coordinate_scalar_regular_natural g domain.1 F p reg nd chart B derivative
  simp only [actualEinsteinResponse, coordinateScalarMetric, ricci, scalar,
    Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, coordinateMetricPullback_matrix]

private theorem flat_normalized : NormalizedSmoothMetricGerm flatMetricField := by
  rw [← hessianMetricPolynomial_flat]
  exact hessianMetricPolynomial_normalized 0

/-- A polynomial normal chart acts on a C∞ metric germ, including a
nonanalytic one. The C² normal-coordinate theorem gives the normalized
value and derivative; the explicit pullback preserves all smooth orders. -/
theorem smooth_normal_frame_operand (g : MetricField) (p : CoordinatePoint)
    (B : CoordinatePoint ≃L[ℝ] CoordinatePoint) (hg : SmoothLorentzOperand g p)
    (frame : LorentzFrameAt g p B) :
    SmoothLorentzOperand (pointNormalizedMetric g p B) 0 ∧
      C2NormalizedMetricGerm (pointNormalizedMetric g p B) := by
  have germ := c2_pointNormalizedMetric_germ g p B hg.1 (smooth_operand_regular hg).2.1 frame
  refine ⟨⟨germ.1, ?_, ContinuousLinearEquiv.refl ℝ CoordinatePoint,
    c2_normalizedMetric_identity_frame _ germ⟩, germ⟩
  intro a b
  rw [← pointNormalChartMap_pullback]
  let F := pointNormalChartMap g p B
  have hF : ContDiffAt ℝ ⊤ F 0 := (pointNormalChartMap_analytic g p B).contDiffAt
  have hG (i j : Fin 4) : ContDiffAt ℝ ∞ (fun x => g x i j) (F 0) := by
    simpa only [F, pointNormalChartMap_zero] using hg.2.1 i j
  unfold coordinateMetricPullback
  apply ContDiffAt.sum
  intro i _
  apply ContDiffAt.sum
  intro j _
  exact (((coordinateJacobian_contDiffAt F 0 hF i a).of_le le_top).mul
    ((hG i j).comp 0 (hF.of_le le_top))).mul ((coordinateJacobian_contDiffAt F 0 hF j b).of_le le_top)

private theorem flat_response_invariant (E : MetricFieldResponse) (hn : SmoothMetricResponseNatural E) :
    InvariantBaseline (E flatMetricField 0) := by
  intro L
  have pull : coordinateMetricPullback flatMetricField (lorentzCoordinateMap L) = flatMetricField := by
    funext x
    rw [coordinateMetricPullback_matrix, lorentzCoordinateMap_jacobian]
    exact L.metric_preserved
  have h := hn (lorentzCoordinateMap L) 0 (lorentzCoordinateEquiv L)
    ((lorentzCoordinateMap_smooth L).contDiffAt.of_le le_top) (lorentzCoordinateMap_hasFDerivAt L 0)
    flatMetricField (by simpa only [lorentzCoordinateMap_zero] using normalized_smooth_operand flat_normalized)
  simpa only [pull, lorentzCoordinateMap_zero, lorentzCoordinateMap_jacobian] using h.symm

/-- All smooth metric first jets are reduced to the identical normal first jet.
Naturality relates actual tensors at arbitrary points to that normalized value.
One universal constant works for all points and all metric operands. -/
theorem first_jet_natural_response_unique_baseline (E : MetricFieldResponse)
    (hn : SmoothMetricResponseNatural E) (local₁ : SmoothMetricResponseOrderAtMost E 1) :
    ∃! c : ℝ, ∀ g p, SmoothLorentzOperand g p → E g p = c • g p := by
  obtain ⟨c, flat, unique⟩ := invariant_baseline_unique_metric_multiple _ (flat_response_invariant E hn)
  refine ⟨c, ?_, ?_⟩
  · intro g p hg
    obtain ⟨B, frame⟩ := hg.2.2
    obtain ⟨normalized,norm⟩ := smooth_normal_frame_operand g p B hg frame
    have equal := local₁ _ _ 0 normalized (normalized_smooth_operand flat_normalized)
      ⟨norm.2.2.1, fun a b => (norm.2.2.2 a b).trans (flat_normalized.2.2.2 a b).symm⟩
    have transformed := hn (pointNormalChartMap g p B) 0 B ((pointNormalChartMap_analytic g p B).contDiffAt.of_le le_top)
      (pointNormalChartMap_hasFDerivAt g p B hg.1) g (by simpa only [pointNormalChartMap_zero] using hg)
    simp only [pointNormalChartMap_pullback, pointNormalChartMap_zero,
      pointNormalChartMap_jacobian g p B hg.1] at transformed
    apply frame_matrix_pullback_injective B
    change (coordinateFrameMatrix B).transpose * E g p * coordinateFrameMatrix B =
      (coordinateFrameMatrix B).transpose * (c • g p) * coordinateFrameMatrix B
    rw [← transformed, equal, flat, Matrix.mul_smul, Matrix.smul_mul, frame]
  · intro d hd
    exact unique d (hd _ 0 (normalized_smooth_operand flat_normalized))

theorem active_natural_response_order_lower_bound (E : MetricFieldResponse)
    (hn : SmoothMetricResponseNatural E) (ha : SmoothMetricResponseActive E)
    (n : ℕ) (order : SmoothMetricResponseOrderAtMost E n) : 2 ≤ n := by
  by_contra! small
  have one : SmoothMetricResponseOrderAtMost E 1 := by
    interval_cases n
    · exact fun g h p hg hh jet => order g h p hg hh jet.1
    · exact order
  exact ha (first_jet_natural_response_unique_baseline E hn one).exists

/-- A smooth active witness for a regular two-jet operator exists whenever
its activity was certified on the native C² envelope. Smooth polynomial germs
match every normalized two-jet. -/
theorem smooth_activity_of_regular_two_jet_activity (E : MetricFieldResponse)
    (hn : RegularLorentzResponseNatural E) (hl : RegularLorentzTwoJetLocal E)
    (active : FullLorentzEnvelopeResponseActive E) : SmoothMetricResponseActive E := by
  rintro ⟨c, pure⟩
  apply active
  refine ⟨c, ?_⟩
  intro g p B hs hr frame
  have germ := c2_pointNormalizedMetric_germ g p B hs hr frame
  have jet := c2_normalized_metric_matches_receiver _ germ
  let H := c2MetricHessian _ 0 germ.1 germ.2.1
  have equal := hl _ (hessianMetricPolynomial H) 0 (c2_normalized_is_lorentz _ germ)
    (hessian_receiver_is_c2_lorentz H) jet
  have polynomial := pure _ 0 (normalized_smooth_operand (hessianMetricPolynomial_normalized H))
  have transformed := hn (pointNormalChartMap g p B) 0 B (pointNormalChartMap_analytic g p B).contDiffAt
    (pointNormalChartMap_hasFDerivAt g p B hs) g
    (by simpa only [pointNormalChartMap_zero] using (show C2LorentzMetricAt g p from ⟨hs, hr, B, frame⟩))
  simp only [pointNormalChartMap_pullback, pointNormalChartMap_zero,
    pointNormalChartMap_jacobian g p B hs] at transformed
  apply frame_matrix_pullback_injective B
  change (coordinateFrameMatrix B).transpose * E g p * coordinateFrameMatrix B =
    (coordinateFrameMatrix B).transpose * (c • g p) * coordinateFrameMatrix B
  rw [← transformed, equal, polynomial, hessianMetricPolynomial_zero, Matrix.mul_smul, Matrix.smul_mul, frame]

private theorem regular_two_jet_on_smooth {E : MetricFieldResponse} (hl : RegularLorentzTwoJetLocal E) :
    SmoothMetricResponseOrderAtMost E 2 :=
  fun g h p hg hh jet => hl g h p (smooth_operand_regular hg) (smooth_operand_regular hh) jet.1

/-- The witness is the geometric response of the admitted Einstein-Hilbert
action, including its possible constant metric baseline. -/
theorem occupied_eh_least_intrinsic_order (κ Λ : ℝ) (hk : κ ≠ 0) :
    IsLeast {n : ℕ | SmoothMetricResponseOrderAtMost (originalEHGeometricResponse κ Λ) n} 2 := by
  let E := originalEHGeometricResponse κ Λ
  have hn := eh_original_geometric_response_regular_natural κ Λ hk
  have hl := eh_original_geometric_response_twojet_local κ Λ hk
  have active := smooth_activity_of_regular_two_jet_activity E hn hl (eh_original_geometric_full_envelope_active κ Λ hk)
  exact ⟨regular_two_jet_on_smooth hl, active_natural_response_order_lower_bound E
    (original_eh_natural_under_smooth_coordinates κ Λ hk) active⟩

/-- Across all finite candidate orders: all metrics are smooth locally at the
tested point, and naturality, symmetry, activity and conservation are imposed
without restricting n. The explicit Einstein tensor occupies order two. -/
theorem least_active_closed_metric_response_order :
    IsLeast {n : ℕ | ∃ E : MetricFieldResponse,
      SmoothMetricResponseNatural E ∧ SmoothMetricResponseActive E ∧
      (∀ g p, SmoothLorentzOperand g p → ∀ i j, E g p i j = E g p j i) ∧
      (∀ g, SmoothLorentzOperand g 0 → g 0 = metric →
        (∀ a b, fderiv ℝ (fun x => g x a b) 0 = 0) → coordinateDivergence g (E g) 0 = 0) ∧
      SmoothMetricResponseOrderAtMost E n} 2 := by
  constructor
  · refine ⟨actualEinsteinResponse, einstein_natural_under_smooth_coordinates,
      smooth_activity_of_regular_two_jet_activity _ actual_einstein_response_natural
        actual_einstein_response_twojet_local actual_einstein_full_envelope_active,
      fun g p hg => actual_einstein_response_symmetric g p (smooth_operand_regular hg), ?_,
      regular_two_jet_on_smooth actual_einstein_response_twojet_local⟩
    intro g hg value derivatives
    exact actual_einstein_general_bianchi_closure g
      ⟨hg.1, fun i j => (hg.2.1 i j).of_le (WithTop.coe_le_coe.mpr (le_top : (3 : ℕ∞) ≤ ⊤)),
        value, derivatives⟩
  · rintro n ⟨E, hn, ha, _, _, ho⟩
    exact active_natural_response_order_lower_bound E hn ha n ho

end
end AASCSemanticExhaustion
