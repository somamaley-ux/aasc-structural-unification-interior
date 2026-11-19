import OriginalWardLocalization

/-! Recover the original-coordinate covariant derivative from the partial
derivative of the same tensor in the locally normalizing quadratic chart. -/
namespace AASCSemanticExhaustion
noncomputable section
open Filter
open scoped BigOperators Topology

theorem normal_chart_tensor_partial (g T : MetricField) (sg : MetricFieldSymmetric g)
    (hT : ∀ i j, ContDiffAt ℝ 2 (fun x => T x i j) 0) (a b c : Fin 4) :
    scalarPartial (fun x => coordinateMetricPullback T (normalizingCoordinateMap g) x a b) 0 c =
      coordinateCovariantTensorDerivative (leviCivitaCoefficients g) T 0 c a b := by
  rw [normalizingCoordinateMap, c2_quadratic_identity_metric_pullback_partial T hT _
    (normalCoordinateCorrection_symmetric g sg)]
  simp only [metricPartial, normalCoordinateCorrection, coordinateCovariantTensorDerivative,
    mul_neg, Finset.sum_neg_distrib]
  have replace (i : Fin 4) (a b : Fin 4) :
      leviCivitaCoefficients g 0 i a b = leviCivitaCoefficients g 0 i b a :=
    leviCivita_torsion_free g sg 0 i a b
  simp_rw [replace _ a c, replace _ b c, mul_comm (T 0 _ b), mul_comm (T 0 a _)]
  unfold scalarPartial
  ring

theorem normal_chart_original_divergence (g T : MetricField) (sg : MetricFieldSymmetric g)
    (hg : ∀ i j, ContDiffAt ℝ 2 (fun x => g x i j) 0) (value : g 0 = metric)
    (hT : ∀ i j, ContDiffAt ℝ 2 (fun x => T x i j) 0) :
    coordinateDivergence (coordinateMetricPullback g (normalizingCoordinateMap g))
        (coordinateMetricPullback T (normalizingCoordinateMap g)) 0 = coordinateDivergence g T 0 := by
  funext b
  rw [c2_normal_coordinateDivergence _ (c2_normalizing_metric_germ g sg hg value)]
  simp_rw [normal_chart_tensor_partial g T sg hT]
  unfold coordinateDivergence
  rw [value,canonical_metric_inverse]
  exact (canonical_metric_contraction_diagonal (fun a c =>
    coordinateCovariantTensorDerivative (leviCivitaCoefficients g) T 0 c a b)).symm

private theorem affine_partial_expansion (T : MetricField) (p : CoordinatePoint)
    (B : CoordinatePoint ≃L[ℝ] CoordinatePoint)
    (reg : ∀ i j, DifferentiableAt ℝ (fun x => T x i j) p) (a b c : Fin 4) :
    metricPartial (framedMetricField T p B) 0 a b c =
      ∑ i, ∑ j, coordinateFrameMatrix B i a * coordinateFrameMatrix B j b *
      ∑ k, coordinateFrameMatrix B k c * metricPartial T p i j k := by
  let F := affineCoordinateMap p B
  have hF : HasFDerivAt F B.toContinuousLinearMap 0 := quadraticCoordinateMap_hasFDerivAt_zero p B 0
  have hj (i j : Fin 4) : HasFDerivAt (fun x => T (F x) i j)
      ((fderiv ℝ (fun x => T x i j) p).comp B.toContinuousLinearMap) 0 := by
    have df : HasFDerivAt (fun x => T x i j) (fderiv ℝ (fun x => T x i j) p) (F 0) := by
      rw [show F 0 = p from affineCoordinateMap_zero _ _]
      exact (reg i j).hasFDerivAt
    exact df.comp 0 hF
  have hfield : (fun x => framedMetricField T p B x a b) =
      fun x => ∑ i, ∑ j, (coordinateFrameMatrix B i a * coordinateFrameMatrix B j b) * T (F x) i j := by
    funext x
    unfold framedMetricField coordinateMetricPullback
    simp only [affineCoordinateMap_jacobian]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  have h := HasFDerivAt.fun_sum (u := Finset.univ) (fun i _ =>
    HasFDerivAt.fun_sum (u := Finset.univ) (fun j _ =>
      (hj i j).const_mul (coordinateFrameMatrix B i a * coordinateFrameMatrix B j b)))
  unfold metricPartial
  rw [hfield,h.fderiv]
  simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply, smul_eq_mul,
    ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  exact continuousLinearMap_four_coordinates (fderiv ℝ (fun x => T x i j) p).toLinearMap (B (Pi.single c 1))

private theorem flat_first_christoffel (g : MetricField) (p : CoordinatePoint)
    (h : ∀ a b c, metricPartial g p a b c = 0) (e a b : Fin 4) :
    leviCivitaCoefficients g p e a b = 0 := by
  simp [leviCivitaCoefficients, lowerChristoffel,h]

private theorem flat_first_divergence (g T : MetricField) (p : CoordinatePoint)
    (h : ∀ a b c, metricPartial g p a b c = 0) (b : Fin 4) :
    coordinateDivergence g T p b = ∑ a, ∑ c, (g p)⁻¹ a c * metricPartial T p a b c := by
  simp [coordinateDivergence,coordinateCovariantTensorDerivative,flat_first_christoffel g p h,
    metricPartial,scalarPartial]

private theorem reorder_four_sums (f : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ) :
    (∑ a, ∑ i, ∑ j, ∑ k, f a i j k) = ∑ j, ∑ i, ∑ k, ∑ a, f a i j k := by
  calc
    _ = ∑ i, ∑ a, ∑ j, ∑ k, f a i j k := Finset.sum_comm
    _ = ∑ i, ∑ j, ∑ a, ∑ k, f a i j k := by
      apply Finset.sum_congr rfl
      intro i _
      exact Finset.sum_comm
    _ = ∑ j, ∑ i, ∑ a, ∑ k, f a i j k := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro i _
      exact Finset.sum_comm

private theorem lorentz_inverse_frame_components (g : MetricField) (p : CoordinatePoint)
    (B : CoordinatePoint ≃L[ℝ] CoordinatePoint) (frame : LorentzFrameAt g p B) (i k : Fin 4) :
    (∑ a, metric a a * coordinateFrameMatrix B i a * coordinateFrameMatrix B k a) = (g p)⁻¹ i k := by
  have h := inverse_frame_contraction_recovery (g p) (lorentz_frame_metric_nondegenerate g p B frame) B
  rw [frame,canonical_metric_inverse] at h
  have h' := congrArg (fun M : Tensor2 => M i k) h
  simp only [Matrix.mul_apply,Matrix.transpose_apply] at h'
  conv at h' => lhs; enter [2,a]; rw [Finset.sum_mul]
  rw [Finset.sum_comm] at h'
  rw [← h']
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_eq_single a]
  · ring
  · intro b _ hba
    simp [metric,Ne.symm hba]
  · simp

theorem flat_first_affine_divergence (g T : MetricField) (p : CoordinatePoint)
    (B : CoordinatePoint ≃L[ℝ] CoordinatePoint) (frame : LorentzFrameAt g p B)
    (rg : ∀ i j, DifferentiableAt ℝ (fun x => g x i j) p)
    (rT : ∀ i j, DifferentiableAt ℝ (fun x => T x i j) p)
    (h : ∀ a b c, metricPartial g p a b c = 0) (b : Fin 4) :
    coordinateDivergence (framedMetricField g p B) (framedMetricField T p B) 0 b =
      ∑ j, coordinateFrameMatrix B j b * coordinateDivergence g T p j := by
  have hF (a d c) : metricPartial (framedMetricField g p B) 0 a d c = 0 := by
    rw [affine_partial_expansion g p B rg]
    simp [h]
  rw [flat_first_divergence _ _ _ hF, framedMetricField_value g p B frame, canonical_metric_inverse,
    canonical_metric_contraction_diagonal]
  simp_rw [affine_partial_expansion T p B rT, flat_first_divergence g T p h, Finset.mul_sum]
  rw [reorder_four_sums]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro k _
  rw [← lorentz_inverse_frame_components g p B frame i k]
  simp only [Finset.sum_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  ring

private theorem translated_tensor_divergence (g T : MetricField) (p : CoordinatePoint)
    (rg : ∀ i j, ContDiffAt ℝ 2 (fun x => g x i j) p)
    (rT : ∀ i j, ContDiffAt ℝ 2 (fun x => T x i j) p) :
    coordinateDivergence (fun x => g (x+p)) (fun x => T (x+p)) 0 = coordinateDivergence g T p := by
  have deriv (S : MetricField) (hs : ∀ i j, ContDiffAt ℝ 2 (fun x => S x i j) p) (a b c : Fin 4) :
      metricPartial (fun x => S (x+p)) 0 a b c = metricPartial S p a b c := by
    exact congrArg (fun D : CoordinatePoint →L[ℝ] ℝ => D (Pi.single c 1))
      (c2_translated_scalar_first _ p (hs a b))
  have christ (i a b : Fin 4) : leviCivitaCoefficients (fun x => g (x+p)) 0 i a b =
      leviCivitaCoefficients g p i a b := by
    simp only [leviCivitaCoefficients, lowerChristoffel, deriv g rg, zero_add]
  funext b
  simp only [coordinateDivergence,coordinateCovariantTensorDerivative,zero_add,christ]
  simp only [show ∀ a b c : Fin 4, scalarPartial (fun x => T (x+p) a b) 0 c =
    scalarPartial (fun x => T x a b) p c from deriv T rT]

private theorem flatten_first_derivatives (g : MetricField) (sg : MetricFieldSymmetric g)
    (reg : ∀ a b, ContDiffAt ℝ 2 (fun x => g x a b) 0) (det : (g 0).det ≠ 0) (a b c : Fin 4) :
    metricPartial (coordinateMetricPullback g (normalizingCoordinateMap g)) 0 a b c = 0 := by
  change scalarPartial (fun x => coordinateMetricPullback g (normalizingCoordinateMap g) x a b) 0 c = 0
  exact (normal_chart_tensor_partial g g sg reg a b c).trans
    (coordinate_metric_covariant_derivative_zero g 0 sg det c a b)

private theorem tangent_identity_pull_value (g T : MetricField) (sg : MetricFieldSymmetric g) :
    coordinateMetricPullback T (normalizingCoordinateMap g) 0 = T 0 := by
  rw [coordinateMetricPullback_matrix,normalizingCoordinateMap]
  simp only [quadraticIdentityMap_jacobian_zero _ (normalCoordinateCorrection_symmetric g sg),
    quadraticIdentityMap_zero, Matrix.transpose_one,one_mul,mul_one]

private theorem flatten_tensor_divergence (g T : MetricField) (sg : MetricFieldSymmetric g)
    (reg : ∀ a b, ContDiffAt ℝ 2 (fun x => g x a b) 0) (det : (g 0).det ≠ 0)
    (rT : ∀ a b, ContDiffAt ℝ 2 (fun x => T x a b) 0) :
    coordinateDivergence (coordinateMetricPullback g (normalizingCoordinateMap g))
       (coordinateMetricPullback T (normalizingCoordinateMap g)) 0 = coordinateDivergence g T 0 := by
  funext b
  rw [flat_first_divergence _ _ _ (flatten_first_derivatives g sg reg det),tangent_identity_pull_value g g sg]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro c _
  congr 1
  exact normal_chart_tensor_partial g T sg rT a b c

/-- Pull a metric or tensor back by shifting the chosen point to the origin,
removing the first metric derivatives with an identity-Jacobian chart, and
then changing the linear frame. The three operations act on the same field. -/
def centeredNormalPullback (g : MetricField) (p : CoordinatePoint)
    (B : CoordinatePoint ≃L[ℝ] CoordinatePoint) (T : MetricField) : MetricField :=
  framedMetricField (coordinateMetricPullback (fun x => T (x+p))
    (normalizingCoordinateMap (fun x => g (x+p)))) 0 B

theorem centered_normal_divergence_transport (g T : MetricField) (p : CoordinatePoint)
    (B : CoordinatePoint ≃L[ℝ] CoordinatePoint) (sg : MetricFieldSymmetric g)
    (rg : ∀ i j, ContDiffAt ℝ 2 (fun x => g x i j) p)
    (rT : ∀ i j, ContDiffAt ℝ 2 (fun x => T x i j) p)
    (frame : LorentzFrameAt g p B) (b : Fin 4) :
    coordinateDivergence (centeredNormalPullback g p B g) (centeredNormalPullback g p B T) 0 b =
      ∑ j, coordinateFrameMatrix B j b * coordinateDivergence g T p j := by
  let gs : MetricField := fun x => g (x+p)
  let ts : MetricField := fun x => T (x+p)
  have sgs : MetricFieldSymmetric gs := fun x => sg (x+p)
  have orig : gs 0 = g p := by simp [gs]
  have rgs := c2_metric_translated_regular g p rg
  have rts := c2_metric_translated_regular T p rT
  have det : (gs 0).det ≠ 0 := orig ▸ lorentz_frame_metric_nondegenerate g p B frame
  let Q := normalizingCoordinateMap gs
  have upper (S : MetricField) (hS : ∀ i j, ContDiffAt ℝ 2 (fun x => S x i j) 0) :
      ∀ i j, DifferentiableAt ℝ (fun x => coordinateMetricPullback S Q x i j) 0 := by
    intro i j
    apply (c2_coordinateMetricPullback_contDiffAt S Q 0 (normalizingCoordinateMap_local_chart gs).1 _ i j).differentiableAt (by simp)
    simpa only [Q,normalizingCoordinateMap_zero] using hS
  have fr : LorentzFrameAt (coordinateMetricPullback gs Q) 0 B := by
    change (coordinateFrameMatrix B).transpose * coordinateMetricPullback gs Q 0 * _ = _
    rw [tangent_identity_pull_value gs gs sgs, orig]
    exact frame
  have transport := flat_first_affine_divergence (coordinateMetricPullback gs Q)
    (coordinateMetricPullback ts Q) 0 B fr (upper _ rgs) (upper _ rts)
    (flatten_first_derivatives gs sgs rgs det) b
  rw [flatten_tensor_divergence gs ts sgs rgs det rts,translated_tensor_divergence g T p rg rT] at transport
  exact transport

private theorem smooth_analytic_pull (g : MetricField) (hg : SmoothCoordinateMetric g)
    (F : CoordinatePoint → CoordinatePoint) (hf : ContDiff ℝ ⊤ F) :
    SmoothCoordinateMetric (coordinateMetricPullback g F) := by
  intro a b
  apply contDiff_iff_contDiffAt.mpr
  intro x
  unfold coordinateMetricPullback
  apply ContDiffAt.sum
  intro i _
  apply ContDiffAt.sum
  intro j _
  exact (((coordinateJacobian_contDiffAt F x hf.contDiffAt i a).of_le le_top).mul
    (((hg i j).contDiffAt).comp x (hf.of_le le_top).contDiffAt)).mul
      ((coordinateJacobian_contDiffAt F x hf.contDiffAt j b).of_le le_top)

private theorem shifted_metric_smooth (g : MetricField) (p : CoordinatePoint)
    (hg : SmoothCoordinateMetric g) : SmoothCoordinateMetric (fun x => g (x+p)) := by
  exact fun i j => (hg i j).comp (contDiff_id.add contDiff_const)

theorem centered_normal_pullback_metric_germ (g : MetricField) (p : CoordinatePoint)
    (B : CoordinatePoint ≃L[ℝ] CoordinatePoint) (sg : MetricFieldSymmetric g)
    (hg : SmoothCoordinateMetric g) (frame : LorentzFrameAt g p B) :
    SmoothCoordinateMetric (centeredNormalPullback g p B g) ∧
    C2NormalizedMetricGerm (centeredNormalPullback g p B g) := by
  let gs : MetricField := fun x => g (x+p)
  have sgs : MetricFieldSymmetric gs := fun x => sg (x+p)
  have orig : gs 0 = g p := by simp [gs]
  have reg : ∀ i j, ContDiffAt ℝ 2 (fun x => gs x i j) 0 := fun i j =>
    ((shifted_metric_smooth g p hg) i j).contDiffAt.of_le (by decide)
  have det : (gs 0).det ≠ 0 := orig ▸ lorentz_frame_metric_nondegenerate g p B frame
  let Q := normalizingCoordinateMap gs
  let gq := coordinateMetricPullback gs Q
  have sq : SmoothCoordinateMetric gq := smooth_analytic_pull _ (shifted_metric_smooth g p hg) _
    (normalizingCoordinateMap_smooth gs)
  have ss : SmoothCoordinateMetric (centeredNormalPullback g p B g) :=
    smooth_analytic_pull gq sq _ (affineCoordinateMap_smooth 0 B)
  have fr : LorentzFrameAt gq 0 B := by
    change (coordinateFrameMatrix B).transpose * coordinateMetricPullback gs Q 0 * _ = _
    rw [tangent_identity_pull_value gs gs sgs,orig]
    exact frame
  refine ⟨ss,framedMetricField_symmetric gq 0 B (coordinateMetricPullback_symmetric gs sgs Q),
    fun i j => (ss i j).contDiffAt.of_le (by decide),framedMetricField_value gq 0 B fr,?_⟩
  intro i j
  apply continuousLinearMap_zero_of_coordinate_basis
  intro c
  change metricPartial (framedMetricField gq 0 B) 0 i j c = 0
  rw [affine_partial_expansion gq 0 B (fun i j => (sq i j).differentiable (by decide) 0)]
  simp [gq, Q, flatten_first_derivatives gs sgs reg det]

theorem centered_normal_divergence_zero_iff (g T : MetricField) (p : CoordinatePoint)
    (B : CoordinatePoint ≃L[ℝ] CoordinatePoint) (sg : MetricFieldSymmetric g)
    (rg : ∀ i j, ContDiffAt ℝ 2 (fun x => g x i j) p)
    (rT : ∀ i j, ContDiffAt ℝ 2 (fun x => T x i j) p)
    (frame : LorentzFrameAt g p B) :
    coordinateDivergence (centeredNormalPullback g p B g) (centeredNormalPullback g p B T) 0 = 0 ↔
      coordinateDivergence g T p = 0 := by
  let D := coordinateDivergence g T p
  let A := coordinateFrameMatrix B
  have trans : coordinateDivergence (centeredNormalPullback g p B g) (centeredNormalPullback g p B T) 0 =
      A.transpose.mulVec D := funext (centered_normal_divergence_transport g T p B sg rg rT frame)
  rw [trans]
  constructor
  · intro h
    have recover : (coordinateFrameMatrix B.symm).transpose * A.transpose = 1 := by
      rw [← Matrix.transpose_mul,coordinateFrameMatrix_right_inverse,Matrix.transpose_one]
    have H := congrArg ((coordinateFrameMatrix B.symm).transpose.mulVec) h
    simpa only [Matrix.mulVec_mulVec,recover,Matrix.one_mulVec,Matrix.mulVec_zero] using H
  · intro h
    change A.transpose.mulVec (coordinateDivergence g T p) = 0
    rw [h,Matrix.mulVec_zero]

end
end AASCSemanticExhaustion

namespace AASCOccupiedProfiles
noncomputable section
open Filter AASCSemanticExhaustion TopologicalSpace AASCKleinGordon
open AASCMetricityOriginalAssembly AASCMetricityLicensingConstruction AASCKleinGordon.CanonicalLicensing
open scoped Topology

/-- Tensorial naturality is needed here only along the explicit composite
normal chart. It is an equality of response germs, with no divergence inputs. -/
def CovariantOnCenteredNormalCharts (E : MetricFieldResponse) : Prop :=
  ∀ (g : MetricField) (p : CoordinatePoint) (B : CoordinatePoint ≃L[ℝ] CoordinatePoint),
    MetricFieldSymmetric g → SmoothCoordinateMetric g → LorentzFrameAt g p B →
    E (centeredNormalPullback g p B g) =ᶠ[𝓝 0] centeredNormalPullback g p B (E g)

theorem original_lie_readings_close_in_original_coordinates (Ω : Opens CoordinatePoint)
    (origin : (0 : CoordinatePoint) ∈ Ω) (κ Λ : ℝ) (hk : κ ≠ 0) (E : MetricFieldResponse)
    (locality : SmoothMetricGermLocal E) (natural : CovariantOnCenteredNormalCharts E)
    (sm : ∀ H : AdmittedOperand Ω, SmoothCoordinateMetric (E (originalEHActMetric H.val)))
    (sy : ∀ H : AdmittedOperand Ω, MetricFieldSymmetric (E (originalEHActMetric H.val)))
    (reads : AllOriginalLieReadings Ω κ Λ E sm) (g : MetricField) (p : CoordinatePoint)
    (B : CoordinatePoint ≃L[ℝ] CoordinatePoint) (sg : MetricFieldSymmetric g)
    (hg : SmoothCoordinateMetric g) (frame : LorentzFrameAt g p B)
    (rE : ∀ i j, ContDiffAt ℝ 2 (fun x => E g x i j) p) :
    coordinateDivergence g (E g) p = 0 := by
  obtain ⟨smN,germ⟩ := centered_normal_pullback_metric_germ g p B sg hg frame
  have closed := original_lie_readings_close_normal_germ Ω origin κ Λ hk E locality sm sy reads _ smN germ
  apply (centered_normal_divergence_zero_iff g (E g) p B sg
    (fun i j => (hg i j).contDiffAt.of_le (by decide)) rE frame).mp
  exact (coordinate_divergence_of_equal_germs (Filter.EventuallyEq.rfl)
    (natural g p B sg hg frame)).symm.trans closed

end
end AASCOccupiedProfiles
