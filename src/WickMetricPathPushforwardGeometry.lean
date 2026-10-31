import WickMetricPathSourceIdentification

/-! Geometric pushforward of the entire compact C1 analytic path receiver.
All fields are derived from affine transport and tensor congruence. No
response/source/covariance identity is part of the input path. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
open Set Filter TopologicalSpace
open scoped Topology Matrix.Norms.Operator
open AASCSemanticExhaustion
namespace AASCKleinGordon

def wickPathAffineHomeomorph (b : Spacetime) (L : ProperLorentzTransform) :
    Spacetime ≃ₜ Spacetime where
  toEquiv :=
    { toFun x := b+spacetimeLorentzCLE L x
      invFun y := (spacetimeLorentzCLE L).symm (y-b)
      left_inv x := by simp
      right_inv y := by simp }
  continuous_toFun := continuous_const.add (spacetimeLorentzCLE L).continuous
  continuous_invFun := (spacetimeLorentzCLE L).symm.continuous.comp
    (continuous_id.sub continuous_const)

def wickPathMatrixCongruence (L : ProperLorentzTransform) :
    NativeRealMatrix →L[ℝ] NativeRealMatrix :=
  ({ toFun G := (wickLorentzMatrix L⁻¹).transpose*G*wickLorentzMatrix L⁻¹
     map_add' G H := by rw [Matrix.mul_add,Matrix.add_mul]
     map_smul' r G := by rw [Matrix.mul_smul,Matrix.smul_mul];rfl } :
    NativeRealMatrix →ₗ[ℝ] NativeRealMatrix).toContinuousLinearMap

theorem wick_path_congruence_flat (L : ProperLorentzTransform) :
    wickPathMatrixCongruence L wickFlatMetric = wickFlatMetric :=
  wick_lorentz_flat_metric L⁻¹

def wickPathCompactPushforward (b : Spacetime) (L : ProperLorentzTransform)
    (K : Compacts Spacetime) : Compacts Spacetime :=
  ⟨wickPathAffineHomeomorph b L '' (K : Set Spacetime),
    K.isCompact.image (wickPathAffineHomeomorph b L).continuous⟩

def wickPathCompactInverse (b : Spacetime) (L : ProperLorentzTransform)
    (K : Compacts Spacetime) (y : wickPathCompactPushforward b L K) : K :=
  ⟨(wickPathAffineHomeomorph b L).symm y.val,by
    rcases y.property with ⟨x,hx,hxy⟩
    rw [← hxy,Homeomorph.symm_apply_apply]
    exact hx⟩

theorem wick_path_compact_inverse_continuous (b : Spacetime) (L : ProperLorentzTransform)
    (K : Compacts Spacetime) : Continuous (wickPathCompactInverse b L K) :=
  ((wickPathAffineHomeomorph b L).symm.continuous.comp continuous_subtype_val).subtype_mk _

def wickPathCompactParameterMap (b : Spacetime) (L : ProperLorentzTransform)
    (K : Compacts Spacetime) (z : ℝ × wickPathCompactPushforward b L K) : ℝ × K :=
  (z.1,wickPathCompactInverse b L K z.2)

theorem wick_path_compact_parameter_continuous (b : Spacetime) (L : ProperLorentzTransform)
    (K : Compacts Spacetime) : Continuous (wickPathCompactParameterMap b L K) :=
  continuous_fst.prodMk ((wick_path_compact_inverse_continuous b L K).comp continuous_snd)

def wickCompactCurvePoincare (b : Spacetime) (L : ProperLorentzTransform)
    {Ω : Opens CoordinatePoint} (π : WickCompactC1MetricCurve Ω) :
    WickCompactC1MetricCurve (wickAffineMetricRegion b L Ω) where
  tangentTest := wickNativeAffineMetricTest b L π.tangentTest
  curve t y := wickPathMatrixCongruence L (π.curve t ((wickPathAffineHomeomorph b L).symm y))
  velocity t y := wickPathMatrixCongruence L (π.velocity t ((wickPathAffineHomeomorph b L).symm y))
  compact := wickPathCompactPushforward b L π.compact
  parameter := π.parameter
  parameterOpen := π.parameterOpen
  parameterZero := π.parameterZero
  continuousCurve := by
    have composed := π.continuousCurve.comp
      (wick_path_compact_parameter_continuous b L π.compact).continuousOn
      (show MapsTo (wickPathCompactParameterMap b L π.compact)
        (π.parameter ×ˢ univ) (π.parameter ×ˢ univ) from fun _ hz => ⟨hz.1,mem_univ _⟩)
    exact (wickPathMatrixCongruence L).continuous.comp_continuousOn composed
  continuousVelocity := by
    have composed := π.continuousVelocity.comp
      (wick_path_compact_parameter_continuous b L π.compact).continuousOn
      (show MapsTo (wickPathCompactParameterMap b L π.compact)
        (π.parameter ×ˢ univ) (π.parameter ×ˢ univ) from fun _ hz => ⟨hz.1,mem_univ _⟩)
    exact (wickPathMatrixCongruence L).continuous.comp_continuousOn composed
  derivative t ht y := (wickPathMatrixCongruence L).hasFDerivAt.comp_hasDerivAt t
    (π.derivative t ht ((wickPathAffineHomeomorph b L).symm y))
  base y := by rw [π.base,wick_path_congruence_flat]
  tangent y := by
    rw [π.tangent]
    have h := wick_native_affine_variation b L π.tangentTest
      ((wickPathAffineHomeomorph b L).symm y)
    change wickPathMatrixCongruence L _ = _
    have recover : b+spacetimeLorentzCLE L ((wickPathAffineHomeomorph b L).symm y)=y :=
      (wickPathAffineHomeomorph b L).apply_symm_apply y
    rw [recover] at h
    exact h.symm
  support := by
    filter_upwards [π.support] with t ht
    intro y hy
    have outside : (wickPathAffineHomeomorph b L).symm y ∉ π.compact := by
      intro hin
      exact hy ⟨(wickPathAffineHomeomorph b L).symm y,hin,
        (wickPathAffineHomeomorph b L).apply_symm_apply y⟩
    rw [ht _ outside,wick_path_congruence_flat]

theorem wick_compact_curve_poincare_tangent (b : Spacetime) (L : ProperLorentzTransform)
    {Ω : Opens CoordinatePoint} (π : WickCompactC1MetricCurve Ω) :
    (wickCompactCurvePoincare b L π).tangentTest =
      wickNativeAffineMetricTest b L π.tangentTest := rfl

theorem wick_compact_curve_poincare_value (b : Spacetime) (L : ProperLorentzTransform)
    {Ω : Opens CoordinatePoint} (π : WickCompactC1MetricCurve Ω) (t : ℝ) (x : Spacetime) :
    (wickCompactCurvePoincare b L π).curve t (b+spacetimeLorentzCLE L x) =
      wickPathMatrixCongruence L (π.curve t x) := by
  change wickPathMatrixCongruence L
    (π.curve t ((wickPathAffineHomeomorph b L).symm ((wickPathAffineHomeomorph b L) x))) = _
  rw [Homeomorph.symm_apply_apply]

end AASCKleinGordon
