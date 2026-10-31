import WickKGOriginalActionProtocols
import WickKGOriginalActionReality
import KGDerivativeWickStateLaws
import KGOriginalLocalWickStateLaws

noncomputable section
set_option maxHeartbeats 1000000
open MeasureTheory Filter Set TopologicalSpace
open scoped Topology Matrix.Norms.Operator
open AASCSemanticExhaustion
namespace AASCKleinGordon

theorem wick_KG_original_act_C1 {Ω : Opens CoordinatePoint} (δ : WickKGFirstMetricAct Ω)
    (x : Spacetime) : ContDiffAt ℝ 1 (fun t => wickKGFirstMetricCurve δ t x) 0 := by
  have base : ContDiffAt ℝ 1 (fun _ : ℝ => wickFlatMetric) 0 := contDiffAt_const
  have h := base.add (δ.parameter_C1.smul
    (contDiffAt_const : ContDiffAt ℝ 1 (fun _ : ℝ => wickNativeMetricVariation δ.test x) 0))
  simpa only [wickKGFirstMetricCurve,wickOriginalFiniteMetric,wick_native_metric_variation_smul] using h

theorem wick_KG_original_act_support {Ω : Opens CoordinatePoint} (δ : WickKGFirstMetricAct Ω)
    (t : ℝ) (x : Spacetime) (outside : x∉tsupport (wickNativeMetricVariation δ.test)) :
    wickKGFirstMetricCurve δ t x=wickFlatMetric := by
  simp only [wickKGFirstMetricCurve,wickOriginalFiniteMetric,wick_native_metric_variation_smul,
    image_eq_zero_of_notMem_tsupport outside,smul_zero,add_zero]

theorem wick_KG_original_act_signature {Ω : Opens CoordinatePoint} (δ : WickKGFirstMetricAct Ω) :
    ∀ᶠ t in 𝓝 0,∀ x,WickLorentzSignature (wickKGFirstMetricCurve δ t x) ∧
      (wickKGFirstMetricCurve δ t x).det≠0 :=
  (wick_KG_original_act_admitted δ).mono (fun t ht x =>
    ⟨wick_original_metric_domain_fixed_signature Ω _ ht x,
      wick_original_metric_domain_nondegenerate Ω _ ht x⟩)

def wickKGComposeParameter {Ω : Opens CoordinatePoint} (δ : WickKGFirstMetricAct Ω)
    (β : ℝ → ℝ) (c : ℝ) (zero : β 0=0) (regular : ContDiffAt ℝ 1 β 0)
    (derivative : HasDerivAt β c 0) : WickKGFirstMetricAct Ω where
  test := δ.test
  parameter := δ.parameter ∘ β
  rate := δ.rate*c
  parameter_zero := by simp only [Function.comp_apply,zero,δ.parameter_zero]
  parameter_C1 := by
    have h : ContDiffAt ℝ 1 δ.parameter (β 0) := by rw [zero];exact δ.parameter_C1
    exact h.comp 0 regular
  derivative := by
    have h : HasDerivAt δ.parameter δ.rate (β 0) := by rw [zero];exact δ.derivative
    exact h.comp 0 derivative

theorem wick_KG_original_reparameterization_tangent {Ω : Opens CoordinatePoint}
    (δ : WickKGFirstMetricAct Ω) (β : ℝ → ℝ) (c : ℝ) (zero : β 0=0)
    (regular : ContDiffAt ℝ 1 β 0) (derivative : HasDerivAt β c 0) :
    wickKGFirstTangent (wickKGComposeParameter δ β c zero regular derivative)=
      c • wickKGFirstTangent δ := by
  simp only [wickKGFirstTangent,wickKGComposeParameter,smul_smul,mul_comm]

theorem wick_KG_original_reparameterization_output (a : Parameters) (s : ℝ) (u : FiniteParticleCore)
    {Ω : Opens CoordinatePoint} (δ : WickKGFirstMetricAct Ω) (β : ℝ → ℝ) (c : ℝ) (zero : β 0=0)
    (regular : ContDiffAt ℝ 1 β 0) (derivative : HasDerivAt β c 0) :
    wickKGFirstOutput a s u (wickKGComposeParameter δ β c zero regular derivative)=
      c*wickKGFirstOutput a s u δ := by
  simp only [wick_KG_original_first_output_computed,wick_KG_original_reparameterization_tangent,
    map_smul,smul_eq_mul]

theorem wick_KG_original_addition_witness (a : Parameters) (s : ℝ) (u : FiniteParticleCore)
    {Ω : Opens CoordinatePoint} (δ ε : WickKGFirstMetricAct Ω) :
    ∃ σ : WickKGFirstMetricAct Ω,
      wickKGFirstTangent σ=wickKGFirstTangent δ+wickKGFirstTangent ε ∧
      wickKGFirstOutput a s u σ=wickKGFirstOutput a s u δ+wickKGFirstOutput a s u ε := by
  refine ⟨wickKGIdentityAct (wickKGFirstTangent δ+wickKGFirstTangent ε),
    wick_KG_identity_tangent _,?_⟩
  simp only [wick_KG_original_first_output_computed,wick_KG_identity_tangent,map_add]

theorem wick_KG_original_scaling_witness (a : Parameters) (s : ℝ) (u : FiniteParticleCore)
    {Ω : Opens CoordinatePoint} (δ : WickKGFirstMetricAct Ω) (r : ℝ) :
    ∃ σ : WickKGFirstMetricAct Ω,wickKGFirstTangent σ=r • wickKGFirstTangent δ ∧
      wickKGFirstOutput a s u σ=r*wickKGFirstOutput a s u δ := by
  refine ⟨wickKGIdentityAct (r • wickKGFirstTangent δ),wick_KG_identity_tangent _,?_⟩
  simp only [wick_KG_original_first_output_computed,wick_KG_identity_tangent,map_smul,smul_eq_mul]

theorem wick_quantum_density_coefficient_scaling (G : NativeRealMatrix) (k : ℂ)
    (D : Fin 4 → Fin 4 → ℂ) (M : ℂ) :
    wickQuantumActionDensity G (fun i j => k*D i j) (k*M)=k*wickQuantumActionDensity G D M := by
  have sum : (∑ i,∑ j,(G⁻¹ i j : ℂ)*(k*D i j))=k*(∑ i,∑ j,(G⁻¹ i j : ℂ)*D i j) := by
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  unfold wickQuantumActionDensity
  rw [sum]
  ring

theorem wick_original_components_state_scaling (a : Parameters) (s : ℝ) (z : ℂ)
    (u v : FiniteParticleCore) (x : Spacetime) :
    originalWickDerivativeComponents a s (z • u) (z • v) x=
      fun i j => (star z*z)*originalWickDerivativeComponents a s u v x i j := by
  funext i j
  unfold originalWickDerivativeComponents originalDerivativeWickMatrix
  rw [originalDerivativeWickBilocalCore_smul_left,originalDerivativeWickBilocalCore_smul_right]
  ring

theorem wick_original_mass_square_state_scaling (a : Parameters) (s : ℝ) (z : ℂ)
    (u v : FiniteParticleCore) (x : Spacetime) :
    originalWickMassSquare a s (z • u) (z • v) x=(star z*z)*originalWickMassSquare a s u v x := by
  unfold originalWickMassSquare
  rw [originalWickSquareMatrix_smul_left,originalWickSquareMatrix_smul_right]
  ring

theorem wick_original_finite_action_state_scaling (a : Parameters) (s : ℝ) (z : ℂ)
    (u v : FiniteParticleCore) {Ω : Opens CoordinatePoint} (H : MetricSourceProbe Ω) :
    wickOriginalFiniteAction a s (z • u) (z • v) H=(star z*z)*wickOriginalFiniteAction a s u v H := by
  unfold wickOriginalFiniteAction
  simp_rw [wick_original_components_state_scaling,wick_original_mass_square_state_scaling,
    wick_quantum_density_coefficient_scaling,← mul_sub]
  exact integral_const_mul _ _

theorem wick_original_finite_action_unit_phase (a : Parameters) (s : ℝ) (z : ℂ) (unit : ‖z‖=1)
    (u v : FiniteParticleCore) {Ω : Opens CoordinatePoint} (H : MetricSourceProbe Ω) :
    wickOriginalFiniteAction a s (z • u) (z • v) H=wickOriginalFiniteAction a s u v H := by
  have phase : star z*z=1 := by
    have h : star z*z=((‖z‖^2 : ℝ) : ℂ) := by
      simpa only [mul_comm,← Complex.ofReal_pow] using Complex.mul_conj' z
    simpa only [unit,one_pow,Complex.ofReal_one] using h
  rw [wick_original_finite_action_state_scaling,phase,one_mul]

theorem wick_KG_original_first_output_unit_phase (a : Parameters) (s : ℝ) (z : ℂ) (unit : ‖z‖=1)
    (u : FiniteParticleCore) {Ω : Opens CoordinatePoint} (δ : WickKGFirstMetricAct Ω) :
    wickKGFirstOutput a s (z • u) δ=wickKGFirstOutput a s u δ := by
  unfold wickKGFirstOutput wickOriginalRealFiniteAction
  congr 1
  funext t
  exact congrArg Complex.re (wick_original_finite_action_unit_phase a s z unit u u _)

theorem wick_KG_original_all_readouts_unit_phase (a : Parameters) (s : ℝ) (z : ℂ) (unit : ‖z‖=1)
    (u : FiniteParticleCore) {Ω : Opens CoordinatePoint} (π : WickKGOriginalProtocol Ω) :
    wickKGOriginalOutput a s (z • u) π=wickKGOriginalOutput a s u π := by
  cases π with
  | first δ => exact congrArg WickKGOriginalReadout.first (wick_KG_original_first_output_unit_phase a s z unit u δ)
  | finite H =>
    by_cases inside : H∈wickOriginalMetricNeighborhood Ω
    · rw [wick_KG_original_finite_success a s (z • u) H inside,wick_KG_original_finite_success a s u H inside]
      apply congrArg WickKGOriginalReadout.finite
      exact congrArg Complex.re (wick_original_finite_action_unit_phase a s z unit u u H)
    · rw [wick_KG_original_finite_failure a s (z • u) H inside,wick_KG_original_finite_failure a s u H inside]

end AASCKleinGordon
