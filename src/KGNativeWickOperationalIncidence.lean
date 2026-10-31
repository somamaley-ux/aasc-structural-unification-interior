import KGNativeWickRaySource

/-! Operational attachment for the declared family of actual straight compact
metric variations. The output is the derivative of the original quantum
relative action. No arbitrary-curve completeness or graph-topology certificate
is asserted by this bounded protocol family. -/
noncomputable section
set_option maxHeartbeats 8000000
open TopologicalSpace
open scoped Matrix.Norms.Operator
open AASCSemanticExhaustion
namespace AASCKleinGordon

theorem native_to_wick_metric_test_injective (Ω : Opens (Fin 4 → ℝ)) :
    Function.Injective (nativeToWickMetricTest Ω) := by
  intro H K h
  apply TestFunction.ext
  intro p
  have hm : tensorEncode (H p)=tensorEncode (K p) := by
    funext i j
    have hh := congrArg (fun k : WickSchwartzMetricTest => k i j (wickSpacetimeCoordinates.symm p)) h
    simp only [native_to_wick_metric_test_apply,ContinuousLinearEquiv.apply_symm_apply] at hh
    exact_mod_cast hh
  have hd := congrArg tensorDecode hm
  simpa only [tensor_decode_encode] using hd

def originalWickStraightMetricOutput (a : Parameters) (s : ℝ) (u : FiniteParticleCore)
    {Ω : Opens (Fin 4 → ℝ)} (H : MetricSourceProbe Ω) : ℝ :=
  (originalWickMetricActionResponse a s u u (wickNativeMetricVariation H)).re

theorem original_wick_straight_output_is_actual_response (a : Parameters) (s : ℝ)
    (u : FiniteParticleCore) (Ω : Opens (Fin 4 → ℝ)) (H : MetricSourceProbe Ω) :
    originalWickStraightMetricOutput a s u H=originalWickNativeRealMetricResponse a s u Ω H :=
  (original_wick_native_real_response_actual_action a s u Ω H).symm

def originalWickNativeLinearMetricIncidence (a : Parameters) (s : ℝ) (u : FiniteParticleCore)
    (Ω : Opens (Fin 4 → ℝ)) : OperationalMetricIncidence Ω (MetricSourceProbe Ω) where
  incident H π := π=H
  output := originalWickStraightMetricOutput a s u
  total H := ⟨H,rfl⟩
  coherent H π ρ hπ hρ := by subst π;subst ρ;rfl
  add_compatible H K π ρ hπ hρ := by
    subst π;subst ρ
    refine ⟨H+K,rfl,?_⟩
    simp only [original_wick_straight_output_is_actual_response,map_add]
  smul_compatible r H π hπ := by
    subst π
    refine ⟨r • H,rfl,?_⟩
    simp only [original_wick_straight_output_is_actual_response,map_smul,smul_eq_mul]

theorem original_wick_operational_response_is_actual_response (a : Parameters) (s : ℝ)
    (u : FiniteParticleCore) (Ω : Opens (Fin 4 → ℝ)) (H : MetricSourceProbe Ω) :
    operationalMetricResponse (originalWickNativeLinearMetricIncidence a s u Ω) H=
      originalWickNativeRealMetricResponse a s u Ω H := by
  rw [operational_response_of_incident _ H H rfl]
  exact original_wick_straight_output_is_actual_response a s u Ω H

theorem original_wick_operational_response_compact_continuous (a : Parameters) (s : ℝ)
    (u : FiniteParticleCore) (Ω : Opens (Fin 4 → ℝ))
    (K : Compacts (Fin 4 → ℝ)) (hK : (K : Set (Fin 4 → ℝ)) ⊆ Ω) :
    Continuous (operationalMetricResponse (originalWickNativeLinearMetricIncidence a s u Ω) ∘
      TestFunction.ofSupportedIn hK) := by
  have heq : operationalMetricResponse (originalWickNativeLinearMetricIncidence a s u Ω)=
      originalWickNativeRealMetricResponse a s u Ω :=
    funext (original_wick_operational_response_is_actual_response a s u Ω)
  rw [heq]
  exact (originalWickNativeRealMetricResponse a s u Ω).continuous.comp (TestFunction.continuous_ofSupportedIn hK)

theorem original_wick_operational_functional_is_actual_response (a : Parameters) (s : ℝ)
    (u : FiniteParticleCore) (Ω : Opens (Fin 4 → ℝ)) :
    operationalMetricFunctional (originalWickNativeLinearMetricIncidence a s u Ω)
      (original_wick_operational_response_compact_continuous a s u Ω)=
      originalWickNativeRealMetricResponse a s u Ω := by
  ext H
  exact original_wick_operational_response_is_actual_response a s u Ω H

end AASCKleinGordon
