import WickSchwartzSeminormBounds

noncomputable section
set_option maxHeartbeats 8000000
open TopologicalSpace
open AASCSemanticExhaustion
namespace AASCKleinGordon

lemma original_wick_native_response_entry_expansion (a : Parameters) (s : ℝ)
    (u v : FiniteParticleCore) (Ω : Opens (Fin 4 → ℝ)) (H : MetricSourceProbe Ω) :
    originalWickNativeMetricResponse a s u v Ω H=(1/2:ℂ)*∑ i,∑ j,
      ((wickFlatSign i:ℂ)*(wickFlatSign j:ℂ))*
        (originalWickScalarStressCandidateSesqForm a s i j u v) (nativeToWickMetricTest Ω H i j) := by
  rw [original_wick_native_metric_response_half_pairing]
  simp only [originalWickStressMetricDistribution,originalWickRaisedStressDistribution,
    ContinuousLinearMap.sum_apply,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.proj_apply,ContinuousLinearMap.smul_apply,smul_eq_mul]

lemma original_wick_native_response_add_left (a : Parameters) (s : ℝ)
    (u u' v : FiniteParticleCore) (Ω : Opens (Fin 4 → ℝ)) :
    originalWickNativeMetricResponse a s (u+u') v Ω=
      originalWickNativeMetricResponse a s u v Ω+originalWickNativeMetricResponse a s u' v Ω := by
  ext H
  simp only [ContinuousLinearMap.add_apply,original_wick_native_response_entry_expansion,
    map_add,LinearMap.add_apply,ContinuousLinearMap.add_apply,Finset.sum_add_distrib,mul_add]

lemma original_wick_native_response_add_right (a : Parameters) (s : ℝ)
    (u v v' : FiniteParticleCore) (Ω : Opens (Fin 4 → ℝ)) :
    originalWickNativeMetricResponse a s u (v+v') Ω=
      originalWickNativeMetricResponse a s u v Ω+originalWickNativeMetricResponse a s u v' Ω := by
  ext H
  simp only [ContinuousLinearMap.add_apply,original_wick_native_response_entry_expansion,
    map_add,LinearMap.add_apply,ContinuousLinearMap.add_apply,Finset.sum_add_distrib,mul_add]

lemma original_wick_native_response_smul_left (a : Parameters) (s : ℝ)
    (c : ℂ) (u v : FiniteParticleCore) (Ω : Opens (Fin 4 → ℝ)) :
    originalWickNativeMetricResponse a s (c • u) v Ω=
      star c • originalWickNativeMetricResponse a s u v Ω := by
  ext H
  simp only [ContinuousLinearMap.smul_apply,original_wick_native_response_entry_expansion,
    map_smulₛₗ,LinearMap.smul_apply,ContinuousLinearMap.smul_apply,
    smul_eq_mul,RingHom.id_apply,starRingEnd_apply]
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

lemma original_wick_native_response_smul_right (a : Parameters) (s : ℝ)
    (c : ℂ) (u v : FiniteParticleCore) (Ω : Opens (Fin 4 → ℝ)) :
    originalWickNativeMetricResponse a s u (c • v) Ω=
      c • originalWickNativeMetricResponse a s u v Ω := by
  ext H
  simp only [ContinuousLinearMap.smul_apply,original_wick_native_response_entry_expansion,
    map_smulₛₗ,LinearMap.smul_apply,ContinuousLinearMap.smul_apply,
    smul_eq_mul,RingHom.id_apply,starRingEnd_apply]
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

def originalWickNativeMetricSesq (a : Parameters) (s : ℝ) (Ω : Opens (Fin 4 → ℝ)) :
    FiniteParticleCore →ₗ⋆[ℂ] FiniteParticleCore →ₗ[ℂ] (MetricSourceProbe Ω →L[ℝ] ℂ) where
  toFun u :=
    { toFun := fun v => originalWickNativeMetricResponse a s u v Ω
      map_add' v w := original_wick_native_response_add_right a s u v w Ω
      map_smul' c v := by
        change originalWickNativeMetricResponse a s u (c • v) Ω=c • originalWickNativeMetricResponse a s u v Ω
        exact original_wick_native_response_smul_right a s c u v Ω }
  map_add' u w := by
    apply LinearMap.ext
    intro v
    exact original_wick_native_response_add_left a s u w v Ω
  map_smul' c u := by
    apply LinearMap.ext
    intro v
    change originalWickNativeMetricResponse a s (c • u) v Ω=
      star c • originalWickNativeMetricResponse a s u v Ω
    exact original_wick_native_response_smul_left a s c u v Ω

lemma original_wick_native_metric_sesq_apply (a : Parameters) (s : ℝ)
    (Ω : Opens (Fin 4 → ℝ)) (u v : FiniteParticleCore) :
    originalWickNativeMetricSesq a s Ω u v=originalWickNativeMetricResponse a s u v Ω := rfl

end AASCKleinGordon
