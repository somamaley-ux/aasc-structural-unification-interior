import NativeRealClockHilbertDerivative

namespace AASCSemanticExhaustion
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0
open scoped Topology BigOperators

def nativeRealClockMetricVariation (G H : NativeRealMatrix) (v : Fin 4 → ℝ) (φ μ : ℝ) : ℝ :=
  (1/2:ℝ)*nativeRealClockVolume G*Matrix.trace (G⁻¹*nativeRealClockStress G v φ μ*G⁻¹*H)

variable {X : Type*} [TopologicalSpace X] {x : X}

theorem native_clock_inverse_continuousAt (g : X → NativeRealMatrix)
    (hg : ContinuousAt g x) (hn : (g x).det≠0) : ContinuousAt (fun y => (g y)⁻¹) x := by
  exact (continuousAt_matrix_inv (g x)
    (differentiableAt_inverse (𝕜:=ℝ) (isUnit_iff_ne_zero.mpr hn)).continuousAt).comp hg

theorem native_clock_density_continuousAt (g : X → NativeRealMatrix) (v : X → Fin 4 → ℝ)
    (φ : X → ℝ) (μ : ℝ) (hg : ContinuousAt g x) (hv : ContinuousAt v x)
    (hφ : ContinuousAt φ x) (hn : (g x).det≠0) :
    ContinuousAt (fun y => nativeRealClockDensity (g y) (v y) (φ y) μ) x := by
  have hi:=native_clock_inverse_continuousAt g hg hn
  unfold nativeRealClockDensity nativeRealClockVolume
  apply ContinuousAt.mul
  · exact continuousAt_const.mul ((continuous_id.matrix_det.continuousAt).comp hg).abs.sqrt
  · apply ContinuousAt.add
    · apply tendsto_finset_sum
      intro a _
      apply tendsto_finset_sum
      intro b _
      exact (((continuous_apply b).continuousAt.comp ((continuous_apply a).continuousAt.comp hi)).mul
        ((continuous_apply a).continuousAt.comp hv)).mul ((continuous_apply b).continuousAt.comp hv)
    · exact continuousAt_const.mul (hφ.pow 2)

theorem native_clock_variation_continuousAt (g h : X → NativeRealMatrix) (v : X → Fin 4 → ℝ)
    (φ : X → ℝ) (μ : ℝ) (hg : ContinuousAt g x) (hh : ContinuousAt h x)
    (hv : ContinuousAt v x) (hφ : ContinuousAt φ x) (hn : (g x).det≠0) :
    ContinuousAt (fun y => nativeRealClockMetricVariation (g y) (h y) (v y) (φ y) μ) x := by
  have hi:=native_clock_inverse_continuousAt g hg hn
  have hq : ContinuousAt (fun y => nativeRealClockQuadratic (g y) (v y) (φ y) μ) x := by
    unfold nativeRealClockQuadratic
    apply ContinuousAt.add
    · apply tendsto_finset_sum
      intro a _
      apply tendsto_finset_sum
      intro b _
      exact (((continuous_apply b).continuousAt.comp ((continuous_apply a).continuousAt.comp hi)).mul
        ((continuous_apply a).continuousAt.comp hv)).mul ((continuous_apply b).continuousAt.comp hv)
    · exact continuousAt_const.mul (hφ.pow 2)
  have ho : ContinuousAt (fun y => nativeRealClockOuter (v y)) x := by
    apply continuousAt_pi.2
    intro a
    apply continuousAt_pi.2
    intro b
    exact ((continuous_apply a).continuousAt.comp hv).mul ((continuous_apply b).continuousAt.comp hv)
  have ht : ContinuousAt (fun y => nativeRealClockStress (g y) (v y) (φ y) μ) x :=
    ho.sub ((continuousAt_const.mul hq).smul hg)
  have hm:=((hi.mul ht).mul hi).mul hh
  have htrace : ContinuousAt (fun y => Matrix.trace ((g y)⁻¹*nativeRealClockStress (g y) (v y) (φ y) μ*(g y)⁻¹*h y)) x := by
    unfold Matrix.trace Matrix.diag
    apply tendsto_finset_sum
    intro a _
    exact (continuous_apply a).continuousAt.comp ((continuous_apply a).continuousAt.comp hm)
  exact (continuousAt_const.mul ((continuous_id.matrix_det.continuousAt).comp hg).abs.sqrt).mul htrace

theorem native_clock_density_path_derivative_at (G H : NativeRealMatrix)
    (v : Fin 4 → ℝ) (φ μ t : ℝ) (hn : (G+t • H).det≠0) :
    HasDerivAt (fun s : ℝ => nativeRealClockDensity (G+s • H) v φ μ)
      (nativeRealClockMetricVariation (G+t • H) H v φ μ) t := by
  have hd:=native_real_clock_hilbert_density_hasDerivAt (G+t • H) H hn v φ μ
  have hd' : HasDerivAt (fun s : ℝ => nativeRealClockDensity (G+t • H+s • H) v φ μ)
      (nativeRealClockMetricVariation (G+t • H) H v φ μ) (id t-t) := by
    simpa only [id_eq,sub_self] using hd
  have hh:=hd'.comp (h:=fun s:ℝ=>s-t) t ((hasDerivAt_id t).sub_const t)
  have heq : (fun s : ℝ => nativeRealClockDensity ((G+t • H)+(s-t) • H) v φ μ)=
      (fun s : ℝ => nativeRealClockDensity (G+s • H) v φ μ) := by
    funext s
    congr 1
    module
  simpa only [Function.comp_def,heq,one_mul,mul_one] using hh

#print axioms native_clock_inverse_continuousAt
#print axioms native_clock_density_continuousAt
#print axioms native_clock_variation_continuousAt
#print axioms native_clock_density_path_derivative_at
end
end AASCSemanticExhaustion
