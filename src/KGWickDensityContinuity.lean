import KGWickMetricDensity

noncomputable section
set_option maxHeartbeats 4000000
open scoped BigOperators Topology
open AASCSemanticExhaustion
namespace AASCKleinGordon
variable {X : Type*} [TopologicalSpace X] {x : X}

theorem wick_quantum_quadratic_continuousAt (g : X → NativeRealMatrix)
    (D : X → Fin 4 → Fin 4 → ℂ) (M : X → ℂ)
    (hg : ContinuousAt g x) (hD : ContinuousAt D x) (hM : ContinuousAt M x)
    (hn : (g x).det ≠ 0) :
    ContinuousAt (fun y => (∑ i,∑ j,((g y)⁻¹ i j : ℂ)*D y i j)+M y) x := by
  have hi := native_clock_inverse_continuousAt g hg hn
  apply ContinuousAt.add
  · apply tendsto_finset_sum
    intro i _
    apply tendsto_finset_sum
    intro j _
    exact (Complex.continuous_ofReal.continuousAt.comp
      ((continuous_apply j).continuousAt.comp ((continuous_apply i).continuousAt.comp hi))).mul
      ((continuous_apply j).continuousAt.comp ((continuous_apply i).continuousAt.comp hD))
  · exact hM

theorem wick_quantum_density_continuousAt (g : X → NativeRealMatrix)
    (D : X → Fin 4 → Fin 4 → ℂ) (M : X → ℂ)
    (hg : ContinuousAt g x) (hD : ContinuousAt D x) (hM : ContinuousAt M x)
    (hn : (g x).det ≠ 0) :
    ContinuousAt (fun y => wickQuantumActionDensity (g y) (D y) (M y)) x := by
  have hv : ContinuousAt (fun y => (nativeRealClockVolume (g y) : ℂ)) x :=
    Complex.continuous_ofReal.continuousAt.comp
      (((continuous_id.matrix_det.continuousAt).comp hg).abs.sqrt)
  exact (continuousAt_const.mul hv).mul (wick_quantum_quadratic_continuousAt g D M hg hD hM hn)

theorem wick_quantum_variation_continuousAt (g h : X → NativeRealMatrix)
    (D : X → Fin 4 → Fin 4 → ℂ) (M : X → ℂ)
    (hg : ContinuousAt g x) (hh : ContinuousAt h x)
    (hD : ContinuousAt D x) (hM : ContinuousAt M x) (hn : (g x).det ≠ 0) :
    ContinuousAt (fun y => wickQuantumDensityVariation (g y) (h y) (D y) (M y)) x := by
  have hi := native_clock_inverse_continuousAt g hg hn
  have hv : ContinuousAt (fun y => (nativeRealClockVolume (g y) : ℂ)) x :=
    Complex.continuous_ofReal.continuousAt.comp
      (((continuous_id.matrix_det.continuousAt).comp hg).abs.sqrt)
  have htrace : ContinuousAt (fun y => ((Matrix.trace ((g y)⁻¹*h y) : ℝ) : ℂ)) x := by
    apply Complex.continuous_ofReal.continuousAt.comp
    unfold Matrix.trace Matrix.diag
    apply tendsto_finset_sum
    intro i _
    exact (continuous_apply i).continuousAt.comp ((continuous_apply i).continuousAt.comp (hi.mul hh))
  have hC := ((hi.neg.mul hh).mul hi)
  have hs : ContinuousAt (fun y => ∑ i,∑ j,
      ((-(g y)⁻¹*h y*(g y)⁻¹) i j : ℂ)*D y i j) x := by
    apply tendsto_finset_sum
    intro i _
    apply tendsto_finset_sum
    intro j _
    exact (Complex.continuous_ofReal.continuousAt.comp
      ((continuous_apply j).continuousAt.comp ((continuous_apply i).continuousAt.comp hC))).mul
      ((continuous_apply j).continuousAt.comp ((continuous_apply i).continuousAt.comp hD))
  exact (continuousAt_const.mul hv).mul
    (((htrace.div_const 2).mul (wick_quantum_quadratic_continuousAt g D M hg hD hM hn)).add hs)

end AASCKleinGordon
