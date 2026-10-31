import ScalarSecondJetLinear
import ActualMetricHessian

namespace AASCSemanticExhaustion
noncomputable section
open scoped BigOperators
set_option maxHeartbeats 0

theorem smooth_scalarPartial_differentiableAt (f : CoordinatePoint → ℝ)
    (smooth : ContDiff ℝ ⊤ f) (p : CoordinatePoint) (c : Fin 4) :
    DifferentiableAt ℝ (fun x => scalarPartial f x c) p := by
  have hdf : DifferentiableAt ℝ (fderiv ℝ f) p :=
    (smooth.contDiffAt.fderiv_right (m := 1) (by simp)).differentiableAt (by simp)
  have hc : DifferentiableAt ℝ (fun _ : CoordinatePoint => (Pi.single c 1 : CoordinatePoint)) p :=
    differentiableAt_const _
  exact hdf.clm_apply hc

theorem smooth_scalarSecondPartial_mul (f h : CoordinatePoint → ℝ)
    (hf : ContDiff ℝ ⊤ f) (hh : ContDiff ℝ ⊤ h) (c d : Fin 4) :
    scalarSecondPartial (fun y => f y * h y) 0 c d =
      f 0 * scalarSecondPartial h 0 c d + h 0 * scalarSecondPartial f 0 c d +
        scalarPartial f 0 c * scalarPartial h 0 d + scalarPartial h 0 c * scalarPartial f 0 d :=
  scalarSecondPartial_mul f h (hf.differentiable (by simp)) (hh.differentiable (by simp)) c d
    (smooth_scalarPartial_differentiableAt f hf 0 c) (smooth_scalarPartial_differentiableAt h hh 0 c)

theorem smooth_scalarSecondPartial_sum {ι : Type*} [Fintype ι] (f : ι → CoordinatePoint → ℝ)
    (hf : ∀ i, ContDiff ℝ ⊤ (f i)) (c d : Fin 4) :
    scalarSecondPartial (fun y => ∑ i, f i y) 0 c d = ∑ i, scalarSecondPartial (f i) 0 c d :=
  scalarSecondPartial_sum f (fun i => (hf i).differentiable (by simp)) c d
    (fun i => smooth_scalarPartial_differentiableAt (f i) (hf i) 0 c)

theorem smooth_scalarPartial_zero_of_fderiv (f : CoordinatePoint → ℝ)
    (first : fderiv ℝ f 0 = 0) (c : Fin 4) : scalarPartial f 0 c = 0 := by
  simp [scalarPartial, first]

theorem smooth_scalarSecondPartial_triple_flat (f h k : CoordinatePoint → ℝ)
    (hf : ContDiff ℝ ⊤ f) (hh : ContDiff ℝ ⊤ h) (hk : ContDiff ℝ ⊤ k)
    (firstf : fderiv ℝ f 0 = 0) (firsth : fderiv ℝ h 0 = 0) (firstk : fderiv ℝ k 0 = 0)
    (c d : Fin 4) :
    scalarSecondPartial (fun x => f x * h x * k x) 0 c d =
      f 0 * h 0 * scalarSecondPartial k 0 c d +
        f 0 * k 0 * scalarSecondPartial h 0 c d + h 0 * k 0 * scalarSecondPartial f 0 c d := by
  rw [smooth_scalarSecondPartial_mul (fun x => f x * h x) k (hf.mul hh) hk c d,
    smooth_scalarSecondPartial_mul f h hf hh c d]
  simp only [scalarPartial_mul f h (hf.differentiable (by simp)) (hh.differentiable (by simp)),
    smooth_scalarPartial_zero_of_fderiv f firstf, smooth_scalarPartial_zero_of_fderiv h firsth,
    smooth_scalarPartial_zero_of_fderiv k firstk]
  ring

#print axioms smooth_scalarPartial_differentiableAt
#print axioms smooth_scalarSecondPartial_mul
#print axioms smooth_scalarSecondPartial_sum
#print axioms smooth_scalarPartial_zero_of_fderiv
#print axioms smooth_scalarSecondPartial_triple_flat
end
end AASCSemanticExhaustion
