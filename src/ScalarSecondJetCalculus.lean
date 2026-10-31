import GeneralMetricHessianField

namespace AASCSemanticExhaustion
noncomputable section
set_option maxHeartbeats 0

def scalarPartial (f : (Fin 4 → ℝ) → ℝ) (x : Fin 4 → ℝ) (c : Fin 4) : ℝ :=
  fderiv ℝ f x (Pi.single c 1)

def scalarSecondPartial (f : (Fin 4 → ℝ) → ℝ) (x : Fin 4 → ℝ) (c d : Fin 4) : ℝ :=
  scalarPartial (fun y => scalarPartial f y c) x d

theorem scalarPartial_mul (f h : (Fin 4 → ℝ) → ℝ)
    (hf : Differentiable ℝ f) (hh : Differentiable ℝ h) (x : Fin 4 → ℝ) (c : Fin 4) :
    scalarPartial (fun y => f y * h y) x c =
      f x * scalarPartial h x c + h x * scalarPartial f x c := by
  have hd := ((hf x).hasFDerivAt.mul (hh x).hasFDerivAt).fderiv
  change fderiv ℝ (fun y => f y * h y) x = _ at hd
  simp only [scalarPartial, hd, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul]

theorem scalarSecondPartial_mul (f h : (Fin 4 → ℝ) → ℝ)
    (hf : Differentiable ℝ f) (hh : Differentiable ℝ h)
    (c d : Fin 4)
    (hcF : DifferentiableAt ℝ (fun y => scalarPartial f y c) 0)
    (hcH : DifferentiableAt ℝ (fun y => scalarPartial h y c) 0) :
    scalarSecondPartial (fun y => f y * h y) 0 c d =
      f 0 * scalarSecondPartial h 0 c d + h 0 * scalarSecondPartial f 0 c d +
        scalarPartial f 0 c * scalarPartial h 0 d + scalarPartial h 0 c * scalarPartial f 0 d := by
  unfold scalarSecondPartial
  simp_rw [scalarPartial_mul f h hf hh]
  have hd := (((hf 0).hasFDerivAt.mul hcH.hasFDerivAt).add
    ((hh 0).hasFDerivAt.mul hcF.hasFDerivAt)).fderiv
  change fderiv ℝ (fun y => f y * scalarPartial h y c + h y * scalarPartial f y c) 0 = _ at hd
  simp only [scalarPartial] at hd
  unfold scalarPartial
  rw [hd]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

#print axioms scalarPartial_mul
#print axioms scalarSecondPartial_mul
end
end AASCSemanticExhaustion
