import ScalarSecondJetCalculus
import CoordinateLeviCivita

namespace AASCSemanticExhaustion
noncomputable section
open scoped BigOperators
set_option maxHeartbeats 0

theorem scalarPartial_const_mul (r : ℝ) (f : CoordinatePoint → ℝ)
    (hf : Differentiable ℝ f) (x : CoordinatePoint) (c : Fin 4) :
    scalarPartial (fun y => r * f y) x c = r * scalarPartial f x c := by
  unfold scalarPartial
  rw [((hf x).hasFDerivAt.const_mul r).fderiv]
  simp

theorem scalarPartial_add (f h : CoordinatePoint → ℝ)
    (hf : Differentiable ℝ f) (hh : Differentiable ℝ h) (x : CoordinatePoint) (c : Fin 4) :
    scalarPartial (fun y => f y + h y) x c = scalarPartial f x c + scalarPartial h x c := by
  have hd := ((hf x).hasFDerivAt.add (hh x).hasFDerivAt).fderiv
  change fderiv ℝ (fun y => f y + h y) x = _ at hd
  simp only [scalarPartial, hd, ContinuousLinearMap.add_apply]

theorem scalarPartial_sum {ι : Type*} [Fintype ι] (f : ι → CoordinatePoint → ℝ)
    (hf : ∀ i, Differentiable ℝ (f i)) (x : CoordinatePoint) (c : Fin 4) :
    scalarPartial (fun y => ∑ i, f i y) x c = ∑ i, scalarPartial (f i) x c := by
  have hd := (HasFDerivAt.fun_sum (u := Finset.univ) (fun i _ => (hf i x).hasFDerivAt)).fderiv
  simp only [scalarPartial, hd, ContinuousLinearMap.sum_apply]

theorem scalarSecondPartial_const_mul (r : ℝ) (f : CoordinatePoint → ℝ)
    (hf : Differentiable ℝ f) (c d : Fin 4)
    (hcf : DifferentiableAt ℝ (fun y => scalarPartial f y c) 0) :
    scalarSecondPartial (fun y => r * f y) 0 c d = r * scalarSecondPartial f 0 c d := by
  unfold scalarSecondPartial
  simp_rw [scalarPartial_const_mul r f hf]
  have hd := (hcf.hasFDerivAt.const_mul r).fderiv
  simp only [scalarPartial] at hd
  unfold scalarPartial
  rw [hd]
  simp

theorem scalarSecondPartial_sum {ι : Type*} [Fintype ι] (f : ι → CoordinatePoint → ℝ)
    (hf : ∀ i, Differentiable ℝ (f i)) (c d : Fin 4)
    (hcf : ∀ i, DifferentiableAt ℝ (fun y => scalarPartial (f i) y c) 0) :
    scalarSecondPartial (fun y => ∑ i, f i y) 0 c d = ∑ i, scalarSecondPartial (f i) 0 c d := by
  unfold scalarSecondPartial
  simp_rw [scalarPartial_sum f hf]
  have hd := (HasFDerivAt.fun_sum (u := Finset.univ) (fun i _ => (hcf i).hasFDerivAt)).fderiv
  simp only [scalarPartial] at hd
  unfold scalarPartial
  rw [hd]
  simp only [ContinuousLinearMap.sum_apply]

#print axioms scalarPartial_const_mul
#print axioms scalarPartial_add
#print axioms scalarPartial_sum
#print axioms scalarSecondPartial_const_mul
#print axioms scalarSecondPartial_sum
end
end AASCSemanticExhaustion
