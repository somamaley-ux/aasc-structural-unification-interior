import NativeGradedDivergenceFirstCoefficient
import ScalarFieldSourceCalculus
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-! The actual massive scalar-clock Lagrangian of Module A 13.3/CSP-C 3,
computed to first metric order at a normalized Lorentz point. Inverse and volume
are explicit finite-algebra expressions. This is not yet the compact LF integral
or a proof of the full Standard Model action's analytic regularity. -/
namespace AASCSemanticExhaustion
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 4096
open scoped BigOperators

def nativeClockNormalMetric : Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.diagonal (fun i => if i=0 then -1 else 1)

def nativeClockMetricJet (H : Matrix (Fin 4) (Fin 4) ℝ) : Matrix (Fin 4) (Fin 4) (DualNumber ℝ) :=
  fun a b => ⟨nativeClockNormalMetric a b,H a b⟩

def nativeClockInverseJet (H : Matrix (Fin 4) (Fin 4) ℝ) : Matrix (Fin 4) (Fin 4) (DualNumber ℝ) :=
  fun a b => ⟨nativeClockNormalMetric a b,-(nativeClockNormalMetric*H*nativeClockNormalMetric) a b⟩

def nativeClockVolumeJet (H : Matrix (Fin 4) (Fin 4) ℝ) : DualNumber ℝ :=
  ⟨1,(-H 0 0+H 1 1+H 2 2+H 3 3)/2⟩

theorem native_clock_metric_determinant_body (H : Matrix (Fin 4) (Fin 4) ℝ) :
    (nativeClockMetricJet H).det.fst=-1 := by
  norm_num [Matrix.det_succ_row_zero,Matrix.det_fin_three,Matrix.det_fin_two,
    nativeClockMetricJet,nativeClockNormalMetric,Matrix.diagonal_apply,
    Matrix.submatrix_apply,Fin.sum_univ_four,Fin.sum_univ_three,Fin.sum_univ_two,
    TrivSqZeroExt.fst_sum] <;>
    (try simp only [Fin.ext_iff]) <;> norm_num [Fin.succAbove,Fin.succ] <;>
    norm_num [Fin.lt_def,Fin.castSucc]

theorem native_clock_metric_determinant_first_coefficient (H : Matrix (Fin 4) (Fin 4) ℝ) :
    (nativeClockMetricJet H).det.snd=H 0 0-H 1 1-H 2 2-H 3 3 := by
  norm_num [Matrix.det_succ_row_zero,Matrix.det_fin_three,Matrix.det_fin_two,
    nativeClockMetricJet,nativeClockNormalMetric,Matrix.diagonal_apply,
    Matrix.submatrix_apply,Fin.sum_univ_four,Fin.sum_univ_three,Fin.sum_univ_two,
    TrivSqZeroExt.fst_sum,TrivSqZeroExt.snd_sum,DualNumber.snd_mul] <;>
    (try simp only [Fin.ext_iff]) <;> norm_num [Fin.succAbove,Fin.succ] <;>
    norm_num [Fin.lt_def,Fin.castSucc]
  change -H 1 1+(-H 2 2+ -H 3 3)+H 0 0=H 0 0-H 1 1-H 2 2-H 3 3
  ring

theorem native_clock_volume_is_exact_square_root (H : Matrix (Fin 4) (Fin 4) ℝ) :
    nativeClockVolumeJet H*nativeClockVolumeJet H=-(nativeClockMetricJet H).det := by
  apply TrivSqZeroExt.ext
  · simp [nativeClockVolumeJet,native_clock_metric_determinant_body]
  · simp [nativeClockVolumeJet,DualNumber.snd_mul,native_clock_metric_determinant_first_coefficient]
    ring

theorem native_clock_volume_unique_body_one (H : Matrix (Fin 4) (Fin 4) ℝ)
    (v : DualNumber ℝ) (body : v.fst=1) (square : v*v=-(nativeClockMetricJet H).det) :
    v=nativeClockVolumeJet H := by
  apply TrivSqZeroExt.ext
  · exact body
  · have hs:=congrArg TrivSqZeroExt.snd square
    simp only [DualNumber.snd_mul,body,one_mul,mul_one,TrivSqZeroExt.snd_neg,
      native_clock_metric_determinant_first_coefficient] at hs
    change v.snd=(-H 0 0+H 1 1+H 2 2+H 3 3)/2
    linarith

theorem native_clock_metric_inverse_exact (H : Matrix (Fin 4) (Fin 4) ℝ) :
    nativeClockMetricJet H*nativeClockInverseJet H=1 ∧
      nativeClockInverseJet H*nativeClockMetricJet H=1 := by
  have hm : nativeClockNormalMetric*nativeClockNormalMetric=1 := by
    ext a b
    fin_cases a <;> fin_cases b <;>
      norm_num [nativeClockNormalMetric,Matrix.mul_apply,Matrix.diagonal_apply,Fin.sum_univ_four] <;>
        (try simp only [Fin.ext_iff]) <;> norm_num
  let ε : DualNumber ℝ:=TrivSqZeroExt.inr 1
  have hε : ε*ε=0:=TrivSqZeroExt.inr_mul_inr ℝ 1 1
  have hG : nativeClockMetricJet H=nativeBodyMatrixEmbed nativeClockNormalMetric+
      nativeExteriorCoefficientMatrix ε H := by
    funext a b
    apply TrivSqZeroExt.ext <;>
      simp [nativeClockMetricJet,nativeBodyMatrixEmbed,nativeExteriorCoefficientMatrix,ε,
        TrivSqZeroExt.algebraMap_eq_inl,DualNumber.snd_mul]
  have hB : nativeClockInverseJet H=nativeBodyMatrixEmbed nativeClockNormalMetric-
      nativeExteriorCoefficientMatrix ε (nativeClockNormalMetric*H*nativeClockNormalMetric) := by
    funext a b
    apply TrivSqZeroExt.ext <;>
      simp [nativeClockInverseJet,nativeBodyMatrixEmbed,nativeExteriorCoefficientMatrix,ε,
        TrivSqZeroExt.algebraMap_eq_inl,DualNumber.snd_mul]
  rw [hG,hB]
  exact native_exterior_metric_inverse_degree_two _ _ _ hm hm ε hε

def nativeClockLagrangianMetricJet (H : Matrix (Fin 4) (Fin 4) ℝ)
    (v : Fin 4 → ℝ) (φ μ : ℝ) : DualNumber ℝ :=
  TrivSqZeroExt.inl (-1/2:ℝ)*nativeClockVolumeJet H*
    ((∑ a, ∑ b, nativeClockInverseJet H a b*TrivSqZeroExt.inl (v a*v b))+
      TrivSqZeroExt.inl (μ*φ^2))

def nativeClockHilbertStress (v : Fin 4 → ℝ) (φ μ : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  fun a b => v a*v b-(1/2:ℝ)*nativeClockNormalMetric a b*
    ((∑ c, ∑ d, nativeClockNormalMetric c d*v c*v d)+μ*φ^2)

theorem native_clock_actual_metric_lagrangian_coefficient
    (H : Matrix (Fin 4) (Fin 4) ℝ) (v : Fin 4 → ℝ) (φ μ : ℝ) :
    (nativeClockLagrangianMetricJet H v φ μ).snd=
      (1/2:ℝ)*∑ a, ∑ b,
        (nativeClockNormalMetric*nativeClockHilbertStress v φ μ*nativeClockNormalMetric) a b*H a b := by
  norm_num [nativeClockLagrangianMetricJet,nativeClockVolumeJet,nativeClockInverseJet,
    nativeClockNormalMetric,nativeClockHilbertStress,Matrix.mul_apply,Matrix.diagonal_apply,
    Fin.sum_univ_four,TrivSqZeroExt.fst_sum,TrivSqZeroExt.snd_sum,DualNumber.snd_mul] <;>
    (try simp only [Fin.ext_iff]) <;> norm_num [Fin.succAbove,Fin.succ] <;>
    norm_num [Fin.lt_def,Fin.castSucc]
  ring

theorem native_clock_normal_metric_eq_canonical : nativeClockNormalMetric=metric := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    norm_num [nativeClockNormalMetric,metric,Matrix.diagonal_apply] <;>
      (try simp only [Fin.ext_iff]) <;> norm_num

theorem native_clock_computed_stress_is_actual_scalar_stress
    (g : MetricField) (φ : CoordinatePoint → ℝ) (p : CoordinatePoint) (μ : ℝ)
    (normal_value : g p=metric) :
    nativeClockHilbertStress (fun a => scalarPartial φ p a) (φ p) μ=scalarFieldStress g φ μ p := by
  ext a b
  simp only [nativeClockHilbertStress,scalarFieldStress,scalarFieldKinetic,
    native_clock_normal_metric_eq_canonical,normal_value,canonical_metric_inverse,pow_two]
  ring

#print axioms native_clock_metric_determinant_body
#print axioms native_clock_metric_determinant_first_coefficient
#print axioms native_clock_volume_is_exact_square_root
#print axioms native_clock_volume_unique_body_one
#print axioms native_clock_metric_inverse_exact
#print axioms native_clock_actual_metric_lagrangian_coefficient
#print axioms native_clock_normal_metric_eq_canonical
#print axioms native_clock_computed_stress_is_actual_scalar_stress
end
end AASCSemanticExhaustion
