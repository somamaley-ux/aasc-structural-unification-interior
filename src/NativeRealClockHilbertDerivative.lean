import NativeRealClockDensityDerivative

/-! The full ordinary real pointwise metric derivative produces the scalar
Hilbert tensor at arbitrary nondegenerate real metric values. No tensor or
conservation equation is a receiving premise. -/
namespace AASCSemanticExhaustion
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0
open scoped BigOperators

def nativeRealClockOuter (v : Fin 4 → ℝ) : NativeRealMatrix := fun a b => v a*v b

def nativeRealClockQuadratic (G : NativeRealMatrix) (v : Fin 4 → ℝ) (φ μ : ℝ) : ℝ :=
  (∑ a,∑ b,G⁻¹ a b*v a*v b)+μ*φ^2

def nativeRealClockStress (G : NativeRealMatrix) (v : Fin 4 → ℝ) (φ μ : ℝ) : NativeRealMatrix :=
  nativeRealClockOuter v-((1/2:ℝ)*nativeRealClockQuadratic G v φ μ) • G

theorem native_real_clock_kinetic_trace (B : NativeRealMatrix) (v : Fin 4 → ℝ) :
    Matrix.trace (B*nativeRealClockOuter v)=∑ a,∑ b,B a b*v a*v b := by
  unfold Matrix.trace Matrix.diag
  simp only [Matrix.mul_apply,nativeRealClockOuter]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

theorem native_real_clock_stress_trace_identity (G B H : NativeRealMatrix)
    (hBG : B*G=1) (hInv : G⁻¹=B) (v : Fin 4 → ℝ) (φ μ : ℝ) :
    Matrix.trace (B*nativeRealClockStress G v φ μ*B*H)=
      -(∑ a,∑ b,(-B*H*B) a b*v a*v b)-
      (1/2:ℝ)*Matrix.trace (B*H)*nativeRealClockQuadratic G v φ μ := by
  have hm : B*nativeRealClockStress G v φ μ*B*H=
      B*nativeRealClockOuter v*B*H-
        ((1/2:ℝ)*nativeRealClockQuadratic G v φ μ) • (B*H) := by
    unfold nativeRealClockStress
    rw [mul_sub,sub_mul,sub_mul,Matrix.mul_smul,Matrix.smul_mul,Matrix.smul_mul,
      hBG,one_mul]
  rw [hm,Matrix.trace_sub,Matrix.trace_smul,← native_real_clock_kinetic_trace]
  have ht : Matrix.trace ((-B*H*B)*nativeRealClockOuter v)=
      -Matrix.trace (B*nativeRealClockOuter v*B*H) := by
    rw [neg_mul,neg_mul,neg_mul,Matrix.trace_neg]
    congr 1
    simpa only [Matrix.mul_assoc] using Matrix.trace_mul_comm (B*H) (B*nativeRealClockOuter v)
  rw [ht]
  simp only [smul_eq_mul]
  ring

theorem native_real_clock_hilbert_density_hasDerivAt (G H : NativeRealMatrix)
    (nondegenerate : G.det≠0) (v : Fin 4 → ℝ) (φ μ : ℝ) :
    HasDerivAt (fun s : ℝ => nativeRealClockDensity (G+s • H) v φ μ)
      ((1/2:ℝ)*nativeRealClockVolume G*
        Matrix.trace (G⁻¹*nativeRealClockStress G v φ μ*G⁻¹*H)) 0 := by
  have hGB:=G.mul_nonsing_inv (isUnit_iff_ne_zero.mpr nondegenerate)
  have hBG:=G.nonsing_inv_mul (isUnit_iff_ne_zero.mpr nondegenerate)
  have hd:=native_real_clock_density_path_hasDerivAt G G⁻¹ H hGB hBG nondegenerate v φ μ
  have ht:=native_real_clock_stress_trace_identity G G⁻¹ H hBG rfl v φ μ
  rw [ht]
  convert hd using 1 <;> dsimp [nativeRealClockQuadratic] <;> ring

theorem native_real_clock_stress_is_actual_scalar_stress
    (g : MetricField) (φ : CoordinatePoint → ℝ) (p : CoordinatePoint) (μ : ℝ) :
    nativeRealClockStress (g p) (fun a => scalarPartial φ p a) (φ p) μ=scalarFieldStress g φ μ p := by
  ext a b
  simp only [nativeRealClockStress,nativeRealClockOuter,nativeRealClockQuadratic,
    scalarFieldStress,scalarFieldKinetic,Matrix.sub_apply,Matrix.smul_apply,smul_eq_mul,pow_two]
  ring

#print axioms native_real_clock_kinetic_trace
#print axioms native_real_clock_stress_trace_identity
#print axioms native_real_clock_hilbert_density_hasDerivAt
#print axioms native_real_clock_stress_is_actual_scalar_stress
end
end AASCSemanticExhaustion
