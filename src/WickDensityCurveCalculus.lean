import KGWickCompactAction

/-! The SAME finite-dimensional quantum density is Frechet differentiable on
the actual nonsingular matrix domain. Straight derivatives identify its actual
Frechet derivative; the chain rule then handles arbitrary differentiable curves.
No curve/stress derivative or Hadamard bridge is an input. -/
noncomputable section
set_option maxHeartbeats 4000000
open scoped BigOperators Topology Matrix.Norms.Operator
open AASCSemanticExhaustion
namespace AASCKleinGordon

theorem wick_matrix_determinant_differentiableAt (G : NativeRealMatrix) :
    DifferentiableAt ℝ (fun A : NativeRealMatrix => A.det) G := by
  simp only [Matrix.det_apply']
  apply DifferentiableAt.fun_sum
  intro σ _
  apply DifferentiableAt.mul (differentiableAt_const _)
  exact (HasFDerivAt.finset_prod (fun i (_ : i ∈ (Finset.univ : Finset (Fin 4))) =>
    (nativeRealMatrixEntry (σ i) i).hasFDerivAt)).differentiableAt

theorem wick_matrix_inverse_differentiableAt (G : NativeRealMatrix) (hn : G.det ≠ 0) :
    DifferentiableAt ℝ (fun A : NativeRealMatrix => A⁻¹) G := by
  let u : NativeRealMatrixˣ := ⟨G,G⁻¹,Matrix.mul_nonsing_inv G (isUnit_iff_ne_zero.mpr hn),
    Matrix.nonsing_inv_mul G (isUnit_iff_ne_zero.mpr hn)⟩
  have h : DifferentiableAt ℝ Ring.inverse G :=
    (hasFDerivAt_ringInverse (𝕜 := ℝ) u).differentiableAt
  convert h using 1
  funext A
  exact Matrix.nonsing_inv_eq_ringInverse A

theorem wick_quantum_density_differentiableAt (G : NativeRealMatrix) (hn : G.det ≠ 0)
    (D : Fin 4 → Fin 4 → ℂ) (M : ℂ) :
    DifferentiableAt ℝ (fun A => wickQuantumActionDensity A D M) G := by
  have hd := wick_matrix_determinant_differentiableAt G
  have hv : DifferentiableAt ℝ (fun A : NativeRealMatrix => nativeRealClockVolume A) G :=
    (hd.abs hn).sqrt (abs_ne_zero.mpr hn)
  have hi := wick_matrix_inverse_differentiableAt G hn
  have hk : DifferentiableAt ℝ
      (fun A : NativeRealMatrix => (∑ i,∑ j,(A⁻¹ i j : ℂ)*D i j)+M) G := by
    apply DifferentiableAt.add _ (differentiableAt_const _)
    apply DifferentiableAt.fun_sum
    intro i _
    apply DifferentiableAt.fun_sum
    intro j _
    exact ((Complex.ofRealCLM.differentiableAt.comp G
      ((nativeRealMatrixEntry i j).differentiableAt.comp G hi)).mul (differentiableAt_const _))
  exact ((differentiableAt_const _).mul (Complex.ofRealCLM.differentiableAt.comp G hv)).mul hk

theorem wick_quantum_density_fderiv_apply (G H : NativeRealMatrix) (hn : G.det ≠ 0)
    (D : Fin 4 → Fin 4 → ℂ) (M : ℂ) :
    fderiv ℝ (fun A => wickQuantumActionDensity A D M) G H =
      wickQuantumDensityVariation G H D M := by
  have hp : HasDerivAt (fun t : ℝ => G+t • H) H 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).smul_const H).const_add G
  have hd := (wick_quantum_density_differentiableAt G hn D M).hasFDerivAt
  have hd' : HasFDerivAt (fun A => wickQuantumActionDensity A D M)
      (fderiv ℝ (fun A => wickQuantumActionDensity A D M) G) (G+(0:ℝ) • H) := by simpa using hd
  have hc := hd'.comp_hasDerivAt 0 hp
  have hs := wick_quantum_density_path_hasDerivAt G H hn D M
  exact hc.unique hs

theorem wick_quantum_density_curve_hasDerivAt (γ : ℝ → NativeRealMatrix)
    (t : ℝ) (H : NativeRealMatrix) (hγ : HasDerivAt γ H t)
    (hn : (γ t).det ≠ 0) (D : Fin 4 → Fin 4 → ℂ) (M : ℂ) :
    HasDerivAt (fun r => wickQuantumActionDensity (γ r) D M)
      (wickQuantumDensityVariation (γ t) H D M) t := by
  have h := (wick_quantum_density_differentiableAt (γ t) hn D M).hasFDerivAt.comp_hasDerivAt t hγ
  simpa only [Function.comp_def,wick_quantum_density_fderiv_apply (γ t) H hn D M] using h

end AASCKleinGordon
