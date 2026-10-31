import OriginalEHBoundaryCurrent

/-! Cancel actual metric lowering/raising before the pending Palatini
variation calculation. No field equation or curvature-response form is input. -/
namespace AASCSemanticExhaustion
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
open scoped BigOperators

def ehConnectionRicci (Γ : ConnectionCoefficients) (p : CoordinatePoint) (a b : Fin 4) : ℝ :=
  ∑ j : Fin 4, connectionCurvature Γ p j a j b

theorem eh_actual_ricci_is_connection_ricci (g : MetricField)
    (sg : MetricFieldSymmetric g) (p : CoordinatePoint) (hn : (g p).det ≠ 0) (a b : Fin 4) :
    coordinateRicci g p a b = ehConnectionRicci (leviCivitaCoefficients g) p a b := by
  have hG : (g p).transpose = g p := by
    ext i j
    exact sg p j i
  have hB : ((g p)⁻¹).transpose = (g p)⁻¹ := by
    rw [Matrix.transpose_nonsing_inv,hG]
  have bs (i j : Fin 4) : (g p)⁻¹ i j = (g p)⁻¹ j i := by
    have he := congrArg (fun M : Tensor2 => M j i) hB
    simpa only [Matrix.transpose_apply] using he
  have inverse : (g p)⁻¹ * g p = 1 := Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hn)
  unfold coordinateRicci loweredConnectionCurvature ehConnectionRicci
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_comm]
  calc
    (∑ e : Fin 4, ∑ i : Fin 4, (g p)⁻¹ i j *
        (g p i e * connectionCurvature (leviCivitaCoefficients g) p e a j b)) =
        ∑ e : Fin 4, ((g p)⁻¹ * g p) j e *
          connectionCurvature (leviCivitaCoefficients g) p e a j b := by
      apply Finset.sum_congr rfl
      intro e _
      simp only [Matrix.mul_apply,Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      rw [bs i j]
      ring
    _ = connectionCurvature (leviCivitaCoefficients g) p j a j b := by
      rw [inverse]
      simp only [Matrix.one_apply,ite_mul,one_mul,zero_mul,Finset.sum_ite_eq,Finset.mem_univ,ite_true]

end
end AASCSemanticExhaustion
