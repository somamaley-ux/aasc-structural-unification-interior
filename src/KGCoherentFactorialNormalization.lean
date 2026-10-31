import KGCoherentVectors

noncomputable section
open scoped SchwartzMap
namespace AASCKleinGordon

def coherentFactor (n : ℕ) : ℂ := (Real.sqrt (n.factorial : ℝ) : ℂ)⁻¹

theorem sqrt_factorial_succ_real (n : ℕ) :
    Real.sqrt ((n+1).factorial : ℝ)=Real.sqrt (n+1 : ℝ)*Real.sqrt (n.factorial : ℝ) := by
  rw [Nat.factorial_succ,Nat.cast_mul,Real.sqrt_mul (by positivity)]
  norm_cast

theorem coherentFactor_succ (n : ℕ) :
    (Real.sqrt (n+1 : ℝ) : ℂ)*coherentFactor (n+1)=coherentFactor n := by
  have hs : Real.sqrt (n+1 : ℝ)≠0 := (Real.sqrt_pos.mpr (by positivity)).ne'
  have hf : Real.sqrt (n.factorial : ℝ)≠0 :=
    (Real.sqrt_pos.mpr (by exact_mod_cast Nat.factorial_pos n)).ne'
  have hr : Real.sqrt (n+1 : ℝ)*(Real.sqrt ((n+1).factorial : ℝ))⁻¹=
      (Real.sqrt (n.factorial : ℝ))⁻¹ := by
    rw [sqrt_factorial_succ_real]
    field_simp
  unfold coherentFactor
  exact_mod_cast hr

theorem coherentFactor_creation (n : ℕ) :
    (Real.sqrt (n+1 : ℝ) : ℂ)*coherentFactor n=((n+1 : ℕ) : ℂ)*coherentFactor (n+1) := by
  have hr : (Real.sqrt (n+1 : ℝ) : ℂ)^2=((n+1 : ℕ) : ℂ) := by
    have hh:=Real.sq_sqrt (show (0 : ℝ)≤n+1 by positivity)
    exact_mod_cast hh
  rw [← hr,pow_two,mul_assoc,coherentFactor_succ]

end AASCKleinGordon
