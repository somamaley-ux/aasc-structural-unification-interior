import NativeRealMetricPathCalculus
import Mathlib.Analysis.Calculus.Deriv.Abs

namespace AASCSemanticExhaustion
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0
open scoped BigOperators Topology
open Filter

def nativeRealClockVolume (G : NativeRealMatrix) : ℝ := Real.sqrt |G.det|

def nativeRealClockDensity (G : NativeRealMatrix) (v : Fin 4 → ℝ) (φ μ : ℝ) : ℝ :=
  (-1/2:ℝ)*nativeRealClockVolume G*
    ((∑ a, ∑ b, G⁻¹ a b*v a*v b)+μ*φ^2)

theorem native_real_clock_volume_path_hasDerivAt (G B H : NativeRealMatrix)
    (hGB : G*B=1) (nondegenerate : G.det≠0) :
    HasDerivAt (fun s : ℝ => nativeRealClockVolume (G+s • H))
      ((1/2:ℝ)*nativeRealClockVolume G*Matrix.trace (B*H)) 0 := by
  have hd:=native_real_metric_determinant_path_hasDerivAt G B H hGB
  have hval : (G+(0:ℝ) • H).det=G.det:=by simp
  have hs : Real.sqrt |G.det|≠0:=ne_of_gt (Real.sqrt_pos.2 (abs_pos.2 nondegenerate))
  have hsq:=Real.sq_sqrt (abs_nonneg G.det)
  rcases lt_or_gt_of_ne nondegenerate with hn|hp
  · have ha:=(hasDerivAt_abs_neg (show (G+(0:ℝ) • H).det<0 by simpa using hn)).comp 0 hd
    have hv:=ha.sqrt (by simpa using (abs_ne_zero.2 nondegenerate))
    have heq : (-(G.det*Matrix.trace (B*H)))/(2*Real.sqrt |G.det|)=
        (1/2:ℝ)*Real.sqrt |G.det| *Matrix.trace (B*H) := by
      have hscale:=congrArg (fun r : ℝ => r*Matrix.trace (B*H)) (hsq.trans (abs_of_neg hn))
      field_simp [hs]
      nlinarith [hscale]
    simpa [nativeRealClockVolume,Function.comp_def,heq] using hv
  · have ha:=(hasDerivAt_abs_pos (show 0<(G+(0:ℝ) • H).det by simpa using hp)).comp 0 hd
    have hv:=ha.sqrt (by simpa using (abs_ne_zero.2 nondegenerate))
    have heq : (G.det*Matrix.trace (B*H))/(2*Real.sqrt |G.det|)=
        (1/2:ℝ)*Real.sqrt |G.det| *Matrix.trace (B*H) := by
      have hscale:=congrArg (fun r : ℝ => r*Matrix.trace (B*H)) (hsq.trans (abs_of_pos hp))
      field_simp [hs]
      nlinarith [hscale]
    simpa [nativeRealClockVolume,Function.comp_def,heq] using hv

theorem native_real_clock_density_path_hasDerivAt (G B H : NativeRealMatrix)
    (hGB : G*B=1) (hBG : B*G=1) (nondegenerate : G.det≠0)
    (v : Fin 4 → ℝ) (φ μ : ℝ) :
    HasDerivAt (fun s : ℝ => nativeRealClockDensity (G+s • H) v φ μ)
      ((-1/2:ℝ)*nativeRealClockVolume G*
        ((1/2:ℝ)*Matrix.trace (B*H)*((∑ a,∑ b,B a b*v a*v b)+μ*φ^2)+
          ∑ a,∑ b,(-B*H*B) a b*v a*v b)) 0 := by
  have hk : HasDerivAt (fun s : ℝ => ∑ a,∑ b,(G+s • H)⁻¹ a b*v a*v b)
      (∑ a,∑ b,(-B*H*B) a b*v a*v b) 0 := by
    apply HasDerivAt.fun_sum
    intro a _
    apply HasDerivAt.fun_sum
    intro b _
    exact ((native_real_metric_inverse_entry_hasDerivAt G B H hGB hBG a b).mul_const (v a)).mul_const (v b)
  have hv:=native_real_clock_volume_path_hasDerivAt G B H hGB nondegenerate
  have h:= (hv.const_mul (-1/2:ℝ)).mul (hk.add_const (μ*φ^2))
  have hInv : G⁻¹=B:=Matrix.inv_eq_right_inv hGB
  convert h using 1 <;> simp [nativeRealClockDensity,nativeRealClockVolume,hInv] <;> ring

#print axioms native_real_clock_volume_path_hasDerivAt
#print axioms native_real_clock_density_path_hasDerivAt
end
end AASCSemanticExhaustion
