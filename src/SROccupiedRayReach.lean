import SourceReachConstruction
import Mathlib.Analysis.Normed.Module.RCLike.Real
import Mathlib.Tactic

/-! The constructive two-ray reach calculation of SR 15.7. On its calibrated
spatial-norm branch, original positive-duration unit rays generate exactly
the entire future cone by finite nonnegative ledgers. Completion is explicit
and adds no vectors here because the generated cone is already closed.
This proves geometric record occupation, not the full massive-body/scattering
Hamiltonian, charge or physical clock-device protocol of SR 15.3--15.6. -/
namespace AASCMetricConstruction
noncomputable section
set_option autoImplicit false
open Set NormedSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def srOriginalFutureRayIncrements : Set (ℝ × E):={z|0<z.1 ∧ ‖z.2‖=z.1}
def srRayFutureCone : Set (ℝ × E):={z|‖z.2‖≤z.1}

theorem sr_original_ray_finite_reach_is_future (z : ℝ × E)
    (h : FiniteReach (srOriginalFutureRayIncrements (E:=E)) z) : z∈srRayFutureCone := by
  induction h with
  | zero => simp [srRayFutureCone]
  | @original v hv => exact hv.2.le
  | @add u v _ _ hu hv =>
    change ‖u.2+v.2‖≤u.1+v.1
    exact (norm_add_le _ _).trans (add_le_add hu hv)
  | @scale r hr v _ hv =>
    change ‖r • v.2‖≤r*v.1
    rw [norm_smul,Real.norm_of_nonneg hr]
    exact mul_le_mul_of_nonneg_left hv hr

theorem sr_spatial_direction_and_radial_amount [Nontrivial E] (x:E) :
    ∃ n:E,‖n‖=1 ∧ ‖x‖ • n=x := by
  by_cases hx:x=0
  · obtain ⟨n,hn⟩:=exists_norm_eq E (by norm_num : (0:ℝ)≤1)
    exact ⟨n,hn,by simp [hx]⟩
  · exact ⟨normalize x,norm_normalize hx,norm_smul_normalize x⟩

theorem sr_every_future_increment_has_original_two_ray_ledger [Nontrivial E]
    (z : ℝ × E) (future : z∈srRayFutureCone) :
    ∃ a b:ℝ,∃ n:E,0≤a ∧ 0≤b ∧ ‖n‖=1 ∧
      (1,n)∈srOriginalFutureRayIncrements ∧ (1,-n)∈srOriginalFutureRayIncrements ∧
      z=a • (1,n)+b • (1,-n) := by
  obtain ⟨n,hn,hrad⟩:=sr_spatial_direction_and_radial_amount z.2
  let a:ℝ:=(z.1+‖z.2‖)/2
  let b:ℝ:=(z.1-‖z.2‖)/2
  have ht:‖z.2‖≤z.1:=future
  have ha:0≤a:=by dsimp [a];linarith [norm_nonneg z.2]
  have hb:0≤b:=by dsimp [b];linarith
  refine ⟨a,b,n,ha,hb,hn,⟨by norm_num,hn⟩,⟨by norm_num,by simpa using hn⟩,?_⟩
  apply Prod.ext
  · change z.1=a*1+b*1
    dsimp [a,b]
    ring
  · change z.2=a • n+b • (-n)
    rw [smul_neg,← sub_eq_add_neg,← sub_smul]
    calc
      _=‖z.2‖ • n:=hrad.symm
      _=(a-b) • n:=by congr 1;dsimp [a,b];ring

theorem sr_original_ray_finite_reach_exact_full_cone [Nontrivial E] (z : ℝ × E) :
    FiniteReach (srOriginalFutureRayIncrements (E:=E)) z ↔ z∈srRayFutureCone := by
  constructor
  · exact sr_original_ray_finite_reach_is_future z
  · intro hz
    obtain ⟨a,b,n,ha,hb,_,hp,hm,he⟩:=sr_every_future_increment_has_original_two_ray_ledger z hz
    rw [he]
    exact FiniteReach.add (FiniteReach.scale a ha (.original hp))
      (FiniteReach.scale b hb (.original hm))

theorem sr_original_ray_completed_reach_exact_full_cone [Nontrivial E] :
    completedReach (srOriginalFutureRayIncrements (E:=E))=srRayFutureCone := by
  have hs:{z:ℝ × E|FiniteReach srOriginalFutureRayIncrements z}=srRayFutureCone:=by
    ext z
    exact sr_original_ray_finite_reach_exact_full_cone z
  have hc:IsClosed (srRayFutureCone (E:=E)):=isClosed_le continuous_snd.norm continuous_fst
  change closure {z:ℝ × E|FiniteReach srOriginalFutureRayIncrements z}=srRayFutureCone
  rw [hs,hc.closure_eq]

theorem sr_original_ray_completed_clock_strict [Nontrivial E] (z : ℝ × E)
    (reach : z∈completedReach srOriginalFutureRayIncrements) (nonzero : z≠0) : 0<z.1 := by
  rw [sr_original_ray_completed_reach_exact_full_cone] at reach
  have hf:‖z.2‖≤z.1:=reach
  have ht:0≤z.1:=(norm_nonneg z.2).trans hf
  by_contra hn
  have he:z.1=0:=le_antisymm (le_of_not_gt hn) ht
  have hx:z.2=0:=norm_eq_zero.mp (by rw [he] at hf;exact le_antisymm hf (norm_nonneg _))
  exact nonzero (Prod.ext he hx)

theorem sr_original_ray_role_occupied [Nontrivial E] :
    ∃ z:ℝ × E,z∈srOriginalFutureRayIncrements ∧ z≠0 := by
  obtain ⟨n,hn⟩:=exists_norm_eq E (by norm_num : (0:ℝ)≤1)
  exact ⟨(1,n),⟨by norm_num,hn⟩,by intro hz;have he:=congrArg Prod.fst hz;norm_num at he⟩

#print axioms sr_original_ray_finite_reach_is_future
#print axioms sr_spatial_direction_and_radial_amount
#print axioms sr_every_future_increment_has_original_two_ray_ledger
#print axioms sr_original_ray_finite_reach_exact_full_cone
#print axioms sr_original_ray_completed_reach_exact_full_cone
#print axioms sr_original_ray_completed_clock_strict
#print axioms sr_original_ray_role_occupied
end
end AASCMetricConstruction
