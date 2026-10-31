import KGLorentzBoostShell
import KGSpacetimeSmearing
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

noncomputable section
set_option maxHeartbeats 600000
open scoped SchwartzMap FourierTransform
namespace AASCKleinGordon

def spacetimeAxisBoostCLE (r : ℝ) : Spacetime ≃L[ℝ] Spacetime :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 4 => ℝ)).trans
    ((axisBoostFourCLE r).trans (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 4 => ℝ)).symm)

@[simp] theorem spacetimeAxisBoostCLE_apply (r : ℝ) (x : Spacetime) (i : Fin 4) :
    spacetimeAxisBoostCLE r x i = axisBoostFour r (fun j => x j) i := rfl

theorem spacetimeAxisBoost_zero (x : Spacetime) : spacetimeAxisBoostCLE 0 x=x := by
  ext i
  exact congrFun (axisBoostFour_zero (fun j => x j)) i

theorem spacetimeAxisBoost_add (r s : ℝ) (x : Spacetime) :
    spacetimeAxisBoostCLE (r+s) x=spacetimeAxisBoostCLE r (spacetimeAxisBoostCLE s x) := by
  ext i
  exact congrFun (axisBoostFour_add r s (fun j => x j)) i

theorem spacetimeAxisBoost_neg_inverse (r : ℝ) (x : Spacetime) :
    spacetimeAxisBoostCLE (-r) (spacetimeAxisBoostCLE r x)=x := by
  rw [← spacetimeAxisBoost_add,neg_add_cancel,spacetimeAxisBoost_zero]

theorem spacetimeAxisBoost_transpose (r : ℝ) (x y : Spacetime) :
    inner ℝ (spacetimeAxisBoostCLE r x) y=inner ℝ x (spacetimeAxisBoostCLE r y) := by
  simp only [PiLp.inner_apply,RCLike.inner_apply,spacetimeAxisBoostCLE_apply]
  simp [Fin.sum_univ_succ,axisBoostFour]
  ring

theorem shellCovector_axisBoost (a : Parameters) (r : ℝ) (p : Momentum) :
    shellCovector a (axisBoostMomentum a (-r) p)=spacetimeAxisBoostCLE r (shellCovector a p) := by
  have hcoord (q : Momentum) : (fun i => shellCovector a q i)=
      ![-energy a q/a.speed,q 0,q 1,q 2] := by
    rw [shellCovector_eq_join]
    ext i
    fin_cases i <;> rfl
  ext i
  change (fun j => shellCovector a (axisBoostMomentum a (-r) p) j) i=
    axisBoostFour r (fun j => shellCovector a p j) i
  rw [hcoord,hcoord]
  fin_cases i
  · change -energy a (axisBoostMomentum a (-r) p)/a.speed=
      Real.cosh r*(-energy a p/a.speed)+Real.sinh r*p 0
    rw [neg_div,axisBoostMomentum_energy]
    simp only [axisBoostTime,Real.cosh_neg,Real.sinh_neg]
    ring
  · change Real.sinh (-r)*(energy a p/a.speed)+Real.cosh (-r)*p 0=
      Real.sinh r*(-energy a p/a.speed)+Real.cosh r*p 0
    simp only [Real.sinh_neg,Real.cosh_neg]
    ring
  all_goals rfl

theorem shellFrequency_axisBoost (a : Parameters) (r : ℝ) (p : Momentum) :
    shellFrequency a (axisBoostMomentum a (-r) p)=spacetimeAxisBoostCLE r (shellFrequency a p) := by
  rw [shellFrequency,shellCovector_axisBoost,shellFrequency,map_smul]

def spacetimeAxisBoostTestCLM (r : ℝ) : 𝓢(Spacetime,ℂ) →L[ℂ] 𝓢(Spacetime,ℂ) :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (spacetimeAxisBoostCLE (-r))

@[simp] theorem spacetimeAxisBoostTestCLM_apply (r : ℝ) (h : 𝓢(Spacetime,ℂ)) (x : Spacetime) :
    spacetimeAxisBoostTestCLM r h x=h (spacetimeAxisBoostCLE (-r) x) := rfl

end AASCKleinGordon
