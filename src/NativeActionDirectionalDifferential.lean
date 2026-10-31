import OperationalMetricSourceAttachment
import Mathlib.Analysis.Calculus.Deriv.Comp

/-! Construct the first response from actual action readouts. The action's
two-parameter restrictions, rather than an assumed linear functional, yield
linearity. No norm topology is put on the LF deformation space. -/
namespace AASCSemanticExhaustion
noncomputable section
set_option autoImplicit false

variable {P : Type*} [AddCommGroup P] [Module ℝ P]

def nativeActionDirectional (S : P → ℝ) (h : P) : ℝ :=
  deriv (fun t : ℝ => S (t • h)) 0

def NativeActionFiniteParamDifferentiable (S : P → ℝ) : Prop :=
  ∀ h k : P, DifferentiableAt ℝ (fun z : ℝ × ℝ => S (z.1 • h + z.2 • k)) 0

theorem native_action_pair_ray_hasDerivAt (S : P → ℝ)
    (regular : NativeActionFiniteParamDifferentiable S) (h k : P) (a b : ℝ) :
    HasDerivAt (fun t : ℝ => S ((t*a) • h + (t*b) • k))
      (fderiv ℝ (fun z : ℝ × ℝ => S (z.1 • h + z.2 • k)) 0 (a,b)) 0 := by
  have hp := ((hasDerivAt_id (0:ℝ)).mul_const a).prodMk
    ((hasDerivAt_id (0:ℝ)).mul_const b)
  have hp' : HasDerivAt (fun t : ℝ => (t*a,t*b)) (a,b) 0 := by
    simpa [ContinuousLinearMap.prod_apply] using HasFDerivAt.hasDerivAt hp
  simpa only [Function.comp_def] using
    (regular h k).hasFDerivAt.comp_hasDerivAt_of_eq 0 hp' (by simp only [zero_mul]; rfl)

theorem native_action_directional_hasDerivAt (S : P → ℝ)
    (regular : NativeActionFiniteParamDifferentiable S) (h : P) :
    HasDerivAt (fun t : ℝ => S (t • h)) (nativeActionDirectional S h) 0 := by
  have hh := native_action_pair_ray_hasDerivAt S regular h 0 1 0
  simp only [mul_one, mul_zero, zero_smul, smul_zero, add_zero] at hh
  change HasDerivAt (fun t : ℝ => S (t • h)) (deriv (fun t : ℝ => S (t • h)) 0) 0
  rw [hh.deriv]
  exact hh

theorem native_action_directional_add (S : P → ℝ)
    (regular : NativeActionFiniteParamDifferentiable S) (h k : P) :
    nativeActionDirectional S (h+k) = nativeActionDirectional S h + nativeActionDirectional S k := by
  let D := fderiv ℝ (fun z : ℝ × ℝ => S (z.1 • h + z.2 • k)) 0
  have hs : nativeActionDirectional S (h+k) = D (1,1) := by
    have hh := (native_action_pair_ray_hasDerivAt S regular h k 1 1).deriv
    simpa only [nativeActionDirectional, mul_one, ← smul_add] using hh
  have hl : nativeActionDirectional S h = D (1,0) := by
    simpa only [nativeActionDirectional, mul_one, mul_zero, zero_smul, add_zero] using
      (native_action_pair_ray_hasDerivAt S regular h k 1 0).deriv
  have hr : nativeActionDirectional S k = D (0,1) := by
    simpa only [nativeActionDirectional, mul_one, mul_zero, zero_smul, zero_add] using
      (native_action_pair_ray_hasDerivAt S regular h k 0 1).deriv
  rw [hs,hl,hr]
  simpa using D.map_add (1,0) (0,1)

theorem native_action_directional_smul (S : P → ℝ)
    (regular : NativeActionFiniteParamDifferentiable S) (a : ℝ) (h : P) :
    nativeActionDirectional S (a • h) = a • nativeActionDirectional S h := by
  let D := fderiv ℝ (fun z : ℝ × ℝ => S (z.1 • h + z.2 • (0:P))) 0
  have ha : nativeActionDirectional S (a • h) = D (a,0) := by
    simpa only [D,nativeActionDirectional, mul_zero, zero_smul, smul_zero, add_zero, smul_smul] using
      (native_action_pair_ray_hasDerivAt S regular h 0 a 0).deriv
  have h1 : nativeActionDirectional S h = D (1,0) := by
    simpa only [D,nativeActionDirectional, mul_one, mul_zero, zero_smul, smul_zero, add_zero] using
      (native_action_pair_ray_hasDerivAt S regular h 0 1 0).deriv
  rw [ha,h1]
  simpa using D.map_smul a (1,0)

def nativeActionDifferential (S : P → ℝ)
    (regular : NativeActionFiniteParamDifferentiable S) : P →ₗ[ℝ] ℝ where
  toFun := nativeActionDirectional S
  map_add' := native_action_directional_add S regular
  map_smul' := native_action_directional_smul S regular

#print axioms native_action_pair_ray_hasDerivAt
#print axioms native_action_directional_hasDerivAt
#print axioms native_action_directional_add
#print axioms native_action_directional_smul
#print axioms nativeActionDifferential
end
end AASCSemanticExhaustion
