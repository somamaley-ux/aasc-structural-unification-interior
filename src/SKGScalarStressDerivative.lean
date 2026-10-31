import SKGScalarStressJetAlgebra

/-! Actual Frechet derivatives of the scalar stress polynomial. All Hessian
entries below are derivatives of the given C2 field, not certificate data. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 8000000
open Set Filter MeasureTheory TopologicalSpace AASCSemanticExhaustion
open AASCKleinGordon.CurvedKG
open scoped Topology BigOperators
namespace AASCKleinGordon.SameActionSource

theorem skg_partial_mul (f h : CoordinatePoint → ℝ) (p : CoordinatePoint)
    (hf : DifferentiableAt ℝ f p) (hh : DifferentiableAt ℝ h p) (c : Fin 4) :
    scalarPartial (fun x => f x * h x) p c =
      f p * scalarPartial h p c + h p * scalarPartial f p c := by
  have hd := (hf.hasFDerivAt.mul hh.hasFDerivAt).fderiv
  change fderiv ℝ (fun x => f x * h x) p = _ at hd
  simp only [scalarPartial, hd, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]

theorem skg_partial_add (f h : CoordinatePoint → ℝ) (p : CoordinatePoint)
    (hf : DifferentiableAt ℝ f p) (hh : DifferentiableAt ℝ h p) (c : Fin 4) :
    scalarPartial (fun x => f x + h x) p c = scalarPartial f p c + scalarPartial h p c := by
  have hd := (hf.hasFDerivAt.add hh.hasFDerivAt).fderiv
  change fderiv ℝ (fun x => f x + h x) p = _ at hd
  simp only [scalarPartial, hd, ContinuousLinearMap.add_apply]

theorem skg_partial_sub (f h : CoordinatePoint → ℝ) (p : CoordinatePoint)
    (hf : DifferentiableAt ℝ f p) (hh : DifferentiableAt ℝ h p) (c : Fin 4) :
    scalarPartial (fun x => f x - h x) p c = scalarPartial f p c - scalarPartial h p c := by
  have hd := (hf.hasFDerivAt.sub hh.hasFDerivAt).fderiv
  change fderiv ℝ (fun x => f x - h x) p = _ at hd
  simp only [scalarPartial, hd, ContinuousLinearMap.sub_apply]

theorem skg_partial_const_mul (r : ℝ) (f : CoordinatePoint → ℝ) (p : CoordinatePoint)
    (hf : DifferentiableAt ℝ f p) (c : Fin 4) :
    scalarPartial (fun x => r * f x) p c = r * scalarPartial f p c := by
  rw [scalarPartial, (hf.hasFDerivAt.const_mul r).fderiv]
  rfl

theorem skg_partial_pow_two (f : CoordinatePoint → ℝ) (p : CoordinatePoint)
    (hf : DifferentiableAt ℝ f p) (c : Fin 4) :
    scalarPartial (fun x => f x ^ 2) p c = 2 * f p * scalarPartial f p c := by
  simp only [pow_two]
  rw [skg_partial_mul f f p hf hf c]
  ring

theorem skg_partial_sum {ι : Type*} [Fintype ι] (f : ι → CoordinatePoint → ℝ)
    (p : CoordinatePoint) (hf : ∀ i, DifferentiableAt ℝ (f i) p) (c : Fin 4) :
    scalarPartial (fun x => ∑ i, f i x) p c = ∑ i, scalarPartial (f i) p c := by
  rw [scalarPartial, (HasFDerivAt.fun_sum (u := Finset.univ) (fun i _ => (hf i).hasFDerivAt)).fderiv]
  simp only [ContinuousLinearMap.sum_apply, scalarPartial]

theorem scalar_flat_kinetic_differentiable (u : CoordinatePoint → ℝ) (p : CoordinatePoint)
    (regular : ContDiffAt ℝ 2 u p) :
    DifferentiableAt ℝ (fun x => scalarFlatKinetic (scalarPartial u x)) p := by
  apply DifferentiableAt.fun_sum
  intro i _
  exact ((c2_local_scalarPartial_differentiableAt u p regular i).pow 2).const_mul (metric i i)

theorem scalar_flat_kinetic_partial (u : CoordinatePoint → ℝ) (p : CoordinatePoint)
    (regular : ContDiffAt ℝ 2 u p) (c : Fin 4) :
    scalarPartial (fun x => scalarFlatKinetic (scalarPartial u x)) p c =
      2 * ∑ i : Fin 4, metric i i * scalarPartial u p i * scalarSecondPartial u p i c := by
  change scalarPartial (fun x => ∑ i : Fin 4, metric i i * scalarPartial u x i ^ 2) p c = _
  rw [skg_partial_sum (fun i x => metric i i * scalarPartial u x i ^ 2) p (fun i =>
    ((c2_local_scalarPartial_differentiableAt u p regular i).pow 2).const_mul (metric i i)) c]
  have per (i : Fin 4) : scalarPartial (fun x => metric i i * scalarPartial u x i ^ 2) p c =
      metric i i * (2 * scalarPartial u p i * scalarSecondPartial u p i c) := by
    rw [skg_partial_const_mul (metric i i) (fun x => scalarPartial u x i ^ 2) p
      ((c2_local_scalarPartial_differentiableAt u p regular i).pow 2) c,
      skg_partial_pow_two (fun x => scalarPartial u x i) p
        (c2_local_scalarPartial_differentiableAt u p regular i) c]
    rfl
  simp_rw [per]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  change metric i i * (2 * scalarPartial u p i * scalarSecondPartial u p i c) = _
  ring

theorem scalar_stress_polynomial_partial (L u : CoordinatePoint → ℝ) (mu2 : ℝ)
    (p : CoordinatePoint) (regularL : DifferentiableAt ℝ L p)
    (regularU : ContDiffAt ℝ 2 u p) (c a b : Fin 4) :
    scalarPartial (fun x => scalarConformalStressPolynomial L u mu2 x a b) p c =
      scalarStressJetPartial (L p) (u p) mu2 (scalarPartial u p) (scalarPartial L p)
        (scalarSecondPartial u p) c a b := by
  have hu : DifferentiableAt ℝ u p := regularU.differentiableAt (by norm_num)
  have hP (i : Fin 4) := c2_local_scalarPartial_differentiableAt u p regularU i
  have hK := scalar_flat_kinetic_differentiable u p regularU
  have hM : DifferentiableAt ℝ (fun x => mu2 * L x * u x ^ 2) p :=
    (regularL.const_mul mu2).mul (hu.pow 2)
  have partialM : scalarPartial (fun x => mu2 * L x * u x ^ 2) p c =
      mu2 * (scalarPartial L p c * u p ^ 2 + L p * (2 * u p * scalarPartial u p c)) := by
    rw [skg_partial_mul (fun x => mu2 * L x) (fun x => u x ^ 2) p
      (regularL.const_mul mu2) (hu.pow 2) c,
      skg_partial_pow_two u p hu c, skg_partial_const_mul mu2 L p regularL c]
    ring
  have hQ := hK.add hM
  have partialQ : scalarPartial (fun x => scalarFlatKinetic (scalarPartial u x) +
      mu2 * L x * u x ^ 2) p c =
      2 * (∑ i : Fin 4, metric i i * scalarPartial u p i * scalarSecondPartial u p i c) +
        mu2 * (scalarPartial L p c * u p ^ 2 + L p * (2 * u p * scalarPartial u p c)) := by
    rw [skg_partial_add _ _ p hK hM c, scalar_flat_kinetic_partial u p regularU c, partialM]
  change scalarPartial (fun x => scalarPartial u x a * scalarPartial u x b -
    ((1 / 2 : ℝ) * metric a b) *
      (scalarFlatKinetic (scalarPartial u x) + mu2 * L x * u x ^ 2)) p c = _
  rw [skg_partial_sub (fun x => scalarPartial u x a * scalarPartial u x b)
    (fun x => ((1 / 2 : ℝ) * metric a b) *
      (scalarFlatKinetic (scalarPartial u x) + mu2 * L x * u x ^ 2)) p
      ((hP a).mul (hP b)) (hQ.const_mul ((1 / 2 : ℝ) * metric a b)) c,
    skg_partial_mul (fun x => scalarPartial u x a) (fun x => scalarPartial u x b) p (hP a) (hP b) c,
    skg_partial_const_mul ((1 / 2 : ℝ) * metric a b)
      (fun x => scalarFlatKinetic (scalarPartial u x) + mu2 * L x * u x ^ 2) p hQ c, partialQ]
  change scalarPartial u p a * scalarSecondPartial u p b c +
      scalarPartial u p b * scalarSecondPartial u p a c - _ = _
  unfold scalarStressJetPartial
  ring

end AASCKleinGordon.SameActionSource
