import KGGeneralLorentzSchwartz
import KGOriginalCoreEventTranslation

/-! Actual all-matrix pullbacks on the original bosonic Schwartz core.
This continuous core action precedes, and does not assume, Wigner-measure
invariance or extension to a full-Fock unitary. -/
noncomputable section
set_option maxHeartbeats 2200000
set_option synthInstance.maxHeartbeats 200000
open scoped SchwartzMap DirectSum
namespace AASCKleinGordon

def particleLorentzMap (a : Parameters) (n : ℕ) (L : ProperLorentzTransform)
    (x : ParticleConfiguration n) : ParticleConfiguration n := fun i => lorentzShellMap a L (x i)

theorem particleLorentzMap_one (a : Parameters) (n : ℕ) (x : ParticleConfiguration n) :
    particleLorentzMap a n 1 x=x := by
  funext i
  exact lorentzShellMap_one a (x i)

theorem particleLorentzMap_mul (a : Parameters) (n : ℕ) (L M : ProperLorentzTransform)
    (x : ParticleConfiguration n) :
    particleLorentzMap a n (L*M) x=particleLorentzMap a n L (particleLorentzMap a n M x) := by
  funext i
  exact lorentzShellMap_mul a L M (x i)

theorem particleLorentzMap_inverse (a : Parameters) (n : ℕ) (L : ProperLorentzTransform)
    (x : ParticleConfiguration n) : particleLorentzMap a n L⁻¹ (particleLorentzMap a n L x)=x := by
  rw [← particleLorentzMap_mul,inv_mul_cancel,particleLorentzMap_one]

theorem particleLorentzMap_temperate (a : Parameters) (n : ℕ) (L : ProperLorentzTransform) :
    (particleLorentzMap a n L).HasTemperateGrowth := by
  classical
  have h : (fun x : ParticleConfiguration n => ∑ i : Fin n,
      (ContinuousLinearMap.single ℝ (fun _ : Fin n => Momentum) i)
        (lorentzShellMap a L (x i))).HasTemperateGrowth := by
    apply Function.HasTemperateGrowth.sum
    intro i _
    exact (ContinuousLinearMap.single ℝ (fun _ : Fin n => Momentum) i).hasTemperateGrowth.comp
      ((lorentzShellMap_temperate a L).comp
        (ContinuousLinearMap.proj i : ParticleConfiguration n →L[ℝ] Momentum).hasTemperateGrowth)
  convert h using 1
  funext x i
  simp [ContinuousLinearMap.single_apply]
  rfl

theorem particleLorentzMap_polynomial_inverse_bound (a : Parameters) (n : ℕ)
    (L : ProperLorentzTransform) :
    ∃ (k : ℕ) (C : ℝ), ∀ x, ‖x‖≤C*(1+‖particleLorentzMap a n L x‖)^k := by
  obtain ⟨k,C,h⟩:=(particleLorentzMap_temperate a n L⁻¹).2 0
  refine ⟨k,C,fun x => ?_⟩
  simpa only [norm_iteratedFDeriv_zero,particleLorentzMap_inverse] using h (particleLorentzMap a n L x)

def particleLorentzSchwartzCLM (a : Parameters) (n : ℕ) (L : ProperLorentzTransform) :
    𝓢(ParticleConfiguration n,ℂ) →L[ℂ] 𝓢(ParticleConfiguration n,ℂ) :=
  SchwartzMap.compCLM ℂ (particleLorentzMap_temperate a n L⁻¹)
    (particleLorentzMap_polynomial_inverse_bound a n L⁻¹)

@[simp] theorem particleLorentzSchwartz_apply (a : Parameters) (n : ℕ) (L : ProperLorentzTransform)
    (H : 𝓢(ParticleConfiguration n,ℂ)) (x : ParticleConfiguration n) :
    particleLorentzSchwartzCLM a n L H x=H (particleLorentzMap a n L⁻¹ x) := rfl

def bosonicLorentzSchwartzCLM (a : Parameters) (n : ℕ) (L : ProperLorentzTransform) :
    bosonicSchwartz n →L[ℂ] bosonicSchwartz n :=
  ((particleLorentzSchwartzCLM a n L).comp (bosonicSchwartz n).subtypeL).codRestrict
    (bosonicSchwartz n) (fun H => by
      intro σ x
      change H.val (fun i => lorentzShellMap a L⁻¹ (x (σ i))) =
        H.val (fun i => lorentzShellMap a L⁻¹ (x i))
      exact H.property σ (fun i => lorentzShellMap a L⁻¹ (x i)))

@[simp] theorem bosonicLorentzSchwartz_apply (a : Parameters) (n : ℕ) (L : ProperLorentzTransform)
    (H : bosonicSchwartz n) (x : ParticleConfiguration n) :
    (bosonicLorentzSchwartzCLM a n L H).val x=H.val (particleLorentzMap a n L⁻¹ x) := rfl

theorem bosonicLorentzSchwartz_one (a : Parameters) (n : ℕ) (H : bosonicSchwartz n) :
    bosonicLorentzSchwartzCLM a n 1 H=H := by
  apply Subtype.ext
  ext x
  simp only [bosonicLorentzSchwartz_apply,inv_one,particleLorentzMap_one]

theorem bosonicLorentzSchwartz_mul (a : Parameters) (n : ℕ) (L M : ProperLorentzTransform)
    (H : bosonicSchwartz n) :
    bosonicLorentzSchwartzCLM a n L (bosonicLorentzSchwartzCLM a n M H)=
      bosonicLorentzSchwartzCLM a n (L*M) H := by
  apply Subtype.ext
  ext x
  simp only [bosonicLorentzSchwartz_apply,mul_inv_rev,particleLorentzMap_mul]

def coreLorentz (a : Parameters) (L : ProperLorentzTransform) : FiniteParticleCore →ₗ[ℂ] FiniteParticleCore :=
  DirectSum.lmap (fun n => (bosonicLorentzSchwartzCLM a n L).toLinearMap)

@[simp] theorem coreLorentz_lof (a : Parameters) (L : ProperLorentzTransform) (n : ℕ)
    (H : bosonicSchwartz n) :
    coreLorentz a L (DirectSum.lof ℂ ℕ (fun n => bosonicSchwartz n) n H)=
      DirectSum.lof ℂ ℕ (fun n => bosonicSchwartz n) n (bosonicLorentzSchwartzCLM a n L H) := by
  simp only [coreLorentz,DirectSum.lmap_lof]
  rfl

theorem coreLorentz_continuous (a : Parameters) (L : ProperLorentzTransform) :
    Continuous (coreLorentz a L) := by
  apply (core_linearMap_continuous_iff _ finiteParticleCore_withSeminorms _).mpr
  intro n
  change Continuous (fun H : bosonicSchwartz n => coreLorentz a L
    (DirectSum.lof ℂ ℕ (fun n => bosonicSchwartz n) n H))
  simp_rw [coreLorentz_lof]
  exact (finiteParticleCore_lof_continuous n).comp (bosonicLorentzSchwartzCLM a n L).continuous

theorem coreLorentz_one (a : Parameters) (u : FiniteParticleCore) : coreLorentz a 1 u=u := by
  induction u using DirectSum.induction_on with
  | zero => exact map_zero _
  | add x y hx hy => simp only [map_add,hx,hy]
  | of n H =>
      change coreLorentz a 1 (DirectSum.lof ℂ ℕ (fun n => bosonicSchwartz n) n H)=
        DirectSum.lof ℂ ℕ (fun n => bosonicSchwartz n) n H
      rw [coreLorentz_lof,bosonicLorentzSchwartz_one]

theorem coreLorentz_mul (a : Parameters) (L M : ProperLorentzTransform) (u : FiniteParticleCore) :
    coreLorentz a L (coreLorentz a M u)=coreLorentz a (L*M) u := by
  induction u using DirectSum.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add,hx,hy]
  | of n H =>
      change coreLorentz a L (coreLorentz a M (DirectSum.lof ℂ ℕ (fun n => bosonicSchwartz n) n H))=
        coreLorentz a (L*M) (DirectSum.lof ℂ ℕ (fun n => bosonicSchwartz n) n H)
      simp only [coreLorentz_lof,bosonicLorentzSchwartz_mul]

theorem coreLorentz_inverse (a : Parameters) (L : ProperLorentzTransform) (u : FiniteParticleCore) :
    coreLorentz a L⁻¹ (coreLorentz a L u)=u := by
  rw [coreLorentz_mul,inv_mul_cancel,coreLorentz_one]

def coreLorentzEquiv (a : Parameters) (L : ProperLorentzTransform) :
    FiniteParticleCore ≃L[ℂ] FiniteParticleCore where
  toLinearEquiv:=
    { toLinearMap:=coreLorentz a L
      invFun:=coreLorentz a L⁻¹
      left_inv:=coreLorentz_inverse a L
      right_inv:=by intro u; simpa only [inv_inv] using coreLorentz_inverse a L⁻¹ u }
  continuous_toFun:=coreLorentz_continuous a L
  continuous_invFun:=coreLorentz_continuous a L⁻¹

theorem bosonicLorentz_zero_sector (a : Parameters) (L : ProperLorentzTransform)
    (H : bosonicSchwartz 0) : bosonicLorentzSchwartzCLM a 0 L H=H := by
  apply Subtype.ext
  ext x
  rw [bosonicLorentzSchwartz_apply]
  exact congrArg H.val (Subsingleton.elim _ _)

theorem coreLorentz_fixes_vacuum (a : Parameters) (L : ProperLorentzTransform) :
    coreLorentz a L vacuumCore=vacuumCore := by
  rw [vacuumCore,coreLorentz_lof,bosonicLorentz_zero_sector]

end AASCKleinGordon
