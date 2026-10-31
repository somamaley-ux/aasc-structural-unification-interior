import KGEventTranslationContinuity
import KGFockExactGenerators

noncomputable section
set_option maxHeartbeats 600000
set_option synthInstance.maxHeartbeats 200000
open MeasureTheory Filter
namespace AASCKleinGordon

theorem particleTotalEnergy_mass_gap (a : Parameters) (n : ℕ) (x : ParticleConfiguration n) :
    (n : ℝ)*(a.mass*a.speed^2)≤particleTotalEnergy a n x := by
  calc
    _ = ∑ _i : Fin n,a.mass*a.speed^2 := by simp
    _ ≤ _ := Finset.sum_le_sum (fun i _ => energy_ge_rest a (x i))

theorem particleTotalEnergy_pos_of_nonzero (a : Parameters) (n : ℕ) (hn : n≠0)
    (x : ParticleConfiguration n) : 0<particleTotalEnergy a n x := by
  have hr : 0<(n : ℝ)*(a.mass*a.speed^2) := by
    have hp : 0<n := Nat.pos_of_ne_zero hn
    have := a.mass_pos
    have := a.speed_pos
    positivity
  exact hr.trans_le (particleTotalEnergy_mass_gap a n x)

theorem fockEnergy_kernel_positive_sector_zero (a : Parameters) (f : (fockMaximalEnergy a).domain)
    (hf : fockMaximalEnergy a f=0) (n : ℕ) (hn : n≠0) : f.val n=0 := by
  have hg := (fockRealMultiplication_mem_graph a (particleTotalEnergy a)
    (fun n => (particleTotalEnergy_continuous a n).measurable)
    (particleTotalEnergy_particlePermutation a) f.val (fockMaximalEnergy a f)).mp
      ((fockMaximalEnergy a).mem_graph f)
  rw [hf] at hg
  have hgn : (0 : ParticleHilbert a n)=ᵐ[particleMeasure a n]
      (fun x => (particleTotalEnergy a n x : ℂ)*(f.val n).val x) := hg n
  apply Subtype.ext
  apply Lp.ext
  filter_upwards [hgn,(Lp.coeFn_zero ℂ 2 (particleMeasure a n))] with x hx hz
  have he : (particleTotalEnergy a n x : ℂ)≠0 := by
    exact_mod_cast (particleTotalEnergy_pos_of_nonzero a n hn x).ne'
  have hm : (particleTotalEnergy a n x : ℂ)*(f.val n).val x=0 := hx.symm.trans hz
  have hzero := (mul_eq_zero.mp hm).resolve_left he
  exact hzero.trans hz.symm

theorem fock_supported_zero_sector_is_vacuum_multiple (a : Parameters) (f : FockHilbert a)
    (hf : ∀ n : ℕ,n≠0 → f n=0) : ∃ z : ℂ,f=z • fockVacuum a := by
  let x0 : ParticleConfiguration 0 := fun i => Fin.elim0 i
  let z : ℂ := (f 0).val x0
  have h0 : f 0=z • bosonicCoreToSector a 0 vacuumSector := by
    apply Subtype.ext
    apply Lp.ext
    have hsm := Lp.coeFn_smul z (bosonicCoreToSector a 0 vacuumSector).val
    have hv := vacuumSchwartz.coeFn_toLp 2 (particleMeasure a 0)
    filter_upwards [hsm,hv] with x hx hy
    change (f 0).val x=(z • (bosonicCoreToSector a 0 vacuumSector).val) x
    rw [hx]
    change (f 0).val x=z*(vacuumSchwartz.toLp 2 (particleMeasure a 0)) x
    rw [hy]
    change (f 0).val x=z*1
    rw [mul_one]
    exact congrArg (fun q : ParticleConfiguration 0 => (f 0).val q) (Subsingleton.elim x x0)
  refine ⟨z,?_⟩
  have hv : fockVacuum a=lp.single 2 0 (bosonicCoreToSector a 0 vacuumSector) := by
    rw [fockVacuum,vacuumCore,finiteParticleCoreToFock_on_sector]
  rw [hv]
  apply lp.ext
  funext n
  cases n with
  | zero => simpa only [lp.coeFn_smul,Pi.smul_apply,lp.single_apply,Pi.single_eq_same] using h0
  | succ n => simp [hf (n+1) (Nat.succ_ne_zero n),lp.single_apply]

theorem fockEnergy_kernel_is_vacuum_multiple (a : Parameters) (f : (fockMaximalEnergy a).domain)
    (hf : fockMaximalEnergy a f=0) : ∃ z : ℂ,f.val=z • fockVacuum a :=
  fock_supported_zero_sector_is_vacuum_multiple a f.val
    (fockEnergy_kernel_positive_sector_zero a f hf)

theorem time_invariant_mem_energy_kernel (a : Parameters) (f : FockHilbert a)
    (hf : ∀ t : ℝ,fockTimeTranslation a t f=f) :
    ∃ hd : f∈(fockMaximalEnergy a).domain,fockMaximalEnergy a ⟨f,hd⟩=0 := by
  have hc : HasDerivAt (fun t : ℝ => fockTimeTranslation a t f) 0 0 := by
    have he : (fun t : ℝ => fockTimeTranslation a t f)=(fun _ : ℝ => f) := funext hf
    rw [he]
    exact hasDerivAt_const 0 f
  have hd := ((fockTimeTranslation_exactGenerator a).1 f).mp hc.differentiableAt
  refine ⟨hd,?_⟩
  have he := ((fockTimeTranslation_exactGenerator a).2 ⟨f,hd⟩).unique hc
  exact (smul_eq_zero.mp he).resolve_left
    (GlobalCharge.physical_generator_coefficient_nonzero a.hbar a.hbar_pos)

theorem time_invariant_is_vacuum_multiple (a : Parameters) (f : FockHilbert a)
    (hf : ∀ t : ℝ,fockTimeTranslation a t f=f) : ∃ z : ℂ,f=z • fockVacuum a := by
  obtain ⟨hd,hz⟩ := time_invariant_mem_energy_kernel a f hf
  exact fockEnergy_kernel_is_vacuum_multiple a ⟨f,hd⟩ hz

theorem normalized_time_invariant_is_vacuum_phase (a : Parameters) (f : FockHilbert a)
    (hn : ‖f‖=1) (hf : ∀ t : ℝ,fockTimeTranslation a t f=f) :
    ∃ z : ℂ,‖z‖=1 ∧ f=z • fockVacuum a := by
  obtain ⟨z,hz⟩ := time_invariant_is_vacuum_multiple a f hf
  refine ⟨z,?_,hz⟩
  rw [hz,norm_smul,fockVacuum_norm,mul_one] at hn
  exact hn

end AASCKleinGordon
