import WickOneParticleMassGap
import KGJointZeroSpectrum
import KGFockMaximalMultiplication

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2600000
open MeasureTheory Filter
namespace AASCKleinGordon

def wickOneMassWindow (a : Parameters) : Set FourMomentum :=
  {q | 0<wickInvariantMassSquared q ∧ wickInvariantMassSquared q<4*a.mass^2*a.speed^2}

def wickOneMassShell (a : Parameters) : Set FourMomentum :=
  {q | wickInvariantMassSquared q=a.mass^2*a.speed^2}

theorem wick_one_mass_window_measurable (a : Parameters) : MeasurableSet (wickOneMassWindow a) :=
  ((isOpen_lt continuous_const wick_invariant_mass_squared_continuous).inter
    (isOpen_lt wick_invariant_mass_squared_continuous continuous_const)).measurableSet

theorem wick_one_mass_shell_measurable (a : Parameters) : MeasurableSet (wickOneMassShell a) :=
  (isClosed_eq wick_invariant_mass_squared_continuous continuous_const).measurableSet

theorem wick_particle_in_one_mass_window_iff (a : Parameters) (n : ℕ) (x : ParticleConfiguration n) :
    particleFourMomentum a n x∈wickOneMassWindow a ↔ n=1 := by
  have hm : 0<a.mass^2*a.speed^2 := mul_pos (sq_pos_of_pos a.mass_pos) (sq_pos_of_pos a.speed_pos)
  constructor
  · intro h
    change 0<wickInvariantMassSquared (particleFourMomentum a n x) ∧
      wickInvariantMassSquared (particleFourMomentum a n x)<4*a.mass^2*a.speed^2 at h
    by_contra hn
    by_cases hz : n=0
    · subst n
      simp [particleFourMomentum_zero,wickInvariantMassSquared] at h
    · have hg := wick_particle_higher_invariant_mass_gap a n (by omega) x
      linarith
  · intro hn
    subst n
    change 0<wickInvariantMassSquared (particleFourMomentum a 1 x) ∧ _
    rw [wick_particle_one_invariant_mass]
    constructor <;> nlinarith

theorem wick_particle_in_one_mass_shell_iff (a : Parameters) (n : ℕ) (x : ParticleConfiguration n) :
    particleFourMomentum a n x∈wickOneMassShell a ↔ n=1 := by
  have hm : 0<a.mass^2*a.speed^2 := mul_pos (sq_pos_of_pos a.mass_pos) (sq_pos_of_pos a.speed_pos)
  constructor
  · intro h
    change wickInvariantMassSquared (particleFourMomentum a n x)=a.mass^2*a.speed^2 at h
    by_contra hn
    by_cases hz : n=0
    · subst n
      have hzero : wickInvariantMassSquared (particleFourMomentum a 0 x)=0 := by
        simp [particleFourMomentum_zero,wickInvariantMassSquared]
      rw [hzero] at h
      linarith
    · have hg := wick_particle_higher_invariant_mass_gap a n (by omega) x
      nlinarith
  · intro hn
    subst n
    exact wick_particle_one_invariant_mass a x

def wickOneSectorSymbol (a : Parameters) : FockContractiveSymbol a where
  value n _ := if n=1 then 1 else 0
  measurable _ := measurable_const
  invariant _ _ _ := rfl
  bound n _ := by split_ifs <;> norm_num

def wickOneParticleProjection (a : Parameters) : FockHilbert a →L[ℂ] FockHilbert a :=
  symbolOperator a (wickOneSectorSymbol a)

theorem wick_one_particle_projection_component (a : Parameters) (f : FockHilbert a) (n : ℕ) :
    wickOneParticleProjection a f n=if n=1 then f n else 0 := by
  classical
  apply Subtype.ext
  apply Lp.ext
  by_cases hn : n=1
  · filter_upwards [symbolOperator_ae a (wickOneSectorSymbol a) f n] with x hx
    simpa [wickOneParticleProjection,wickOneSectorSymbol,hn] using hx
  · filter_upwards [symbolOperator_ae a (wickOneSectorSymbol a) f n,
      Lp.coeFn_zero ℂ 2 (particleMeasure a n)] with x hx hz
    simp only [if_neg hn]
    have heq : (symbolOperator a (wickOneSectorSymbol a) f n).val x=0 := by
      simpa [wickOneSectorSymbol,hn] using hx
    exact heq.trans hz.symm

theorem wick_joint_mass_window_is_one_particle (a : Parameters) :
    jointSpectralProjection a (wickOneMassWindow a) (wick_one_mass_window_measurable a)=
      wickOneParticleProjection a := by
  apply symbolOperator_eq_of_value_eq
  intro n x
  classical
  change (wickOneMassWindow a).indicator (fun _ => (1 : ℂ)) (particleFourMomentum a n x)=
    if n=1 then 1 else 0
  by_cases hn : n=1 <;> simp [wick_particle_in_one_mass_window_iff,hn]

theorem wick_joint_mass_shell_is_one_particle (a : Parameters) :
    jointSpectralProjection a (wickOneMassShell a) (wick_one_mass_shell_measurable a)=
      wickOneParticleProjection a := by
  apply symbolOperator_eq_of_value_eq
  intro n x
  classical
  change (wickOneMassShell a).indicator (fun _ => (1 : ℂ)) (particleFourMomentum a n x)=
    if n=1 then 1 else 0
  by_cases hn : n=1 <;> simp [wick_particle_in_one_mass_shell_iff,hn]

theorem wick_one_particle_projection_idempotent (a : Parameters) :
    (wickOneParticleProjection a).comp (wickOneParticleProjection a)=wickOneParticleProjection a := by
  apply ContinuousLinearMap.ext
  intro f
  apply lp.ext
  funext n
  change wickOneParticleProjection a (wickOneParticleProjection a f) n=wickOneParticleProjection a f n
  rw [wick_one_particle_projection_component]
  by_cases hn : n=1
  · simp only [if_pos hn]
  · rw [if_neg hn,wick_one_particle_projection_component,if_neg hn]

theorem wick_one_particle_projection_symmetric (a : Parameters) (f g : FockHilbert a) :
    inner ℂ (wickOneParticleProjection a f) g=inner ℂ f (wickOneParticleProjection a g) := by
  rw [← wick_joint_mass_window_is_one_particle]
  exact jointSpectralProjection_symmetric a _ _ f g

def wickIsolatedOneParticleSpace (a : Parameters) : Submodule ℂ (FockHilbert a) :=
  (wickOneParticleProjection a-ContinuousLinearMap.id ℂ (FockHilbert a)).ker

theorem wick_isolated_one_particle_space_closed (a : Parameters) :
    IsClosed (wickIsolatedOneParticleSpace a : Set (FockHilbert a)) :=
  ContinuousLinearMap.isClosed_ker _

theorem wick_isolated_one_particle_space_iff (a : Parameters) (f : FockHilbert a) :
    f∈wickIsolatedOneParticleSpace a ↔ ∀ n,n≠1 → f n=0 := by
  change (wickOneParticleProjection a-ContinuousLinearMap.id ℂ (FockHilbert a)) f=0 ↔ _
  simp only [ContinuousLinearMap.sub_apply,ContinuousLinearMap.id_apply,sub_eq_zero]
  constructor
  · intro h n hn
    have hh := congrArg (fun z : FockHilbert a => z n) h
    change wickOneParticleProjection a f n=f n at hh
    rw [wick_one_particle_projection_component,if_neg hn] at hh
    exact hh.symm
  · intro h
    apply lp.ext
    funext n
    rw [wick_one_particle_projection_component]
    split_ifs with hn
    · rfl
    · exact (h n hn).symm

theorem wick_isolated_one_particle_contains_original_core (a : Parameters) (f : bosonicSchwartz 1) :
    finiteParticleCoreToFock a (wickOneParticleCore f)∈wickIsolatedOneParticleSpace a := by
  apply (wick_isolated_one_particle_space_iff a _).mpr
  intro n hn
  rw [wick_original_fock_component,wick_one_particle_off_sector f n hn,map_zero]

theorem wick_isolated_one_particle_nonzero (a : Parameters) :
    ∃ f : FockHilbert a,f≠0 ∧ f∈wickIsolatedOneParticleSpace a := by
  refine ⟨finiteParticleCoreToFock a (wickOneParticleCore oneParticleSector),?_,
    wick_isolated_one_particle_contains_original_core a oneParticleSector⟩
  intro hz
  apply oneParticleCore_nonzero
  exact finiteParticleCoreToFock_injective a (hz.trans (map_zero _).symm)

def wickJointCasimir (a : Parameters) : FockHilbert a →ₗ.[ℂ] FockHilbert a :=
  fockRealMultiplication a (fun n x => wickInvariantMassSquared (particleFourMomentum a n x))
    (fun n => (wick_invariant_mass_squared_continuous.comp (particleFourMomentum_continuous a n)).measurable)
    (fun n σ x => by dsimp only; rw [particleFourMomentum_permutation])

theorem wick_joint_casimir_self_adjoint (a : Parameters) : IsSelfAdjoint (wickJointCasimir a) :=
  fockRealMultiplication_selfAdjoint _ _ _ _

theorem wick_joint_casimir_graph_on_isolated_sector (a : Parameters) (f : FockHilbert a)
    (hf : f∈wickIsolatedOneParticleSpace a) :
    (f,((a.mass^2*a.speed^2 : ℝ) : ℂ) • f)∈(wickJointCasimir a).graph := by
  apply (fockRealMultiplication_mem_graph _ _ _ _ _ _).mpr
  intro n
  by_cases hn : n=1
  · subst n
    filter_upwards [Lp.coeFn_smul (((a.mass^2*a.speed^2 : ℝ) : ℂ)) (f 1).val] with x hx
    change (((a.mass^2*a.speed^2 : ℝ) : ℂ) • (f 1).val) x=_
    rw [hx,wick_particle_one_invariant_mass]
    rfl
  · have hz := (wick_isolated_one_particle_space_iff a f).mp hf n hn
    change (((((a.mass^2*a.speed^2 : ℝ) : ℂ) • f n).val) : ParticleConfiguration n → ℂ)=ᵐ[particleMeasure a n] _
    rw [hz,smul_zero]
    filter_upwards [Lp.coeFn_zero ℂ 2 (particleMeasure a n)] with x hx
    simp [hx]

/-- The joint maximal multiplier agrees with the SAME original common-core
charge Casimir; no equality of unrestricted composed maximal domains is claimed. -/
theorem wick_joint_casimir_graph_on_original_core (a : Parameters) (u : FiniteParticleCore) :
    (finiteParticleCoreToFock a u,finiteParticleCoreToFock a (wickOriginalCoreCasimir a u))∈
      (wickJointCasimir a).graph := by
  apply (fockRealMultiplication_mem_graph _ _ _ _ _ _).mpr
  intro n
  have h1 := (wickOriginalCoreCasimir a u n).val.coeFn_toLp 2 (particleMeasure a n)
  have h2 := (u n).val.coeFn_toLp 2 (particleMeasure a n)
  filter_upwards [h1,h2] with x hx hy
  simp only [wick_original_fock_component]
  change (((wickOriginalCoreCasimir a u n).val).toLp 2 (particleMeasure a n)) x=
    (wickInvariantMassSquared (particleFourMomentum a n x) : ℂ)*
      ((u n).val.toLp 2 (particleMeasure a n)) x
  rw [hx,hy,wick_original_core_casimir_component]
  simp only [wickInvariantMassSquared,Complex.ofReal_sub,Complex.ofReal_pow]

theorem wick_joint_casimir_graph_on_calibrated_core (a : Parameters) (u : FiniteParticleCore) :
    (finiteParticleCoreToFock a u,finiteParticleCoreToFock a (wickCalibratedStressCasimir a u))∈
      (wickJointCasimir a).graph := by
  rw [wick_calibrated_source_inertial_casimir_same]
  exact wick_joint_casimir_graph_on_original_core a u

end AASCKleinGordon
