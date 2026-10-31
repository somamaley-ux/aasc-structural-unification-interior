import WickCovariantSourceRigging

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
open MeasureTheory Filter Topology
open scoped SchwartzMap FourierTransform
namespace AASCKleinGordon
attribute [local irreducible] originalWickRaisedStressDistribution wickCovariantOriginalCore

/-- Continuity from an actual continuous control, with no norm on the
Schwartz source silently substituted for its seminorm topology. -/
theorem wick_linear_continuous_of_control {X : Type*}
    [AddCommGroup X] [Module ℂ X] [TopologicalSpace X] [IsTopologicalAddGroup X]
    (L : X →ₗ[ℂ] ℂ) (q : X → ℝ) (hq : Continuous q) (hq0 : q 0=0)
    (hb : ∀ x,‖L x‖≤q x) : Continuous L := by
  apply continuous_iff_continuousAt.mpr
  intro x₀
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hc : Continuous (fun x : X => q (x-x₀)) := hq.comp (continuous_id.sub continuous_const)
  have hs : ∀ᶠ x in 𝓝 x₀,q (x-x₀)<ε :=
    (hc.tendsto x₀).eventually (Iio_mem_nhds (by simpa only [sub_self,hq0] using hε))
  filter_upwards [hs] with x hx
  rw [dist_eq_norm,← map_sub]
  exact (hb _).trans_lt hx

def wickCovariantKernelPrefactor (a : Parameters) (s : ℝ) : ℂ :=
  2*(s : ℂ)^2/(wickCovariantScale a : ℂ)

def wickCovariantKernelTest (a : Parameters) (s : ℝ) (i j : Fin 4)
    (G : 𝓢(ParticleConfiguration 2,ℂ)) : 𝓢(Spacetime,ℂ) →L[ℂ] ℂ :=
  wickCovariantKernelPrefactor a s •
    ((wickKernelEvaluationCLM a 2
      (fun z => wickCoreChannelFrequency0 a 0 1 z+wickCoreChannelFrequency1 a 0 1 z)
      ((wickCoreChannelFrequency0_temperate a 0 1).add
        (wickCoreChannelFrequency1_temperate a 0 1)).1.continuous
      (wickRaisedStressKernelCLM a 2 (wickCoreChannelFrequency0 a 0 1)
        (wickCoreChannelFrequency1 a 0 1) i j G)).comp
      (FourierTransform.fourierCLM ℂ 𝓢(Spacetime,ℂ)))

theorem wick_covariant_kernel_test_apply (a : Parameters) (s : ℝ) (i j : Fin 4)
    (G : 𝓢(ParticleConfiguration 2,ℂ)) (h : 𝓢(Spacetime,ℂ)) :
    wickCovariantKernelTest a s i j G h=wickCovariantKernelPrefactor a s*
      ∫ z,(𝓕 h) (wickCoreChannelFrequency0 a 0 1 z+wickCoreChannelFrequency1 a 0 1 z)*
        (wickRaisedStressKernelCLM a 2 (wickCoreChannelFrequency0 a 0 1)
          (wickCoreChannelFrequency1 a 0 1) i j G) z ∂particleMeasure a 2 := rfl

def wickCovariantKernelMomentumLM (a : Parameters) (s : ℝ) (i j : Fin 4)
    (h : 𝓢(Spacetime,ℂ)) : 𝓢(ParticleConfiguration 2,ℂ) →ₗ[ℂ] ℂ where
  toFun G := wickCovariantKernelTest a s i j G h
  map_add' G H := by
    simp only [wick_covariant_kernel_test_apply,
      map_add,SchwartzMap.add_apply,mul_add]
    rw [integral_add
      (wickKernelTest_integrable a 2
        (fun z => wickCoreChannelFrequency0 a 0 1 z+wickCoreChannelFrequency1 a 0 1 z)
        ((wickCoreChannelFrequency0_temperate a 0 1).add
          (wickCoreChannelFrequency1_temperate a 0 1)).1.continuous _ (𝓕 h))
      (wickKernelTest_integrable a 2
        (fun z => wickCoreChannelFrequency0 a 0 1 z+wickCoreChannelFrequency1 a 0 1 z)
        ((wickCoreChannelFrequency0_temperate a 0 1).add
          (wickCoreChannelFrequency1_temperate a 0 1)).1.continuous _ (𝓕 h))]
    ring
  map_smul' c G := by
    simp only [wick_covariant_kernel_test_apply,
      map_smul,SchwartzMap.smul_apply,smul_eq_mul,RingHom.id_apply]
    simp_rw [show ∀ z : ParticleConfiguration 2,
      (𝓕 h) (wickCoreChannelFrequency0 a 0 1 z+wickCoreChannelFrequency1 a 0 1 z)*
        (c*(wickRaisedStressKernelCLM a 2 (wickCoreChannelFrequency0 a 0 1)
          (wickCoreChannelFrequency1 a 0 1) i j G) z)=
      c*((𝓕 h) (wickCoreChannelFrequency0 a 0 1 z+wickCoreChannelFrequency1 a 0 1 z)*
        (wickRaisedStressKernelCLM a 2 (wickCoreChannelFrequency0 a 0 1)
          (wickCoreChannelFrequency1 a 0 1) i j G) z) from fun _ => by ring]
    rw [integral_const_mul]
    ring

theorem wick_covariant_kernel_test_bound (a : Parameters) (s : ℝ) (i j : Fin 4)
    (G : 𝓢(ParticleConfiguration 2,ℂ)) (h : 𝓢(Spacetime,ℂ)) :
    ‖wickCovariantKernelTest a s i j G h‖≤
      ‖wickCovariantKernelPrefactor a s‖*‖wickChannelKernelL1CLM a 0 1 i j G‖*
        SchwartzMap.seminorm ℂ 0 0 (𝓕 h) := by
  have hn : ‖wickChannelKernelL1CLM a 0 1 i j G‖=
      ∫ z,‖(wickRaisedStressKernelCLM a 2 (wickCoreChannelFrequency0 a 0 1)
        (wickCoreChannelFrequency1 a 0 1) i j G) z‖ ∂particleMeasure a 2 := by
    change ‖(wickRaisedStressKernelCLM a 2 _ _ i j G).toLp 1 _‖=_
    rw [L1.norm_eq_integral_norm]
    exact integral_congr_ae (((wickRaisedStressKernelCLM a 2 _ _ i j G).coeFn_toLp 1 _).fun_comp norm)
  rw [wick_covariant_kernel_test_apply,norm_mul,hn,mul_assoc]
  exact mul_le_mul_of_nonneg_left (wickKernelTest_bound a 2 _
    ((wickCoreChannelFrequency0_temperate a 0 1).add
      (wickCoreChannelFrequency1_temperate a 0 1)).1.continuous _ (𝓕 h)) (norm_nonneg _)

def wickCovariantKernelMomentumCLM (a : Parameters) (s : ℝ) (i j : Fin 4)
    (h : 𝓢(Spacetime,ℂ)) : 𝓢(ParticleConfiguration 2,ℂ) →L[ℂ] ℂ :=
  { toLinearMap := wickCovariantKernelMomentumLM a s i j h
    cont := wick_linear_continuous_of_control _
      (fun G => ‖wickCovariantKernelPrefactor a s‖*‖wickChannelKernelL1CLM a 0 1 i j G‖*
        SchwartzMap.seminorm ℂ 0 0 (𝓕 h))
      ((continuous_const.mul (wickChannelKernelL1CLM a 0 1 i j).continuous.norm).mul continuous_const)
      (by simp) (fun G => wick_covariant_kernel_test_bound a s i j G h) }

def wickCovariantKernelTestLM (a : Parameters) (s : ℝ) (i j : Fin 4) :
    𝓢(ParticleConfiguration 2,ℂ) →ₗ[ℂ] (𝓢(Spacetime,ℂ) →L[ℂ] ℂ) where
  toFun G := wickCovariantKernelTest a s i j G
  map_add' G H := by
    ext h
    exact (wickCovariantKernelMomentumLM a s i j h).map_add G H
  map_smul' c G := by
    ext h
    exact (wickCovariantKernelMomentumLM a s i j h).map_smul c G

theorem wick_covariant_kernel_joint_continuous (a : Parameters) (s : ℝ) (i j : Fin 4) :
    Continuous (fun z : 𝓢(ParticleConfiguration 2,ℂ) × 𝓢(Spacetime,ℂ) =>
      wickCovariantKernelTest a s i j z.1 z.2) := by
  let B := wickCovariantKernelTestLM a s i j
  let P : 𝓢(ParticleConfiguration 2,ℂ) → ℝ := fun G =>
    ‖wickCovariantKernelPrefactor a s‖*‖wickChannelKernelL1CLM a 0 1 i j G‖
  let q : 𝓢(Spacetime,ℂ) → ℝ := fun h => SchwartzMap.seminorm ℂ 0 0 (𝓕 h)
  have hP : Continuous P := continuous_const.mul (wickChannelKernelL1CLM a 0 1 i j).continuous.norm
  have hq : Continuous q := ((schwartz_withSeminorms ℂ Spacetime ℂ).continuous_seminorm (0,0)).comp
    (FourierTransform.fourierCLM ℂ 𝓢(Spacetime,ℂ)).continuous
  have hP0 : P 0=0 := by simp [P]
  have hq0 : q 0=0 := by simp [q]
  apply continuous_iff_continuousAt.mpr
  intro z₀
  let R := fun z : 𝓢(ParticleConfiguration 2,ℂ) × 𝓢(Spacetime,ℂ) =>
    P (z.1-z₀.1)*q z.2+P z₀.1*q (z.2-z₀.2)
  have hR : Continuous R := by dsimp only [R];fun_prop
  have hR0 : R z₀=0 := by simp [R,hP0,hq0]
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hs : ∀ᶠ z in 𝓝 z₀,R z<ε :=
    (hR.tendsto z₀).eventually (Iio_mem_nhds (by simpa only [hR0] using hε))
  filter_upwards [hs] with z hz
  rw [dist_eq_norm]
  have he : B z.1 z.2-B z₀.1 z₀.2=B (z.1-z₀.1) z.2+B z₀.1 (z.2-z₀.2) := by
    simp only [map_sub,ContinuousLinearMap.sub_apply]
    abel
  change ‖B z.1 z.2-B z₀.1 z₀.2‖<ε
  rw [he]
  exact ((norm_add_le _ _).trans (add_le_add
    (wick_covariant_kernel_test_bound a s i j (z.1-z₀.1) z.2)
    (wick_covariant_kernel_test_bound a s i j z₀.1 (z.2-z₀.2)))).trans_lt hz

def wickCovariantPairTest (f g : 𝓢(Momentum,ℂ)) : 𝓢(ParticleConfiguration 2,ℂ) :=
  wickCoreChannelStateKernel 0 (wickOneParticleCore (wickSectorOneOfSchwartzCLM f))
    (wickOneParticleCore (wickSectorOneOfSchwartzCLM g)) 1

theorem wick_covariant_kernel_test_actual_symbol (a : Parameters) (s : ℝ) (i j : Fin 4)
    (G : 𝓢(ParticleConfiguration 2,ℂ)) (h : 𝓢(Spacetime,ℂ)) :
    wickCovariantKernelMomentumCLM a s i j h G=
      ((s : ℂ)^2/((wickCovariantScale a : ℂ)*(a.hbar : ℂ)^2))*
        ∫ z,(𝓕 h) (shellFrequency a (z 0)-shellFrequency a (z 1))*
          (scalarMatrixElement a (massShell a (z 0)) (massShell a (z 1)) i j : ℂ)*G z
            ∂particleMeasure a 2 := by
  have hi : (∫ z,(𝓕 h) (shellFrequency a (z 0)-shellFrequency a (z 1))*
      (scalarMatrixElement a (massShell a (z 0)) (massShell a (z 1)) i j : ℂ)*G z
        ∂particleMeasure a 2)=
      (2*(a.hbar : ℂ)^2)*wickKernelEvaluationCLM a 2
        (fun z => wickCoreChannelFrequency0 a 0 1 z+wickCoreChannelFrequency1 a 0 1 z)
        ((wickCoreChannelFrequency0_temperate a 0 1).add
          (wickCoreChannelFrequency1_temperate a 0 1)).1.continuous
        (wickRaisedStressKernelCLM a 2 (wickCoreChannelFrequency0 a 0 1)
          (wickCoreChannelFrequency1 a 0 1) i j G) (𝓕 h) := by
    change _=(2*(a.hbar : ℂ)^2)*(∫ z,
      (𝓕 h) (wickCoreChannelFrequency0 a 0 1 z+wickCoreChannelFrequency1 a 0 1 z)*
        (wickRaisedStressKernelCLM a 2 (wickCoreChannelFrequency0 a 0 1)
          (wickCoreChannelFrequency1 a 0 1) i j G) z ∂particleMeasure a 2)
    rw [← integral_const_mul]
    apply integral_congr_ae
    exact ae_of_all _ fun z => by
      have he := wick_actual_CA_kernel_elastic_tensor a 0 G z i j
      rw [wick_raised_stress_kernel_CLM_apply]
      change _=(2*(a.hbar : ℂ)^2)*
        ((𝓕 h) (shellFrequency a (z 0)-shellFrequency a (z 1))*_)
      change _=(scalarMatrixElement a (massShell a (z 0)) (massShell a (z 1)) i j : ℂ)*G z at he
      linear_combination -((𝓕 h) (shellFrequency a (z 0)-shellFrequency a (z 1)))*he
  rw [hi]
  change wickCovariantKernelTest a s i j G h=_
  rw [wick_covariant_kernel_test_apply,wickKernelEvaluationCLM_apply]
  have hk : (wickCovariantScale a : ℂ)≠0 :=
    Complex.ofReal_ne_zero.mpr (wick_covariant_scale_positive a).ne'
  have hh : (a.hbar : ℂ)≠0 := Complex.ofReal_ne_zero.mpr a.hbar_pos.ne'
  unfold wickCovariantKernelPrefactor
  field_simp [hk,hh]

theorem wick_covariant_pair_test_apply (f g : 𝓢(Momentum,ℂ)) (z : ParticleConfiguration 2) :
    wickCovariantPairTest f g z=star (f (z 0))*g (z 1) := by
  rw [wickCovariantPairTest,wick_one_particle_mixed_state_apply,
    wick_sector_one_roundtrip,wick_sector_one_roundtrip]

theorem wick_covariant_pair_test_original (a : Parameters) (f g : 𝓢(Momentum,ℂ)) :
    wickCovariantPairTest f g=(wickCovariantScale a : ℂ) •
      wickCoreChannelStateKernel 0 (wickOneParticleCore (wickCovariantOriginalSector a f))
        (wickOneParticleCore (wickCovariantOriginalSector a g)) 1 := by
  ext z
  rw [wick_covariant_pair_test_apply,SchwartzMap.smul_apply,smul_eq_mul,
    wick_one_particle_mixed_state_apply]
  have he := wick_covariant_wavefunction_pair a
    (sectorOneToSchwartz (wickCovariantOriginalSector a f))
    (sectorOneToSchwartz (wickCovariantOriginalSector a g)) (z 0) (z 1)
  rw [wick_covariant_original_sector_wavefunction,wick_covariant_original_sector_wavefunction] at he
  exact he

/-- Exact SAME-source square on every wavepacket pair and spacetime test;
the kernel is constructed from the original mixed-channel stress CLM. -/
theorem wick_covariant_kernel_source_square (a : Parameters) (s : ℝ) (i j : Fin 4)
    (f g : 𝓢(Momentum,ℂ)) (h : 𝓢(Spacetime,ℂ)) :
    wickCovariantKernelMomentumCLM a s i j h (wickCovariantPairTest f g)=
      wickCovariantSourceOperatorLM a s i j h g f := by
  change wickCovariantKernelMomentumLM a s i j h (wickCovariantPairTest f g)=_
  rw [wick_covariant_pair_test_original,map_smul]
  change (wickCovariantScale a : ℂ) * wickCovariantKernelTest a s i j
    (wickCoreChannelStateKernel 0 (wickOneParticleCore (wickCovariantOriginalSector a f))
      (wickOneParticleCore (wickCovariantOriginalSector a g)) 1) h=_
  rw [wick_covariant_kernel_test_apply]
  change _=originalWickRaisedStressDistribution a s
    (wickCovariantOriginalCore a f) (wickCovariantOriginalCore a g) i j h
  rw [wick_covariant_original_core_apply,wick_covariant_original_core_apply]
  rw [wick_original_one_particle_source_test_incidence,wick_one_particle_elastic_test_integral_actual]
  rw [wick_raised_stress_kernel_CLM_apply,wickKernelEvaluationCLM_apply]
  have hk : (wickCovariantScale a : ℂ)≠0 :=
    Complex.ofReal_ne_zero.mpr (wick_covariant_scale_positive a).ne'
  have hh : (a.hbar : ℂ)≠0 := Complex.ofReal_ne_zero.mpr a.hbar_pos.ne'
  unfold wickCovariantKernelPrefactor
  field_simp [hk,hh]

end AASCKleinGordon
