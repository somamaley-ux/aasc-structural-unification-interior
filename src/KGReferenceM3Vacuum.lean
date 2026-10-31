import KGReferenceVacuumUniqueness
import KGOriginalFieldGeneratorIdentification
import KGRealFieldPoincareWeylCovariance

noncomputable section
set_option maxHeartbeats 2400000
set_option synthInstance.maxHeartbeats 200000
namespace AASCKleinGordon

theorem event_invariant_iff_vacuum_multiple (a : Parameters) (f : FockHilbert a) :
    (∀ b : Spacetime,fockEventTranslation a b f=f) ↔ ∃ z : ℂ,f=z • fockVacuum a := by
  constructor
  · intro hf
    apply time_invariant_is_vacuum_multiple a f
    intro t
    rw [← fockEventTranslation_time]
    exact hf _
  · rintro ⟨z,rfl⟩ b
    rw [map_smul,fockEventTranslation_fixes_vacuum]

theorem poincare_invariant_iff_vacuum_multiple (a : Parameters) (f : FockHilbert a) :
    (∀ (b : Spacetime) (L : ProperLorentzTransform),fockPoincareUnitary a b L f=f) ↔
      ∃ z : ℂ,f=z • fockVacuum a := by
  constructor
  · intro hf
    apply (event_invariant_iff_vacuum_multiple a f).mp
    intro b
    have hh:=hf b 1
    change fockEventTranslation a b (fockLorentzUnitary a 1 f)=f at hh
    rwa [fockLorentzUnitary_one] at hh
  · rintro ⟨z,rfl⟩ b L
    rw [map_smul,fockPoincareUnitary_fixes_vacuum]

theorem normalized_poincare_invariant_is_vacuum_phase (a : Parameters) (f : FockHilbert a)
    (hn : ‖f‖=1)
    (hf : ∀ (b : Spacetime) (L : ProperLorentzTransform),fockPoincareUnitary a b L f=f) :
    ∃ z : ℂ,‖z‖=1 ∧ f=z • fockVacuum a := by
  obtain ⟨z,hz⟩:=(poincare_invariant_iff_vacuum_multiple a f).mp hf
  refine ⟨z,?_,hz⟩
  rw [hz,norm_smul,fockVacuum_norm,mul_one] at hn
  exact hn

theorem original_vacuum_energy_zero_baseline (a : Parameters) :
    ∃ hd : fockVacuum a∈(fockMaximalEnergy a).domain,
      fockMaximalEnergy a ⟨fockVacuum a,hd⟩=0 :=
  time_invariant_mem_energy_kernel a (fockVacuum a) (fockTimeTranslation_fixes_vacuum a)

end AASCKleinGordon
