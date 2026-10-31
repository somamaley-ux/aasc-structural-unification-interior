import KGSchwartzCoordinates
import Mathlib.Analysis.LocallyConvex.WithSeminorms

/-! The locally convex direct-sum topology on the ORIGINAL algebraic core.
Its generating seminorms are precisely those whose restrictions to every
Schwartz sector are continuous. The universal continuity theorem below is
proved from that topology, not provided as a certificate. -/
noncomputable section
open scoped SchwartzMap DirectSum
namespace AASCKleinGordon

def CoreSeminormIndex := {p : Seminorm ℂ FiniteParticleCore //
  ∀ n, Continuous (p.comp (DirectSum.lof ℂ ℕ (fun n => bosonicSchwartz n) n))}

def coreSeminormFamily : CoreSeminormIndex → Seminorm ℂ FiniteParticleCore := Subtype.val

instance finiteParticleCoreTopology : TopologicalSpace FiniteParticleCore :=
  (SeminormFamily.moduleFilterBasis coreSeminormFamily).topology

theorem finiteParticleCore_withSeminorms : WithSeminorms coreSeminormFamily := ⟨rfl⟩

instance finiteParticleCore_topologicalAddGroup : IsTopologicalAddGroup FiniteParticleCore :=
  finiteParticleCore_withSeminorms.topologicalAddGroup

instance finiteParticleCore_continuousSMul : ContinuousSMul ℂ FiniteParticleCore :=
  finiteParticleCore_withSeminorms.continuousSMul

instance finiteParticleCore_locallyConvex : LocallyConvexSpace ℝ FiniteParticleCore :=
  finiteParticleCore_withSeminorms.toLocallyConvexSpace

theorem finiteParticleCore_lof_continuous (n : ℕ) :
    Continuous (DirectSum.lof ℂ ℕ (fun n => bosonicSchwartz n) n) := by
  apply Seminorm.continuous_of_continuous_comp finiteParticleCore_withSeminorms
  intro p
  exact p.property n

theorem core_continuous_seminorm_of_sector_continuous (p : Seminorm ℂ FiniteParticleCore)
    (hp : ∀ n, Continuous (p.comp (DirectSum.lof ℂ ℕ (fun n => bosonicSchwartz n) n))) :
    Continuous p := finiteParticleCore_withSeminorms.continuous_seminorm ⟨p,hp⟩

theorem core_linearMap_continuous_iff {W : Type*} [AddCommGroup W] [Module ℂ W]
    [TopologicalSpace W] {ι : Type*} (q : ι → Seminorm ℂ W) (hq : WithSeminorms q)
    (L : FiniteParticleCore →ₗ[ℂ] W) :
    Continuous L ↔ ∀ n, Continuous (L.comp (DirectSum.lof ℂ ℕ (fun n => bosonicSchwartz n) n)) := by
  constructor
  · intro h n
    exact h.comp (finiteParticleCore_lof_continuous n)
  · intro h
    apply Seminorm.continuous_of_continuous_comp hq
    intro i
    apply core_continuous_seminorm_of_sector_continuous
    intro n
    exact (hq.continuous_seminorm i).comp (h n)

theorem core_normed_linearMap_continuous_iff {W : Type*} [NormedAddCommGroup W]
    [NormedSpace ℂ W] (L : FiniteParticleCore →ₗ[ℂ] W) :
    Continuous L ↔ ∀ n, Continuous (L.comp (DirectSum.lof ℂ ℕ (fun n => bosonicSchwartz n) n)) :=
  core_linearMap_continuous_iff _ (norm_withSeminorms ℂ W) L

end AASCKleinGordon
