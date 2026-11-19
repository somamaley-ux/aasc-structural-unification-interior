import LinePacket

namespace AASCLinePacket

def rank (p : Site) := p.1+p.2

private theorem rank_step (p : Site) (d : Dir) : rank (next d p) = rank p+1 := by
  cases p; cases d <;> simp [rank,next] <;> omega

/-- Every actually surviving packet reaches a given event in the same number
of primitive registered acts, for every controller and every intermediate
deformation which permits that endpoint. -/
theorem native_stage_count (cs : List Control) (p q : Site) (m n : Mask)
    (arrive : run cs (some (p,m)) = some (q,n)) :
    rank q = rank p+cs.length := by
  induction cs generalizing p q m n with
  | nil =>
    exact (congrArg (fun w : Site × Mask => rank w.1) (Option.some.inj arrive)).symm
  | cons c cs ih =>
    change run cs (advance c (some (p,m))) = some (q,n) at arrive
    unfold advance at arrive
    dsimp only at arrive
    split at arrive
    · have h := ih _ _ _ _ arrive
      rw [rank_step] at h
      simp only [List.length_cons]
      omega
    · rw [no_recreation] at arrive; contradiction

/-- Immediate physical future means strictly reachable with no distinct
intermediate reachable event. -/
def Immediate (p q : Site) : Prop := CompleteAccess p q ∧ p ≠ q ∧
    ∀ r, CompleteAccess p r → CompleteAccess r q → r=p ∨ r=q

theorem reconstruct_native_neighbors (p q : Site) :
    Immediate p q ↔ q=next .right p ∨ q=next .left p := by
  rcases p with ⟨u,v⟩
  rcases q with ⟨x,y⟩
  simp only [Immediate,complete_access_exact,Prod.mk_le_mk,Prod.mk.injEq,next]
  constructor
  · rintro ⟨⟨hx,hy⟩,ne,between⟩
    by_cases e : u=x
    · subst x
      have vy : v<y := lt_of_le_of_ne hy (fun h => ne (by subst y; rfl))
      have h := between (u,v+1) ⟨le_rfl,by omega⟩ ⟨le_rfl,by omega⟩
      rcases h with h | h
      · have z := congrArg Prod.snd h; simp at z
      · exact Or.inr ⟨rfl,(congrArg Prod.snd h).symm⟩
    · have h := between (u+1,v) ⟨by omega,le_rfl⟩ ⟨by omega,hy⟩
      rcases h with h | h
      · have z := congrArg Prod.fst h; simp at z
      · exact Or.inl ⟨(congrArg Prod.fst h).symm,(congrArg Prod.snd h).symm⟩
  · rintro (⟨rfl,rfl⟩ | ⟨rfl,rfl⟩)
    all_goals
      refine ⟨⟨by omega,by omega⟩,by simp,?_⟩
      rintro ⟨a,b⟩ ⟨_,_⟩ ⟨_,_⟩
      simp only [Prod.mk.injEq]
      omega

end AASCLinePacket
