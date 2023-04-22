import .indep
import mathlib.data.set.basic 

noncomputable theory
open_locale classical
open_locale big_operators


open set

namespace matroid

variables {E : Type*} {M : matroid E} {I J B C X Y : set E} {e f x y : E}

lemma cl_def (M : matroid E) : M.cl X = ⋂₀ {F | M.flat F ∧ X ⊆ F} := rfl

lemma mem_cl_iff_forall_mem_flat : e ∈ M.cl X ↔ ∀ F, M.flat F → X ⊆ F → e ∈ F :=
by simp_rw [cl_def, mem_sInter, mem_set_of_eq, and_imp]

lemma subset_cl (M : matroid E) (X : set E) : X ⊆ M.cl X :=
by simp only [cl_def, subset_sInter_iff, mem_set_of_eq, and_imp, imp_self, implies_true_iff]

@[simp] lemma cl_univ (M : matroid E) : M.cl univ = univ := (subset_univ _).antisymm (M.subset_cl _)

@[simp] lemma cl_cl (M : matroid E) (X : set E) : M.cl (M.cl X) = M.cl X :=
begin
  refine (subset_cl _ _).antisymm' (λ e he, _), 
  rw mem_cl_iff_forall_mem_flat at *, 
  refine λ F hF hXF, he _ hF (λ f hf, _), 
  rw mem_cl_iff_forall_mem_flat at hf, 
  exact hf _ hF hXF, 
end

lemma cl_subset_cl_of_subset (M : matroid E) (h : X ⊆ Y) : M.cl X ⊆ M.cl Y :=
sInter_subset_sInter (λ F hF, ⟨hF.1, h.trans hF.2⟩)

lemma cl_mono (M : matroid E) : monotone M.cl := λ _ _, M.cl_subset_cl_of_subset

lemma cl_subset_cl_of_subset_cl (hXY : X ⊆ M.cl Y) : M.cl X ⊆ M.cl Y :=
by simpa only [cl_cl] using M.cl_subset_cl_of_subset hXY

lemma cl_subset_cl_iff_subset_cl : M.cl X ⊆ M.cl Y ↔ X ⊆ M.cl Y :=
⟨λ h, (M.subset_cl _).trans h, cl_subset_cl_of_subset_cl⟩

lemma subset_cl_of_subset (M : matroid E) (hXY : X ⊆ Y) : X ⊆ M.cl Y := hXY.trans (M.subset_cl Y)

lemma mem_cl_of_mem (M : matroid E) (h : e ∈ X) : e ∈ M.cl X := (M.subset_cl X) h

lemma cl_insert_eq_of_mem_cl (he : e ∈ M.cl X) : M.cl (insert e X) = M.cl X :=
begin
  refine (M.cl_mono (subset_insert _ _)).antisymm' _,
  rw [←M.cl_cl X],
  exact M.cl_subset_cl_of_subset (insert_subset.mpr ⟨he, M.subset_cl _⟩),
end

@[simp] lemma cl_union_cl_right_eq_cl_union (M : matroid E) (X Y : set E) :
  M.cl (X ∪ M.cl Y) = M.cl (X ∪ Y) :=
begin
  refine ((M.cl_mono (union_subset_union_right X (M.subset_cl _)))).antisymm' _,
  rw [←M.cl_cl (X ∪ Y)],
  exact M.cl_mono (union_subset ((subset_union_left _ _).trans (M.subset_cl _))
    (M.cl_mono (subset_union_right _ _))),
end

@[simp] lemma cl_union_cl_left_eq_cl_union (M : matroid E) (X Y : set E) :
  M.cl (M.cl X ∪ Y) = M.cl (X ∪ Y) :=
by rw [union_comm, cl_union_cl_right_eq_cl_union, union_comm]

@[simp] lemma cl_cl_union_cl_eq_cl_union (M : matroid E) (X Y : set E) :
  M.cl (M.cl X ∪ M.cl Y) = M.cl (X ∪ Y) :=
by rw [cl_union_cl_left_eq_cl_union, cl_union_cl_right_eq_cl_union]

@[simp] lemma cl_insert_cl_eq_cl_insert (M : matroid E) (e : E) (X : set E) :
  M.cl (insert e (M.cl X)) = M.cl (insert e X) :=
by simp_rw [←singleton_union, cl_union_cl_right_eq_cl_union]

lemma mem_cl_self (M : matroid E) (e : E) : e ∈ M.cl {e} := (M.subset_cl {e}) (mem_singleton e)

lemma indep.cl_eq_set_of_basis (hI : M.indep I) : M.cl I = {x | M.basis I (insert x I)} :=
begin
  set F := {x | M.basis I (insert x I)} with hF, 
  have hIF : M.basis I F,
  { rw basis_iff, 
    refine ⟨hI, (λ e he, by { rw [hF, mem_set_of, insert_eq_of_mem he], exact hI.basis_self }), 
      λ J hJ hIJ hJF, hIJ.antisymm (λ e he, _)⟩,
    rw basis.eq_of_subset_indep (hJF he) (hJ.subset (insert_subset.mpr ⟨he, hIJ⟩)) 
      (subset_insert _ _) subset.rfl, 
    exact mem_insert _ _ },
  
  have hF : M.flat F, 
  { refine λ J Y hJ hJY y hy, (indep.basis_of_forall_insert hI (subset_insert _ _) (λ e he heI, _)), 
    refine (hIF.transfer hJ (subset_union_right _ _) (hJY.basis_union hJ)).insert_dep
      (mem_of_mem_of_subset he _) heI, 
    rw [diff_subset_iff, union_diff_self, insert_subset], 
    exact ⟨or.inr (or.inl hy), subset_union_left _ _⟩ },
  
  rw [subset_antisymm_iff, cl, subset_sInter_iff], 
  refine ⟨sInter_subset_of_mem ⟨hF, hIF.subset⟩, _⟩, 

  rintro F' ⟨hF',hIF'⟩ e (he : M.basis I (insert e I)), 
  obtain ⟨J, hIJ, hJ⟩ := hI.subset_basis_of_subset hIF', 
  exact (hF' hJ (he.basis_union_of_subset hJ.indep hIJ)) (or.inr (mem_insert _ _)), 
end

lemma indep.mem_cl_iff (hI : M.indep I) : x ∈ M.cl I ↔ (M.indep (insert x I) → x ∈ I) := 
begin
  rw [hI.cl_eq_set_of_basis, mem_set_of_eq], 
  refine ⟨λ h h', _, λ h, hI.basis_of_forall_insert (subset_insert _ _) (λ e he heI, he.2 _)⟩,
  { rw h.eq_of_subset_indep h' (subset_insert _ _) subset.rfl, 
    exact mem_insert _ _ },
  rw [←singleton_union, union_diff_right, mem_diff, mem_singleton_iff] at he,   
  rw [he.1] at heI ⊢, 
  exact h heI, 
end 

lemma indep.mem_cl_iff_of_not_mem (hI : M.indep I) (heI : e ∉ I) : 
  e ∈ M.cl I ↔ ¬M.indep (insert e I) :=
by rw [hI.mem_cl_iff, (iff_false _).mpr heI, imp_false]

lemma indep.not_mem_cl_iff (hI : M.indep I) : x ∉ M.cl I ↔ x ∉ I ∧ M.indep (insert x I) :=
by rw [←not_iff_not, not_not_mem, and_comm, not_and, hI.mem_cl_iff, not_not_mem]

lemma Inter_cl_eq_cl_Inter_of_Union_indep {ι : Type*} (I : ι → set E) (h : M.indep (⋃ i, I i)) :
  (⋂ i, M.cl (I i)) = M.cl (⋂ i, I i) :=
begin  
  have hi : ∀ i, M.indep (I i), from λ i, h.subset (subset_Union _ _), 
  refine subset.antisymm _ (subset_Inter (λ i, M.cl_subset_cl_of_subset (Inter_subset _ _))), 
  rintro e he, rw mem_Inter at he, 
  by_contra h', 
  obtain (hι | ⟨⟨i₀⟩⟩) := (is_empty_or_nonempty ι),
  { haveI := hι, apply h', rw [Inter_of_empty, cl_univ], exact mem_univ _ },
  have hiu : (⋂ i , I i) ⊆ ⋃ i, I i, from 
    ((Inter_subset _ i₀).trans (subset_Union _ i₀)), 
  have hi_inter : M.indep (⋂ i, I i), from (hi i₀).subset (Inter_subset _ _), 
  rw [hi_inter.not_mem_cl_iff, mem_Inter, not_forall] at h', 
  obtain ⟨⟨i₁, hei₁⟩, hei⟩ := h',   

  have hdi₁ : ¬M.indep (insert e (I i₁)), from λ h_ind, hei₁ ((hi i₁).mem_cl_iff.mp (he i₁) h_ind),   
  have heu : e ∉ ⋃ i, I i, from λ he, hdi₁ (h.subset (insert_subset.mpr ⟨he, subset_Union _ _⟩)), 
  
  have hd_all : ∀ i, ¬M.indep (insert e (I i)), 
    from λ i hind, heu (mem_Union_of_mem _ ((hi i).mem_cl_iff.mp (he i) hind)), 
  
  have hb : M.basis (⋃ i, I i) (insert e (⋃ i, I i)), 
  { have h' := (M.cl_subset_cl_of_subset) (subset_Union _ _) (he i₀),
    rwa [h.cl_eq_set_of_basis] at h' },
  
  obtain ⟨I', hI', hssI', hI'ss⟩ := 
    hei.exists_basis_subset_union_basis (insert_subset_insert hiu) hb, 
  
  rw [insert_union, union_eq_right_iff_subset.mpr hiu] at hI'ss, 
  
  have hI'I : I' \ (⋃ i, I i) = {e}, 
  { refine subset.antisymm _ (singleton_subset_iff.mpr ⟨hssI' (mem_insert _ _),heu⟩),
    rwa [diff_subset_iff, union_singleton] }, 
  
  obtain ⟨f, hfI, hf⟩ := hI'.eq_exchange_of_diff_eq_singleton hb hI'I, 

  have hf' : ∀ i, f ∈ I i, 
  { refine λ i, by_contra (λ hfi, (hd_all i (hI'.indep.subset (insert_subset.mpr ⟨_,_⟩)))), 
    { exact hssI' (mem_insert _ _) },
    rw [←diff_singleton_eq_self hfi, diff_subset_iff, singleton_union], 
    exact ((subset_Union _ i).trans_eq hf).trans (diff_subset _ _) },   

  exact hfI.2 (hssI' (or.inr (by rwa mem_Inter))), 
end 

lemma bInter_cl_eq_cl_sInter_of_sUnion_indep (Is : set (set E)) (h : M.indep (⋃₀ Is)) :
  (⋂ I ∈ Is, M.cl I) = M.cl (⋂₀ Is) :=
begin
  rw [sUnion_eq_Union] at h, 
  rw [bInter_eq_Inter, sInter_eq_Inter], 
  exact Inter_cl_eq_cl_Inter_of_Union_indep (λ (x : Is), coe x) h, 
end 

lemma inter_cl_eq_cl_inter_of_union_indep (h : M.indep (I ∪ J)) : M.cl I ∩ M.cl J = M.cl (I ∩ J) :=
begin
  rw [inter_eq_Inter, inter_eq_Inter], rw [union_eq_Union] at h, 
  convert Inter_cl_eq_cl_Inter_of_Union_indep (λ b, cond b I J) (by simpa), 
  ext, cases x; simp, 
end

lemma basis.cl (hIX : M.basis I X) : M.cl I = M.cl X := 
(M.cl_subset_cl_of_subset hIX.subset).antisymm (cl_subset_cl_of_subset_cl 
  (λ x hx, hIX.indep.mem_cl_iff.mpr (λ h, hIX.mem_of_insert_indep hx h)))

lemma basis.mem_cl_iff (hIX : M.basis I X) : 
  e ∈ M.cl X ↔ (M.indep (insert e I) → e ∈ I) := 
by rw [←hIX.cl, hIX.indep.mem_cl_iff]
 
lemma basis.mem_cl_iff_of_not_mem (hIX : M.basis I X) (he : e ∉ X) : 
  e ∈ M.cl X ↔ ¬M.indep (insert e I) :=
by { rw [hIX.mem_cl_iff], exact ⟨λ h h', he (hIX.subset (h h')), λ h h', (h h').elim⟩ }

lemma basis.subset_cl (hI : M.basis I X) : X ⊆ M.cl I := by { rw hI.cl, exact M.subset_cl X }  

lemma indep.basis_cl (hI : M.indep I) : M.basis I (M.cl I) :=
begin
  refine hI.basis_of_forall_insert (M.subset_cl _) (λ e he heI, he.2 _), 
  rw [mem_diff, hI.mem_cl_iff] at he, 
  exact he.1 heI, 
end 

lemma cl_eq_set_of_indep_not_indep (M : matroid E) (X : set E) : 
  M.cl X = X ∪ {e | ∃ I ⊆ X, M.indep I ∧ ¬M.indep (insert e I)} := 
begin
  refine subset_antisymm (λ e he, ((em (e ∈ X)).elim or.inl (λ heX, or.inr _ ))) 
    (union_subset (M.subset_cl X) _), 
  { obtain ⟨I, hI⟩ := M.exists_basis X, 
    refine ⟨I, hI.subset, hI.indep, _⟩,
    refine hI.indep.basis_cl.dep_of_ssubset (ssubset_insert (not_mem_subset hI.subset heX)) 
      (insert_subset.mpr ⟨by rwa hI.cl,M.subset_cl I⟩) },  
  rintro e ⟨I, hIX, hI, hIe⟩, 
  refine (M.cl_subset_cl_of_subset hIX) _, 
  rw [hI.mem_cl_iff], 
  exact λ h, (hIe h).elim,  
end     

lemma indep.basis_of_subset_cl (hI : M.indep I) (hIX : I ⊆ X) (h : X ⊆ M.cl I) : M.basis I X :=
hI.basis_cl.basis_subset hIX h
 
lemma indep.base_of_cl_eq_univ (hI : M.indep I) (h : M.cl I = univ) : M.base I :=
by { rw base_iff_basis_univ, refine hI.basis_of_subset_cl (subset_univ _) (by rw h) }

lemma basis.basis_cl (hI : M.basis I X) : M.basis I (M.cl X) :=
by { rw [←hI.cl], exact hI.indep.basis_cl }

lemma basis_iff_basis_cl_of_subset (hIX : I ⊆ X) : M.basis I X ↔ M.basis I (M.cl X) :=
⟨λ h, h.basis_cl,λ h, h.basis_subset hIX (subset_cl _ _)⟩

lemma basis.basis_of_cl_eq_cl (hI : M.basis I X) (hY : I ⊆ Y) (h : M.cl X = M.cl Y) : M.basis I Y :=
by { rw [basis_iff_basis_cl_of_subset hY, ←h], exact hI.basis_cl }

lemma base.cl (hB : M.base B) : M.cl B = univ :=
by { rw [(base_iff_basis_univ.mp hB).cl], exact eq_univ_of_univ_subset (M.subset_cl _) }

lemma base.cl_of_supset (hB : M.base B) (hBX : B ⊆ X) : M.cl X = univ :=
eq_univ_of_univ_subset (subset_trans (by rw hB.cl) (M.cl_mono hBX))
  
lemma base_subset_iff_cl_eq_univ : (∃ B ⊆ X, M.base B) ↔ M.cl X = univ :=
begin
  refine ⟨λ ⟨B,hBX,hB⟩, hB.cl_of_supset hBX, λ h, _⟩, 
  obtain ⟨B, hBX⟩ := M.exists_basis X, 
  use [B, hBX.subset],
  rw [base_iff_basis_univ, ←h, ←hBX.cl] , 
  exact hBX.indep.basis_cl, 
end

lemma mem_cl_insert (he : e ∉ M.cl X) (hef : e ∈ M.cl (insert f X)) : f ∈ M.cl (insert e X) :=
begin
  have hf : f ∉ M.cl X, 
  { exact λ hf, he (by rwa ←cl_insert_eq_of_mem_cl hf) }, 
  
  obtain ⟨I, hI⟩ := M.exists_basis X, 
  rw [←hI.cl, hI.indep.not_mem_cl_iff] at he hf, 
  have he' := hI.insert_basis_insert he.2, 
  rw [←he'.cl, he'.indep.mem_cl_iff, mem_insert_iff] , 
  have hf' := hI.insert_basis_insert hf.2, 
  rw [←hf'.cl, hf'.indep.mem_cl_iff, insert_comm, mem_insert_iff] at hef, 
  intro h', 
  obtain (rfl | heI) := hef h', 
  { exact or.inl rfl },
  exact (he.1 heI).elim, 
end

lemma cl_exchange (he : e ∈ M.cl (insert f X) \ M.cl X ) : f ∈ M.cl (insert e X) \ M.cl X :=
begin
  refine ⟨mem_cl_insert he.2 he.1, λ hf, _ ⟩,
  rw [cl_insert_eq_of_mem_cl hf, diff_self] at he,
  exact not_mem_empty _ he,
end

lemma cl_exchange_iff : e ∈ M.cl (insert f X) \ M.cl X ↔ f ∈ M.cl (insert e X) \ M.cl X :=
⟨cl_exchange, cl_exchange⟩

lemma cl_diff_singleton_eq_cl (h : e ∈ M.cl (X \ {e})) : M.cl (X \ {e}) = M.cl X :=
begin
  refine (M.cl_mono (diff_subset _ _)).antisymm _,
  have h' := M.cl_mono (insert_subset.mpr ⟨h, (M.subset_cl _ )⟩),
  rw [insert_diff_singleton, cl_cl] at h',
  exact (M.cl_mono (subset_insert _ _)).trans h',
end

lemma mem_cl_diff_singleton_iff_cl (he : e ∈ X) :
  e ∈ M.cl (X \ {e}) ↔ M.cl (X \ {e}) = M.cl X :=
⟨cl_diff_singleton_eq_cl, λ h, by {rw h, exact subset_cl _ _ he}⟩

lemma indep_iff_cl_diff_ne_forall :
  M.indep I ↔ ∀ e ∈ I, M.cl (I \ {e}) ≠ M.cl I :=
begin
  refine ⟨λ h e heI h_eq, _,λ h, _⟩, 
  { have h' := (h.diff {e}).basis_cl, 
    rw [h_eq] at h', 
    have h'' := h'.mem_of_insert_indep (M.subset_cl _ heI), 
    simp_rw [insert_diff_singleton, mem_diff, mem_singleton, not_true, and_false, 
      insert_eq_of_mem heI] at h'', 
    exact h'' h },
  obtain ⟨J, hJ⟩ := M.exists_basis I, 
  convert hJ.indep,
  refine hJ.subset.antisymm' (λ e he, by_contra (λ heJ, _)), 
  have hJIe : J ⊆ I \ {e}, from subset_diff_singleton hJ.subset heJ, 
  have hcl := h e he, 
  rw [ne.def, ←mem_cl_diff_singleton_iff_cl he] at hcl, 
  have hcl' := not_mem_subset (M.cl_mono hJIe) hcl, 
  rw [hJ.cl] at hcl', 
  exact hcl' (M.subset_cl I he), 
end

lemma indep_iff_not_mem_cl_diff_forall : M.indep I ↔ ∀ e ∈ I, e ∉ M.cl (I \ {e}) :=
begin
  rw indep_iff_cl_diff_ne_forall,
  exact ⟨λ h, λ x hxI, by {rw mem_cl_diff_singleton_iff_cl hxI, exact h x hxI },
    λ h x hxI, by {rw [ne.def, ←mem_cl_diff_singleton_iff_cl hxI], exact h x hxI }⟩,
end

lemma indep_iff_cl_ssubset_ssubset_forall : M.indep I ↔ ∀ J ⊂ I, M.cl J ⊂ M.cl I :=
begin
  refine ⟨λ hI J hJI, _,
    λ h, indep_iff_cl_diff_ne_forall.mpr (λ x hx, (h _ $ diff_singleton_ssubset.2 hx).ne)⟩,
  obtain ⟨e,heI,heJ⟩ := exists_of_ssubset hJI,
  exact (M.cl_subset_cl_of_subset (subset_diff_singleton hJI.subset heJ)).trans_ssubset
    ((M.cl_subset_cl_of_subset (diff_subset I {e})).ssubset_of_ne
    (indep_iff_cl_diff_ne_forall.mp hI e heI)),
end

lemma indep.insert_indep_iff_of_not_mem (hI : M.indep I) (he : e ∉ I) :
  M.indep (insert e I) ↔ e ∉ M.cl I :=
⟨λ h, hI.not_mem_cl_iff.mpr ⟨he,h⟩, λ h, (hI.not_mem_cl_iff.mp h).2⟩

lemma indep.cl_diff_singleton_ssubset (hI : M.indep I) (he : e ∈ I) : M.cl (I \ {e}) ⊂  M.cl I :=
ssubset_of_subset_of_ne (M.cl_mono (diff_subset _ _)) (indep_iff_cl_diff_ne_forall.mp hI _ he)

lemma indep.cl_ssubset_ssubset (hI : M.indep I) (hJI : J ⊂ I) : M.cl J ⊂ M.cl I :=
indep_iff_cl_ssubset_ssubset_forall.mp hI J hJI

lemma basis_iff_cl : M.basis I X ↔ I ⊆ X ∧ X ⊆ M.cl I ∧ ∀ J ⊆ I, X ⊆ M.cl J → J = I :=
begin
  split, 
  { refine λ h, ⟨h.subset, h.subset_cl, λ J hJI hXJ, hJI.antisymm (λ e heI, _)⟩, 
    rw [(h.indep.subset hJI).cl_eq_set_of_basis] at hXJ, 
    exact (h.subset.trans hXJ heI : M.basis _ _).mem_of_insert_indep (mem_insert _ _) 
      (h.indep.subset (insert_subset.mpr ⟨heI, hJI⟩)) },
  rintro ⟨hIX, hXI, hmin⟩,  
  refine indep.basis_of_forall_insert _ hIX _, 
  { rw indep_iff_cl_diff_ne_forall,
    intros e he hecl,
    rw ← hmin _ (diff_subset _ _) (hXI.trans_eq hecl.symm) at he, 
    exact he.2 (mem_singleton e) },
  
  exact λ e he hi, he.2 
    (((hi.subset (subset_insert _ _)).basis_cl).mem_of_insert_indep (hXI (he.1)) hi)
end

lemma basis_union_iff_indep_cl : M.basis I (I ∪ X) ↔ M.indep I ∧ X ⊆ M.cl I :=
begin
  refine ⟨λ h, ⟨h.indep, (subset_union_right _ _).trans h.subset_cl⟩, _⟩,
  rw basis_iff_cl,
  rintros ⟨hI, hXI⟩,
  refine ⟨subset_union_left _ _, union_subset (M.subset_cl _) hXI, λ J hJI hJ, by_contra (λ h', _)⟩,
  obtain ⟨e,heI,heJ⟩ := exists_of_ssubset (hJI.ssubset_of_ne h'),
  have heJ' : e ∈ M.cl J,
    from hJ (or.inl heI),
  refine indep_iff_not_mem_cl_diff_forall.mp hI e heI (mem_of_mem_of_subset heJ' _),
  exact M.cl_subset_cl_of_subset (subset_diff_singleton hJI heJ),
end

lemma basis_iff_indep_cl : M.basis I X ↔ M.indep I ∧ X ⊆ M.cl I ∧ I ⊆ X :=
⟨λ h, ⟨h.indep, h.subset_cl, h.subset⟩,
  λ h, (basis_union_iff_indep_cl.mpr ⟨h.1,h.2.1⟩).basis_subset h.2.2 (subset_union_right _ _)⟩

lemma basis.eq_of_cl_subset (hI : M.basis I X) (hJI : J ⊆ I) (hJ : X ⊆ M.cl J) : J = I :=
(basis_iff_cl.mp hI).2.2 J hJI hJ

lemma empty_basis_iff : M.basis ∅ X ↔ X ⊆ M.cl ∅ :=
begin
  simp only [basis_iff_cl, empty_subset, true_and, and_iff_left_iff_imp],
  exact λ h J hJ hXJ, subset_empty_iff.mp hJ,
end

lemma eq_of_cl_eq_cl_forall {M₁ M₂ : matroid E} (h : ∀ X, M₁.cl X = M₂.cl X) : M₁ = M₂ :=
eq_of_indep_iff_indep_forall (λ I, by simp_rw [indep_iff_cl_diff_ne_forall, h])

end matroid

section from_axioms

variables {E : Type*} 

lemma cl_diff_singleton_eq_cl (cl : set E → set E) (subset_cl : ∀ X, X ⊆ cl X)
(cl_mono : ∀ X Y, X ⊆ Y → cl X ⊆ cl Y) (cl_idem : ∀ X, cl (cl X) = cl X )
{x : E} {I : set E} (h : x ∈ cl (I \ {x})) :
  cl (I \ {x}) = cl I :=
begin
  refine (cl_mono _ _ (diff_subset _ _)).antisymm _,
  have h' := cl_mono _ _ (insert_subset.mpr ⟨h, (subset_cl _ )⟩),
  rw [insert_diff_singleton, cl_idem] at h',
  exact (cl_mono _ _ (subset_insert _ _)).trans h',
end

/-- A set is independent relative to a closure function if none of its elements are contained in 
  the closure of their removal -/
def cl_indep (cl : set E → set E) (I : set E) : Prop := ∀ e ∈ I, e ∉ cl (I \ {e})   

lemma cl_indep_mono {cl : set E → set E} (cl_mono : ∀ ⦃X Y⦄, X ⊆ Y → cl X ⊆ cl Y) {I J : set E} 
(hJ : cl_indep cl J) (hIJ : I ⊆ J) :
  cl_indep cl I :=
(λ e heI hecl, hJ e (hIJ heI) (cl_mono (diff_subset_diff_left hIJ) hecl))

lemma cl_indep_aux {e : E} {I : set E} {cl : set E → set E} 
(cl_exchange : ∀ (X e f), f ∈ cl (insert e X) \ cl X → e ∈ cl (insert f X) \ cl X ) 
(h : cl_indep cl I) (heI : ¬cl_indep cl (insert e I)) : 
e ∈ cl I :=
begin
  have he : e ∉ I, by { intro he, rw [insert_eq_of_mem he] at heI, exact heI h },
  rw [cl_indep] at heI, push_neg at heI, 
  obtain ⟨f, ⟨(rfl | hfI), hfcl⟩⟩ := heI, 
  { rwa [insert_diff_self_of_not_mem he] at hfcl },
  have hne : e ≠ f, by { rintro rfl, exact he hfI }, 
  rw [←insert_diff_singleton_comm hne] at hfcl, 
  convert (cl_exchange (I \ {f}) e f ⟨hfcl,h f hfI⟩).1, 
  rw [insert_diff_singleton, insert_eq_of_mem hfI],  
end   

/-- If the closure axioms hold, then `cl`-independence gives rise to a matroid -/
def matroid_of_cl (cl : set E → set E) (subset_cl : ∀ X, X ⊆ cl X)
(cl_mono : ∀ ⦃X Y⦄, X ⊆ Y → cl X ⊆ cl Y) (cl_idem : ∀ X, cl (cl X) = cl X )
(cl_exchange : ∀ (X e f), f ∈ cl (insert e X) \ cl X → e ∈ cl (insert f X) \ cl X ) 
(cl_indep_maximal : ∀ ⦃I X⦄, cl_indep cl I → I ⊆ X  → 
    (maximals (⊆) {J | cl_indep cl J ∧ I ⊆ J ∧ J ⊆ X }).nonempty) :
matroid E := 
matroid_of_indep (cl_indep cl) 
(λ e he _, not_mem_empty _ he) (λ I J hJ hIJ, cl_indep_mono cl_mono hJ hIJ)
(begin
  refine λ I I' hI hIn hI'm, _, 
  obtain ⟨B, hB⟩ := cl_indep_maximal hI (subset_union_left I I'), 
  have hB' : B ∈ maximals (⊆) {J | cl_indep cl J},  
  { refine ⟨hB.1.1,(λ B' hB' hBB' e heB', by_contra (λ heB, _) )⟩,
    have he' : e ∈ cl I', 
    { refine (em (e ∈ I')).elim (λ heI', (subset_cl I') heI') 
        (λ heI', cl_indep_aux cl_exchange hI'm.1 (λ hi, _)), 
      exact heI' (hI'm.2 hi (subset_insert e _) (mem_insert e _)) },
      have hI'B : I' ⊆ cl B, 
    { refine λ f hf, (em (f ∈ B)).elim (λ h', subset_cl B h') 
        (λ hfB', cl_indep_aux cl_exchange hB.1.1 (λ hi, hfB' _)),  
      
      refine hB.2 ⟨hi,hB.1.2.1.trans (subset_insert _ _),_⟩ (subset_insert _ _) (mem_insert _ _), 
      exact insert_subset.mpr ⟨or.inr hf,hB.1.2.2⟩ }, 
    have heBcl := (cl_idem B).subset ((cl_mono hI'B) he'), 
    refine cl_indep_mono cl_mono hB' (insert_subset.mpr ⟨heB', hBB'⟩) e (mem_insert _ _) _,
    rwa [insert_diff_of_mem _ (mem_singleton e), diff_singleton_eq_self heB] },
  obtain ⟨f,hfB,hfI⟩ := exists_of_ssubset 
    (hB.1.2.1.ssubset_of_ne (by { rintro rfl, exact hIn hB' })), 
  refine ⟨f, ⟨_, hfI⟩, cl_indep_mono cl_mono hB.1.1 (insert_subset.mpr ⟨hfB,hB.1.2.1⟩)⟩,    
  exact or.elim (hB.1.2.2 hfB) (false.elim ∘ hfI) id, 
end)
(λ I X hI hIX, cl_indep_maximal hI hIX)
 
lemma cl_indep_cl_eq {cl : set E → set E }
  (subset_cl : ∀ X, X ⊆ cl X )
  (cl_mono : ∀ ⦃X Y⦄, X ⊆ Y → cl X ⊆ cl Y )
  (cl_idem : ∀ X, cl (cl X) = cl X )
  (cl_exchange : ∀ (X e f), f ∈ cl (insert e X) \ cl X → e ∈ cl (insert f X) \ cl X ) 
  (cl_indep_maximal : ∀ ⦃I X⦄, cl_indep cl I → I ⊆ X →  
    (maximals (⊆) {J | cl_indep cl J ∧ I ⊆ J ∧ J ⊆ X }).nonempty ) (X : set E) :
cl X = X ∪ {e | ∃ I ⊆ X, cl_indep cl I ∧ ¬cl_indep cl (insert e I) }  :=
begin
  ext f, 
  refine ⟨λ h, (em (f ∈ X)).elim or.inl (λ hf, or.inr _), 
    λ h, or.elim h (λ g, subset_cl X g) _⟩, 
  { have hd : ¬ (cl_indep cl (insert f X)), 
    { refine λ hi, hi f (mem_insert _ _) _, convert h, 
      rw [insert_diff_of_mem _ (mem_singleton f), diff_singleton_eq_self hf] },
    obtain ⟨I, hI⟩ := cl_indep_maximal (λ e he h', not_mem_empty _ he) (empty_subset X), 
    have hXI : X ⊆ cl I,  
    { refine λ x hx, (em (x ∈ I)).elim (λ h', subset_cl _ h') (λ hxI, _),
      refine cl_indep_aux cl_exchange hI.1.1 (λ hi, hxI _),  
      refine hI.2 ⟨hi, empty_subset (insert x I), _⟩ (subset_insert x _) (mem_insert _ _), 
      exact insert_subset.mpr ⟨hx, hI.1.2.2⟩ },
    have hfI : f ∈ cl I, from (cl_mono (hXI)).trans_eq (cl_idem I) h,
    refine ⟨I, hI.1.2.2, hI.1.1, λ hi, hf (hi f (mem_insert f _) _).elim⟩,
    rwa [insert_diff_of_mem _ (mem_singleton f), diff_singleton_eq_self],  
    exact not_mem_subset hI.1.2.2 hf },
  rintro ⟨I, hIX, hI, hfI⟩, 
  exact (cl_mono hIX) (cl_indep_aux cl_exchange hI hfI), 
end 

@[simp] lemma matroid_of_cl_apply {cl : set E → set E} (subset_cl : ∀ X, X ⊆ cl X)
(cl_mono : ∀ ⦃X Y⦄, X ⊆ Y → cl X ⊆ cl Y) (cl_idem : ∀ X, cl (cl X) = cl X)
(cl_exchange : ∀ (X e f), f ∈ cl (insert e X) \ cl X → e ∈ cl (insert f X) \ cl X) 
(cl_indep_maximal : ∀ ⦃I X⦄, cl_indep cl I → I ⊆ X →   
    (maximals (⊆) {J | cl_indep cl J ∧ I ⊆ J ∧ J ⊆ X }).nonempty) :
(matroid_of_cl cl subset_cl cl_mono cl_idem cl_exchange cl_indep_maximal).cl = cl :=
begin
  ext1 X,
  rw [(cl_indep_cl_eq subset_cl cl_mono cl_idem cl_exchange cl_indep_maximal X : cl X = _), 
    matroid_of_cl, matroid.cl_eq_set_of_indep_not_indep], 
  simp, 
end 

@[simp] lemma matroid_of_cl_indep_iff {cl : set E → set E} (subset_cl : ∀ X, X ⊆ cl X)
(cl_mono : ∀ ⦃X Y⦄, X ⊆ Y → cl X ⊆ cl Y) (cl_idem : ∀ X, cl (cl X) = cl X)
(cl_exchange : ∀ (X e f), f ∈ cl (insert e X) \ cl X → e ∈ cl (insert f X) \ cl X) 
(cl_indep_maximal : ∀ ⦃I X⦄, cl_indep cl I → I ⊆ X →   
    (maximals (⊆) {J | cl_indep cl J ∧ I ⊆ J ∧ J ⊆ X }).nonempty) {I : set E}:
(matroid_of_cl cl subset_cl cl_mono cl_idem cl_exchange cl_indep_maximal).indep I ↔ cl_indep cl I :=
by rw [matroid_of_cl, matroid_of_indep_apply]

/-- The maximality axiom isn't needed if all independent sets are at most some fixed size. -/
def matroid_of_cl_of_indep_bounded (cl : set E → set E)
  (subset_cl : ∀ X, X ⊆ cl X )
  (cl_mono : ∀ ⦃X Y⦄, X ⊆ Y → cl X ⊆ cl Y )
  (cl_idem : ∀ X, cl (cl X) = cl X )
  (cl_exchange : ∀ (X e f), f ∈ cl (insert e X) \ cl X → e ∈ cl (insert f X) \ cl X )  
  (n : ℕ) (hn : ∀ I, cl_indep cl I → I.finite ∧ I.ncard ≤ n) :
matroid E := matroid_of_cl cl subset_cl cl_mono cl_idem cl_exchange
(exists_maximal_subset_property_of_bounded ⟨n, hn⟩)

@[simp] lemma matroid_of_cl_of_indep_bounded_apply (cl : set E → set E) (subset_cl : ∀ X, X ⊆ cl X )
(cl_mono : ∀ ⦃X Y⦄, X ⊆ Y → cl X ⊆ cl Y) (cl_idem : ∀ X, cl (cl X) = cl X )
(cl_exchange : ∀ (X e f), f ∈ cl (insert e X) \ cl X → e ∈ cl (insert f X) \ cl X )  
(n : ℕ) (hn : ∀ I, cl_indep cl I → I.finite ∧ I.ncard ≤ n) : 
(matroid_of_cl_of_indep_bounded cl subset_cl cl_mono cl_idem cl_exchange n hn).cl = cl := 
by simp [matroid_of_cl_of_indep_bounded]

instance (cl : set E → set E) (subset_cl : ∀ X, X ⊆ cl X )
(cl_mono : ∀ ⦃X Y⦄, X ⊆ Y → cl X ⊆ cl Y) (cl_idem : ∀ X, cl (cl X) = cl X )
(cl_exchange : ∀ (X e f), f ∈ cl (insert e X) \ cl X → e ∈ cl (insert f X) \ cl X )  
(n : ℕ) (hn : ∀ I, cl_indep cl I → I.finite ∧ I.ncard ≤ n) :
matroid.finite_rk (matroid_of_cl_of_indep_bounded cl subset_cl cl_mono cl_idem cl_exchange n hn) 
:= 
begin
  obtain ⟨B, h⟩ := 
    (matroid_of_cl_of_indep_bounded cl subset_cl cl_mono cl_idem cl_exchange n hn).exists_base, 
  refine h.finite_rk_of_finite (hn _ _).1, 
  simp_rw [matroid_of_cl_of_indep_bounded, matroid_of_cl, matroid.base_iff_maximal_indep, 
    matroid_of_indep_apply] at h, 
  exact h.1, 
end 

/-- A finite matroid as defined by the closure axioms. -/
def matroid_of_cl_of_finite [finite E] (cl : set E → set E) (subset_cl : ∀ X, X ⊆ cl X )
(cl_mono : ∀ ⦃X Y⦄, X ⊆ Y → cl X ⊆ cl Y) (cl_idem : ∀ X, cl (cl X) = cl X)
(cl_exchange : ∀ (X e f), f ∈ cl (insert e X) \ cl X → e ∈ cl (insert f X) \ cl X) : 
matroid E   :=
matroid_of_cl_of_indep_bounded cl subset_cl cl_mono cl_idem cl_exchange (nat.card E)
(λ I hI, ⟨to_finite _, by { rw [←ncard_univ], exact ncard_le_of_subset (subset_univ _) }⟩) 
 
@[simp] lemma matroid_of_cl_of_finite_apply [finite E] (cl : set E → set E) 
(subset_cl : ∀ X, X ⊆ cl X )
(cl_mono : ∀ ⦃X Y⦄, X ⊆ Y → cl X ⊆ cl Y) (cl_idem : ∀ X, cl (cl X) = cl X)
(cl_exchange : ∀ (X e f), f ∈ cl (insert e X) \ cl X → e ∈ cl (insert f X) \ cl X) :
(matroid_of_cl_of_finite cl subset_cl cl_mono cl_idem cl_exchange).cl = cl :=
by simp [matroid_of_cl_of_finite] 



end from_axioms