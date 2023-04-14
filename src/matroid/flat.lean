import .indep
import mathlib.data.set.basic 

noncomputable theory
open_locale classical
open_locale big_operators


/-
  Flats and closure.
  
  TODO : Flats are a `modular_lattice`
-/

open set

namespace matroid

variables {E : Type*} {M M₁ M₂ : matroid E}
  {I I₁ I₂ B₁ B₂ J B C X Y Z F F₀ F₁ F₂ H H₁ H₂ : set E} {e f x y z : E}

lemma flat_def : M.flat F ↔ ∀ I X, M.basis I F → M.basis I X → X ⊆ F := iff.rfl

lemma flat.Inter {ι : Type*} (F : ι → set E) (hF : ∀ i, M.flat (F i)) : M.flat (⋂ i, F i) :=
begin
  refine λ I X hI hIX, subset_Inter (λ i, _), 
  obtain ⟨J, hJ, hIJ⟩ := hI.indep.subset_basis_of_subset 
    (hI.subset.trans (Inter_subset _ _ ) : I ⊆ F i), 
  refine (union_subset_iff.mp (@hF i _ (F i ∪ X) hIJ _)).2, 
  rw [←union_eq_left_iff_subset.mpr hIJ.subset, union_assoc], 
  exact hIJ.basis_union (hIX.basis_union_of_subset hIJ.indep hJ),  
end

lemma flat.inter (hF₁ : M.flat F₁) (hF₂ : M.flat F₂) : M.flat (F₁ ∩ F₂) :=
by { rw inter_eq_Inter, refine flat.Inter _ (λ i, _), cases i; assumption }

lemma univ_flat (M : matroid E) : M.flat univ := 
by { convert @flat.Inter _ M empty empty.elim (λ i, empty.elim i), simp }

lemma cl_def (M : matroid E) : M.cl X = ⋂₀ {F | M.flat F ∧ X ⊆ F} := rfl

lemma mem_cl_iff_forall_mem_flat : e ∈ M.cl X ↔ ∀ F, M.flat F → X ⊆ F → e ∈ F :=
by simp_rw [cl_def, mem_sInter, mem_set_of_eq, and_imp]

lemma flat_of_cl (M : matroid E) (X : set E) : M.flat (M.cl X) :=
by { rw [cl_def, sInter_eq_Inter], refine flat.Inter _ _, rintro ⟨F,hF⟩, exact hF.1 }
 
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


lemma flat_iff_cl_self : M.flat F ↔ M.cl F = F := 
⟨λ h, subset_antisymm (sInter_subset_of_mem ⟨h, subset.rfl⟩) (M.subset_cl _),
  λ h, by {rw ←h, exact flat_of_cl _ _ }⟩ 

lemma flat.cl (hF : M.flat F) : M.cl F = F := flat_iff_cl_self.mp hF 

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

lemma bInter_cl_eq_cl_bInter_of_sUnion_indep (Is : set (set E)) (h : M.indep (⋃₀ Is)) :
  (⋂ I ∈ Is, M.cl I) = M.cl (⋂ I ∈ Is, I) :=
begin
  rw [sUnion_eq_Union] at h, 
  rw [bInter_eq_Inter, bInter_eq_Inter], 
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

lemma basis.subset_cl (hI : M.basis I X) : X ⊆ M.cl I := by { rw hI.cl, exact M.subset_cl X }

lemma indep.basis_cl (hI : M.indep I) : M.basis I (M.cl I) :=
begin
  refine hI.basis_of_forall_insert (M.subset_cl _) (λ e he heI, he.2 _), 
  rw [mem_diff, hI.mem_cl_iff] at he, 
  exact he.1 heI, 
end 

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

lemma indep_iff_not_mem_cl_diff_forall :
  M.indep I ↔ ∀ e ∈ I, e ∉ M.cl (I \ {e}) :=
begin
  rw indep_iff_cl_diff_ne_forall,
  exact ⟨λ h, λ x hxI, by {rw mem_cl_diff_singleton_iff_cl hxI, exact h x hxI },
    λ h x hxI, by {rw [ne.def, ←mem_cl_diff_singleton_iff_cl hxI], exact h x hxI }⟩,
end

lemma indep_iff_cl_ssubset_ssubset_forall :
  M.indep I ↔ ∀ J ⊂ I, M.cl J ⊂ M.cl I :=
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

lemma flat_iff_ssubset_cl_insert_forall : M.flat F ↔ ∀ e ∉ F, M.cl F ⊂ M.cl (insert e F) :=
begin
  refine ⟨λ h e he, (M.cl_subset_cl_of_subset (subset_insert _ _)).ssubset_of_ne _, λ h, _⟩,
  { rw [h.cl], exact λ h', mt ((set.ext_iff.mp h') e).mpr he ((M.subset_cl _) (mem_insert _ _))},
  rw flat_iff_cl_self,
  by_contra h',
  obtain ⟨e,he',heF⟩ := exists_of_ssubset (ssubset_of_ne_of_subset (ne.symm h') (M.subset_cl F)),
  have h'' := (h e heF),
  rw [←cl_insert_cl_eq_cl_insert, insert_eq_of_mem he', cl_cl] at h'',
  exact h''.ne rfl,
end

lemma flat.cl_exchange (hF : M.flat F) (he : e ∈ M.cl (insert f F) \ F) :
  f ∈ M.cl (insert e F) \ F :=
by {nth_rewrite 1 ←hF.cl, apply cl_exchange, rwa hF.cl}

lemma flat.cl_subset_of_subset (hF : M.flat F) (h : X ⊆ F) :
  M.cl X ⊆ F :=
by {have h' := M.cl_mono h, rwa hF.cl at h'}

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

lemma eq_of_cl_eq_cl_forall {M₁ M₂ : matroid E} (h : ∀ X, M₁.cl X = M₂.cl X) :
  M₁ = M₂ :=
eq_of_indep_iff_indep_forall (λ I, by simp_rw [indep_iff_cl_diff_ne_forall, h])


/- ### Exchange -/

-- TODO. This is currently in the rank folder (for `finite_rk`), but it shouldn't need it

-- theorem base.strong_exchange (hB₁ : M.base B₁) (hB₂ : M.base B₂) (he : e ∈ B₁ \ B₂) :
--   ∃ f ∈ B₂ \ B₁, M.base (insert e (B₂ \ {f})) ∧ M.base (insert f (B₁ \ {e})) :=
-- begin
--   suffices : ∃ f ∈ B₂ \ B₁, M.indep (insert e (B₂ \ {f})) ∧ M.indep (insert f (B₁ \ {e})),
--   { obtain ⟨f,hf,h₁,h₂⟩:= this, 
--     exact ⟨f,hf,hB₂.exchange_base_of_indep hf.1 he.2 h₁, hB₁.exchange_base_of_indep he.1 hf.2 h₂⟩ },
--   by_contra' h', 
  
--   have h₁ : ∀ f ∈ (B₂ \ B₁), M.indep (insert e (B₂ \ {f})) → f ∈  M.cl (B₁ \ {e}) ,  
--   { rintro f hf hi, 
--     rw [(hB₁.indep.diff _).mem_cl_iff_of_not_mem (λ h, hf.2 h.1)],
--     exact (h' f hf) hi }, 
  
--   -- have := λ (f : E) (hf : f ∈ B₂ \ B₁), M.indep (insert f (B₁ \ {e})) → ¬M.indep (insert )  
--   -- have : ∀ f ∈  (B₂ \ B₁) ∩ M.cl (insert e (B₂ \ {f})), false, 
--   -- { },
--   -- by_contra' h', 

-- end 



/- ### Covering  -/

/-- A set is covered by another in a matroid if they are strictly nested flats, with no flat
  between them . -/
def covby (M : matroid E) (F₀ F₁ : set E) : Prop :=
  M.flat F₀ ∧ M.flat F₁ ∧ F₀ ⊂ F₁ ∧ ∀ F, M.flat F → F₀ ⊆ F → F ⊆ F₁ → F = F₀ ∨ F = F₁

lemma covby_iff :
  M.covby F₀ F₁ ↔ M.flat F₀ ∧ M.flat F₁ ∧ F₀ ⊂ F₁ ∧
    ∀ F, M.flat F → F₀ ⊆ F → F ⊆ F₁ → F = F₀ ∨ F = F₁ :=
iff.rfl

lemma covby.flat_left (h : M.covby F₀ F₁) : M.flat F₀ := h.1

lemma covby.flat_right (h : M.covby F₀ F₁) : M.flat F₁ := h.2.1

lemma covby.ssubset (h : M.covby F₀ F₁) : F₀ ⊂ F₁ := h.2.2.1

lemma covby.subset (h : M.covby F₀ F₁) : F₀ ⊆ F₁ := h.2.2.1.subset

lemma covby.eq_or_eq (h : M.covby F₀ F₁) (hF : M.flat F) (h₀ : F₀ ⊆ F) (h₁ : F ⊆ F₁) :
  F = F₀ ∨ F = F₁ :=
h.2.2.2 F hF h₀ h₁

lemma covby.eq_of_subset_of_ssubset (h : M.covby F₀ F₁) (hF : M.flat F) (hF₀ : F₀ ⊆ F) 
(hF₁ : F ⊂ F₁) :
  F = F₀ :=
(h.2.2.2 F hF hF₀ hF₁.subset).elim id (λ h', (hF₁.ne h').elim)

lemma covby.eq_of_ssubset_of_subset (h : M.covby F₀ F₁) (hF : M.flat F) (hF₀ : F₀ ⊂ F)
(hF₁ : F ⊆ F₁) :
  F = F₁ :=
(h.2.2.2 F hF hF₀.subset hF₁).elim (λ h', (hF₀.ne.symm h').elim) id

lemma covby.cl_insert_eq  (h : M.covby F₀ F₁) (he : e ∈ F₁ \ F₀) :
  M.cl (insert e F₀) = F₁ :=
h.eq_of_ssubset_of_subset (M.flat_of_cl _)
  ((ssubset_insert he.2).trans_subset (M.subset_cl _))
  (h.flat_right.cl_subset_of_subset (insert_subset.mpr ⟨he.1, h.ssubset.subset⟩))

lemma flat.exists_unique_flat_of_not_mem [finite_rk M] (hF₀ : M.flat F₀) (he : e ∉ F₀) :
  ∃! F₁, e ∈ F₁ ∧ M.covby F₀ F₁ :=
begin
  refine ⟨M.cl (insert e F₀), ⟨(M.subset_cl _) (mem_insert _ _),_⟩, _⟩,
  { refine ⟨hF₀,M.flat_of_cl _, 
      (ssubset_insert he).trans_subset (M.subset_cl _), λ F hF hF₀F hFeF₀,_⟩,
    by_contra' h,
    refine h.2 (hFeF₀.antisymm (hF.cl_subset_of_subset (insert_subset.mpr ⟨_,hF₀F⟩))),
    obtain ⟨x,hxF,hxF₀⟩ := exists_of_ssubset (hF₀F.ssubset_of_ne (ne.symm h.1)),
    exact mem_of_mem_of_subset (hF₀.cl_exchange ⟨hFeF₀ hxF, hxF₀⟩).1
      (hF.cl_subset_of_subset (insert_subset.mpr ⟨hxF, hF₀F⟩))},
  rintro F ⟨heF, ⟨-,hF,hF₀F,hmin⟩⟩,
  obtain (h' | rfl) := hmin (M.cl (insert e F₀)) (M.flat_of_cl _)
    ((subset_insert _ _).trans (M.subset_cl _))
    (hF.cl_subset_of_subset (insert_subset.mpr ⟨heF,hF₀F.subset⟩)),
  { exact (((ssubset_insert he).trans_subset (M.subset_cl _)).ne.symm h').elim},
  refl,
end

/- ### Hyperplanes -/

section hyperplane

lemma hyperplane_def : M.hyperplane H ↔ (M.flat H ∧ H ⊂ univ ∧ ∀ F, H ⊂ F → M.flat F → F = univ) :=
iff.rfl

lemma cocircuit.compl_hyperplane {K : set E} (hK : M.cocircuit K) : M.hyperplane Kᶜ := hK

lemma hyperplane.flat (hH : M.hyperplane H) : M.flat H := hH.1

lemma hyperplane.ssubset_univ (hH : M.hyperplane H) : H ⊂ univ := hH.2.1

lemma univ_not_hyperplane (M : matroid E) : ¬ M.hyperplane univ := λ h, h.2.1.ne rfl

lemma hyperplane.eq_of_subset (h₁ : M.hyperplane H₁) (h₂ : M.hyperplane H₂) (h : H₁ ⊆ H₂) :
  H₁ = H₂ :=
by_contra (λ he, h₂.ssubset_univ.ne (h₁.2.2 (h.ssubset_of_ne he) h₂.flat))

lemma hyperplane.not_ssubset (h₁ : M.hyperplane H₁) (h₂ : M.hyperplane H₂) :
  ¬ H₁ ⊂ H₂ :=
λ hss, hss.ne (h₁.eq_of_subset h₂ hss.subset)

lemma hyperplane.exists_not_mem (hH : M.hyperplane H) :
  ∃ e, e ∉ H :=
by {by_contra' h, apply M.univ_not_hyperplane, convert hH, rwa [eq_comm, eq_univ_iff_forall] }

lemma hyperplane_iff_maximal_cl_ne_univ :
  M.hyperplane H ↔ M.cl H ≠ univ ∧ ∀ X, H ⊂ X → M.cl X = univ :=
begin
  rw [hyperplane_def, cl_def],
  simp only [ne.def, sInter_eq_univ, mem_set_of_eq, and_imp, not_forall, exists_prop],
  refine ⟨λ h, ⟨⟨H, h.1, rfl.subset, h.2.1.ne⟩, λ X hHX, h.2.2 _
    (hHX.trans_subset (M.subset_cl _)) (M.flat_of_cl _)⟩, λ h, _⟩,
  obtain ⟨⟨F,hF,hHF,hFne⟩,hmax⟩ := h,
  suffices h_eq : H = F,
  { subst h_eq,
    refine ⟨hF, ssubset_univ_iff.mpr hFne, λ F hHF hF, _⟩,
    rw ←hF.cl,
    exact hmax _ hHF, },
  refine by_contra (λ hne, hFne _),
  rw [←hmax F (ssubset_of_ne_of_subset hne hHF), hF.cl],
end

lemma hyperplane_iff_maximal_not_supset_base :
  M.hyperplane H ↔ (¬∃ B ⊆ H, M.base B) ∧ ∀ X, H ⊂ X → ∃ B ⊆ X, M.base B :=
by simp_rw [hyperplane_iff_maximal_cl_ne_univ, ne.def, ←base_subset_iff_cl_eq_univ]

lemma base.hyperplane_of_cl_diff_singleton (hB : M.base B) (heB : e ∈ B) :
  M.hyperplane (M.cl (B \ {e})) :=
begin
  rw [hyperplane_iff_maximal_cl_ne_univ, cl_cl, ne_univ_iff_exists_not_mem],
  refine ⟨⟨e, λ he, indep_iff_cl_diff_ne_forall.mp hB.indep _ heB (cl_diff_singleton_eq_cl he)⟩,
    λ X hX, univ_subset_iff.mp _⟩,
  obtain ⟨f,hfX, hfB⟩ := exists_of_ssubset hX,
  obtain (rfl | hef) := eq_or_ne f e,
  { have hu := union_subset (singleton_subset_iff.mpr hfX) ((subset_cl _ _).trans hX.subset),
    rw [singleton_union, insert_diff_singleton, insert_eq_of_mem heB] at hu,
    exact (hB.cl.symm.trans_subset (M.cl_subset_cl_of_subset hu))},
  rw (hB.indep.diff {e}).not_mem_cl_iff at hfB,
  have  hf : f ∉ B,
  { refine λ hf, hef _,
    simp only [mem_diff, mem_singleton_iff, not_and, not_not] at hfB,
    exact hfB.1 hf},
  rw ←(hB.exchange_base_of_indep heB hf hfB.2).cl,
  exact M.cl_subset_cl_of_subset (insert_subset.mpr ⟨hfX,subset_trans (M.subset_cl _) hX.subset⟩),
end

lemma hyperplane.ssupset_eq_univ_of_flat (hH : M.hyperplane H) (hF : M.flat F) (h : H ⊂ F) :
  F = univ :=
by { rw hyperplane_iff_maximal_cl_ne_univ at hH, rw [←hH.2 F h, hF.cl] }

lemma hyperplane.cl_insert_eq_univ (hH : M.hyperplane H) (he : e ∉ H) :
  M.cl (insert e H) = univ :=
hH.ssupset_eq_univ_of_flat (M.flat_of_cl _) ((ssubset_insert he).trans_subset (M.subset_cl _))

lemma exists_hyperplane_sep_of_not_mem_cl (h : e ∉ M.cl X) :
  ∃ H, M.hyperplane H ∧ X ⊆ H ∧ e ∉ H :=
begin
  obtain ⟨I,hI⟩ := M.exists_basis X,
  rw [←hI.cl, hI.indep.not_mem_cl_iff] at h,  
  obtain ⟨B, hB, heIB⟩ := h.2.exists_base_supset, 
  rw insert_subset at heIB,
  refine ⟨M.cl (B \ {e}), hB.hyperplane_of_cl_diff_singleton heIB.1,_,λ hecl, _ ⟩,
  { exact hI.subset_cl.trans (M.cl_subset_cl_of_subset (subset_diff_singleton heIB.2 h.1)) },
  exact indep_iff_cl_diff_ne_forall.mp hB.indep e heIB.1 (cl_diff_singleton_eq_cl hecl),
end

lemma cl_eq_sInter_hyperplanes (M : matroid E) [finite_rk M] (X : set E) :
  M.cl X = ⋂₀ {H | M.hyperplane H ∧ X ⊆ H} :=
begin
  apply subset_antisymm,
  { simp only [subset_sInter_iff, mem_set_of_eq, and_imp],
    exact λ H hH hXH, hH.flat.cl_subset_of_subset hXH},
  by_contra' h',
  obtain ⟨x, h, hx⟩ := not_subset.mp h',
  obtain ⟨H, hH, hXH, hxH⟩ := exists_hyperplane_sep_of_not_mem_cl hx,
  exact hxH (h H ⟨hH, hXH⟩),
end

lemma flat.subset_hyperplane_of_ne_univ (hF : M.flat F) (h : F ≠ univ) :
  ∃ H, M.hyperplane H ∧ F ⊆ H :=
begin
  obtain ⟨e,he⟩ := (ne_univ_iff_exists_not_mem _).mp h, 
  rw ←hF.cl at he,  
  obtain ⟨H, hH, hFH, -⟩ := exists_hyperplane_sep_of_not_mem_cl he, 
  exact ⟨H, hH, hFH⟩,  
end

lemma subset_hyperplane_iff_cl_ne_univ :
  M.cl Y ≠ univ ↔ ∃ H, M.hyperplane H ∧ Y ⊆ H :=
begin
  refine ⟨λ h, _,_⟩,
  { obtain ⟨H, hH, hYH⟩ := (M.flat_of_cl Y).subset_hyperplane_of_ne_univ h,
    exact ⟨H, hH, (M.subset_cl Y).trans hYH⟩},
  rintro ⟨H, hH, hYH⟩ hY,
  refine hH.ssubset_univ.not_subset _,
  rw ←hH.flat.cl,
  exact (hY.symm.trans_subset (M.cl_mono hYH)),
end

lemma coindep_iff_cl_compl_eq_univ :
  M.coindep I ↔ M.cl Iᶜ = univ :=
by { simp_rw [←base_subset_iff_cl_eq_univ, subset_compl_iff_disjoint_left, coindep], tauto }

/- This follows more easily from a rank argument, but I'm trying to avoid rank. -/
lemma hyperplane.inter_right_covby_of_inter_left_covby
(hH₁ : M.hyperplane H₁) (hH₂ : M.hyperplane H₂) (h : M.covby (H₁ ∩ H₂) H₁) :
  M.covby (H₁ ∩ H₂) H₂ :=
begin
  obtain (rfl | hne) := eq_or_ne H₁ H₂, assumption,
  have hssu : H₁ ∩ H₂ ⊂ H₂,
  { refine (inter_subset_right _ _).ssubset_of_ne (λh'', hne _ ),
    rw [inter_eq_right_iff_subset, ←le_iff_subset] at h'',
    rw eq_of_le_of_not_lt h'' (hH₂.not_ssubset hH₁)},

  refine ⟨hH₁.flat.inter hH₂.flat, hH₂.flat, hssu, λ F hF hssF hFH₂, _⟩,
  by_contra' h',

  obtain ⟨x,hxF,hx⟩ := exists_of_ssubset (hssF.ssubset_of_ne (ne.symm h'.1)),
  obtain ⟨y,hyH₂,hy⟩ := exists_of_ssubset (hFH₂.ssubset_of_ne h'.2),
  obtain ⟨z,hzH₁,hz⟩ := exists_of_ssubset h.ssubset,
  have hzcl : M.cl (insert z (H₁ ∩ H₂)) = H₁ := h.cl_insert_eq ⟨hzH₁,hz⟩,
  have hxH₁ : x ∉ H₁ := λ hxH₁, hx ⟨hxH₁, hFH₂ hxF⟩,

  have h₁ : z ∉ M.cl (insert x (H₁ ∩ H₂)),
  { intro hz', apply hxH₁,
    have h' := cl_exchange ⟨hz', by rwa (hH₁.flat.inter hH₂.flat).cl⟩,
    rw [h.cl_insert_eq ⟨hzH₁,hz⟩] at h',
    exact h'.1},

  have hycl : y ∈ M.cl (insert z (insert x (H₁ ∩ H₂))) \ M.cl (insert x (H₁ ∩ H₂)),
  { refine ⟨_,λ hy',hy _⟩,
    { rw [insert_comm, ←cl_insert_cl_eq_cl_insert, hzcl, hH₁.cl_insert_eq_univ hxH₁],
      exact mem_univ _ },
    exact hF.cl_subset_of_subset (insert_subset.mpr ⟨hxF,hssF⟩) hy' },

  refine hz ⟨hzH₁, mem_of_mem_of_subset (cl_exchange hycl) ((diff_subset _ _).trans
    (hH₂.flat.cl_subset_of_subset _))⟩,
  rw [insert_subset, insert_subset],
  exact ⟨hyH₂, hFH₂ hxF, inter_subset_right _ _⟩,
end

lemma hyperplane.inter_covby_comm (hH₁ : M.hyperplane H₁) (hH₂ : M.hyperplane H₂) :
  M.covby (H₁ ∩ H₂) H₁ ↔  M.covby (H₁ ∩ H₂) H₂ :=
⟨hH₁.inter_right_covby_of_inter_left_covby hH₂,
  by {rw inter_comm, intro h, exact hH₂.inter_right_covby_of_inter_left_covby hH₁ h}⟩

end hyperplane

end matroid

section from_axioms

variables {E : Type*} [finite E]

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

/- ### closure and flat axioms -/
/-- A function satisfying the closure axioms determines a matroid -/
def matroid_of_cl (cl : set E → set E)
  (subset_cl : ∀ X, X ⊆ cl X )
  (cl_mono : ∀ X Y, X ⊆ Y → cl X ⊆ cl Y )
  (cl_idem : ∀ X, cl (cl X) = cl X )
  (cl_exchange : ∀ X e f, f ∈ cl (insert e X) \ cl X → e ∈ cl (insert f X) \ cl X ) :
matroid E := matroid.matroid_of_base_of_finite
  (λ B, cl B = univ ∧ ∀ X ⊂ B, cl X ≠ univ)

  (let ⟨B,hB,hBmin⟩ := finite.exists_minimal (λ B, cl B = univ)
      ⟨univ, eq_univ_of_univ_subset (subset_cl _)⟩ in
    ⟨B, hB, λ X hXB hX, hXB.ne.symm (hBmin _ hX hXB.subset)⟩)

  (begin
    intros B₁ B₂ hB₁ hB₂ x hx,
    by_contra' h,
    have h₁ : ∀ y ∈ B₂, y ∉ cl (B₁ \ {x}) → cl (insert y (B₁ \ {x})) = univ,
    { refine λ y hyB₂ hynotin, _,
      have hex := cl_exchange (B₁ \ {x}) x y,
      rw [insert_diff_singleton, insert_eq_of_mem hx.1, hB₁.1, ←compl_eq_univ_diff,
        mem_compl_iff] at hex,
      have h' := insert_subset.mpr ⟨(hex hynotin).1, (subset_insert _ _).trans (subset_cl _)⟩,
      rw [insert_diff_singleton, insert_eq_of_mem hx.1] at h',
      have h'' := cl_mono _ _ h',
      rwa [cl_idem, hB₁.1, univ_subset_iff] at h''},

    have hss : B₂ \ B₁ ⊆ cl (B₁ \ {x}),
    { refine λ y hy, by_contra (λ h', _),
      have hxy : x ≠ y,
      { rintro rfl, exact hx.2 hy.1},
      obtain ⟨A,⟨hAs,hA⟩,hAmin⟩ := finite.exists_minimal _ (h y hy (h₁ y hy.1 h')),
      have hxA : x ∉ A,
      { refine λ hxA, hxy _,  have := hAs.subset, simpa using this hxA},
      have hyA : y ∈ A,
      { by_contra hyA,
        exact hB₁.2 _ (((subset_insert_iff_of_not_mem hyA).mp hAs.subset).trans_ssubset
          $ diff_singleton_ssubset.2 hx.1) hA },
      have hy' : B₁ ⊆ cl (A \ {y}),
      { refine λ z hz, by_contra (λ hz', _ ),
        have hzA : z ∈ cl (insert y (A \ {y})),
        { rw [insert_diff_singleton, insert_eq_of_mem hyA, hA], exact mem_univ _,},
        have h' := (cl_exchange _ _ _ ⟨hzA,hz'⟩).1,
        have h'' := insert_subset.mpr ⟨h', (subset_insert _ _).trans (subset_cl _)⟩,
        rw [insert_diff_singleton, insert_eq_of_mem hyA] at h'',
        have h''' := cl_mono _ _ h'',
        rw [hA, univ_subset_iff, cl_idem] at h''',
        refine hB₁.2 _ _ h''',
        refine ssubset_of_ne_of_subset _ (insert_subset.mpr ⟨hz,_⟩),
        { obtain (rfl | hxz) := eq_or_ne x z,
          { intro h_eq,
            rw [←h_eq, insert_diff_singleton_comm hxy.symm] at hAs,
            refine hAs.not_subset _,
            rw [diff_subset_iff, insert_comm, singleton_union, insert_diff_singleton,
              insert_eq_of_mem hyA], },
          simp_rw [ne.def, ext_iff, not_forall, mem_insert_iff, mem_diff, mem_singleton_iff],
          use x,
          have := hx.1, tauto},
        rw [diff_subset_iff, singleton_union],
        exact hAs.subset.trans (insert_subset_insert (diff_subset _ _))},
      have hA' := cl_mono _ _ hy',
      rw [hB₁.1, univ_subset_iff, cl_idem] at hA',
      refine (diff_singleton_ssubset.2 hyA).ne.symm (hAmin _ ⟨_,hA'⟩ (diff_subset _ _)),
      exact (diff_subset _ _).trans_ssubset hAs},

  have ht : B₂ ⊆ _ := subset_trans _ (union_subset hss (subset_cl (B₁ \ {x}))),
  { have ht' := cl_mono _ _ ht,
    rw [hB₂.1, cl_idem, univ_subset_iff] at ht',
    exact hB₁.2 _ (diff_singleton_ssubset.2 hx.1) ht'},
  nth_rewrite 0 [←diff_union_inter B₂ B₁],
  apply union_subset_union rfl.subset,
  rintros y ⟨hy2,hy1⟩,
  rw mem_diff_singleton,
  use hy1,
  rintro rfl,
  exact hx.2 hy2,
  end )

lemma matroid_of_cl_aux (cl : set E → set E)
  (subset_cl : ∀ X, X ⊆ cl X )
  (cl_mono : ∀ X Y, X ⊆ Y → cl X ⊆ cl Y )
  (cl_idem : ∀ X, cl (cl X) = cl X )
  (cl_exchange : ∀ X e f, f ∈ cl (insert e X) \ cl X → e ∈ cl (insert f X) \ cl X )
  {I : set E} :
(∀ x ∈ I, cl (I \ {x}) ≠ cl I) ↔ ∃ B, cl B = univ ∧ (∀ X ⊂ B, cl X ≠ univ) ∧ I ⊆ B :=
begin
  refine ⟨λ h, _, λ h x hI hcl, _⟩,
  { obtain ⟨B, ⟨hB, hIB⟩, hBmax⟩ :=
      finite.exists_maximal (λ X, (∀ e ∈ X, cl (X \ {e}) ≠ cl X) ∧ I ⊆ X)
         ⟨I, h, rfl.subset⟩,
    refine ⟨B, by_contra (λ hBu, _), λ X hXB hX, _, hIB⟩,
    { rw [←ne.def, ne_univ_iff_exists_not_mem] at hBu,
      obtain ⟨a,haB⟩ := hBu,
      have haB' : a ∉ B := λ haB', haB (subset_cl B haB'),
      rw hBmax (insert a B) _ (subset_insert _ _) at haB',
      { exact haB' (mem_insert _ _)},
      refine ⟨λ e heaB hcl, _,  hIB.trans (subset_insert _ _)⟩,
      have hea : e ≠ a,
      { rintro rfl,
        rw [insert_diff_self_of_not_mem haB'] at hcl,
        rw hcl at haB,
        exact haB ((subset_cl (insert e B)) (mem_insert e B))},
      have heB : e ∈ B := mem_of_mem_insert_of_ne heaB hea,
      have hecl : e ∉ cl ((insert a B) \ {e}),
      { refine λ h_in, hB e heB (cl_diff_singleton_eq_cl cl subset_cl cl_mono cl_idem _),
        by_contra hecl, apply haB,
        rw ←insert_diff_singleton_comm hea.symm  at h_in,
        have := (cl_exchange _ _ _ ⟨h_in,hecl⟩).1,
        rwa [insert_diff_singleton, insert_eq_of_mem heB] at this},
      rw hcl at hecl,
      exact hecl ((subset_cl _) heaB)},
    obtain ⟨e,heB, heX⟩ := exists_of_ssubset hXB,
    have hcon := hX.symm.trans_subset (cl_mono _ _ (subset_diff_singleton hXB.subset heX)),
    rw [univ_subset_iff] at hcon,
    refine hB e heB ((cl_mono _ _ (diff_subset _ _)).antisymm _),
    rw [hcon],
    apply subset_univ},
  obtain ⟨B, hBu, hBmax, hIB⟩ := h,
  refine hBmax _ (diff_singleton_ssubset.2 $ hIB hI) _,
  rwa cl_diff_singleton_eq_cl cl subset_cl cl_mono cl_idem,
  have hdiff := cl_mono _ _  (@diff_subset_diff_left _ _ _ {x} hIB),
  rw [hcl] at hdiff,
  apply hdiff,
  apply subset_cl,
  exact hI,
end

@[simp] lemma matroid_of_cl_apply (cl : set E → set E)
  (subset_cl : ∀ X, X ⊆ cl X )
  (cl_mono : ∀ X Y, X ⊆ Y → cl X ⊆ cl Y )
  (cl_idem : ∀ X, cl (cl X) = cl X )
  (cl_exchange : ∀ X e f, f ∈ cl (insert e X) \ cl X → e ∈ cl (insert f X) \ cl X ) :
(matroid_of_cl cl subset_cl cl_mono cl_idem cl_exchange).cl = cl :=
begin
  set M := matroid_of_cl cl subset_cl cl_mono cl_idem cl_exchange with hM,
  apply funext,
  by_contra' h,
  obtain ⟨I,hI,hImin⟩ := finite.exists_minimal _ h,

  have hImin' : ∀ x ∈ I, M.cl (I \ {x}) = cl (I \ {x}),
  { by_contra' h,
    obtain ⟨x,hxI,hne⟩ := h,
    exact (diff_singleton_ssubset.2 hxI).ne' (hImin _ hne  $diff_subset _ _) },

  set indep : set E → Prop := λ I, ∀ x ∈ I, cl (I \ {x}) ≠ cl I with h_indep,

  have hIi : (M.indep I) ∧ (indep I),
  { rw [matroid.indep_iff_cl_diff_ne_forall],
    by_contra h', apply hI,
    simp_rw [not_and_distrib, h_indep, not_forall, not_ne_iff] at h',
    obtain (⟨x,hxI,hne⟩ | ⟨x,hxI,hne⟩) := h',
    { rw [←hne, hImin' _ hxI, cl_diff_singleton_eq_cl cl subset_cl cl_mono cl_idem],
      rw [←hImin' x hxI, hne],
      exact (M.subset_cl I) hxI},
    rw [←hne, ←hImin' _ hxI, cl_diff_singleton_eq_cl M.cl M.subset_cl M.cl_mono M.cl_cl],
    rw [hImin' _ hxI, hne],
    exact (subset_cl I) hxI},

  simp_rw [set.ext_iff, not_forall, not_iff, hIi.1.not_mem_cl_iff,
    matroid.indep_iff_subset_base, hM, matroid_of_cl] at hI,

  obtain ⟨x,hx⟩:= hI,
  obtain (hxI | hxI) := em (x ∈ cl I),
  { obtain ⟨hxI', B, ⟨hB, hBmin⟩, hxIB⟩ := hx.mpr hxI,
    refine hBmin (B \ {x}) (diff_singleton_ssubset.2 $ hxIB $ mem_insert _ _) _,
    rwa [cl_diff_singleton_eq_cl cl subset_cl cl_mono cl_idem],
    have hIBx : I ⊆ B \ {x}, from ((subset_diff_singleton ((subset_insert _ _).trans hxIB)) hxI'),
    exact cl_mono I (B \ {x}) hIBx hxI},

  have hxI' : x ∉ I, from λ hxI', hxI ((subset_cl _) hxI'),
  simp_rw [iff_false_right hxI, not_and, not_exists, not_and] at hx,

  have hxI : indep (insert x I),
   { rintro y (rfl | hy) h_eq,

    { simp only [insert_diff_of_mem, mem_singleton] at h_eq,
      refine hxI (cl_mono _ _ (diff_subset _ {y}) _),
      rw h_eq,
      refine subset_cl _ (mem_insert _ _)},

    have hxy : x ≠ y, {rintro rfl, exact hxI' hy},
    have hycl : y ∈ cl (insert x (I \ {y})),
    { rw [insert_diff_singleton_comm hxy, h_eq], apply subset_cl, exact subset_insert _ _ hy},
    have hy' : y ∉ cl (I \ {y}), from
      λ hy', hIi.2 y hy (cl_diff_singleton_eq_cl cl subset_cl cl_mono cl_idem  hy'),
    have h' := (cl_exchange _ _ _ ⟨hycl,hy'⟩).1,
    rw [insert_diff_singleton, insert_eq_of_mem hy] at h',
    exact hxI h' },
  rw [h_indep, matroid_of_cl_aux cl subset_cl cl_mono cl_idem cl_exchange] at hxI,
  obtain ⟨B, hB, hIB⟩ := hxI,
  exact hx hxI' B ⟨hB, hIB.1⟩ hIB.2,
end

lemma matroid_of_flat_aux (flat : set E → Prop) (univ_flat : flat univ)
(flat_inter : ∀ F₁ F₂, flat F₁ → flat F₂ → flat (F₁ ∩ F₂)) (X : set E) :
  flat (⋂₀ {F | flat F ∧ X ⊆ F}) ∧ ∀ F₀, flat F₀ → ((⋂₀ {F | flat F ∧ X ⊆ F}) ⊆ F₀ ↔ X ⊆ F₀) :=
begin
  set F₁ := ⋂₀ {F | flat F ∧ X ⊆ F} with hF₁,
  refine ⟨_, λ F₀ hF₀, ⟨λ hF₁F₀, _, λ hXF, _⟩⟩ ,
  { obtain ⟨F',⟨hF',hYF'⟩,hmin⟩ := finite.exists_minimal (λ F, flat F ∧ X ⊆ F)
      ⟨univ, univ_flat, subset_univ _⟩,
    convert hF',
    refine subset_antisymm (sInter_subset_of_mem ⟨hF',hYF'⟩) (subset_sInter _),
    rintro F ⟨hF,hYF⟩,
    rw hmin _ ⟨flat_inter _ _ hF hF', subset_inter hYF hYF'⟩ _,
    { apply inter_subset_left},
    apply inter_subset_right},
  { refine subset_trans (subset_sInter (λ F h, _)) hF₁F₀, exact h.2},
  apply sInter_subset_of_mem,
  exact ⟨hF₀, hXF⟩,
end

/-- A collection of sets satisfying the flat axioms determines a matroid -/
def matroid_of_flat (flat : set E → Prop) (univ_flat : flat univ)
(flat_inter : ∀ F₁ F₂, flat F₁ → flat F₂ → flat (F₁ ∩ F₂))
(flat_partition : ∀ F₀ e, flat F₀ → e ∉ F₀ →
  ∃! F₁, flat F₁ ∧ insert e F₀ ⊆ F₁ ∧ ∀ F, flat F → F₀ ⊆ F → F ⊂ F₁ → F₀ = F) :=
matroid_of_cl (λ X, ⋂₀ {F | flat F ∧ X ⊆ F})
(λ X, subset_sInter (λ F, and.right))
(λ X Y hXY, subset_sInter (λ F hF, by {apply sInter_subset_of_mem, exact ⟨hF.1, hXY.trans hF.2⟩}))
(begin
  refine λ X, (subset_sInter (λ F, and.right)).antisymm' _,
  simp only [subset_sInter_iff, mem_set_of_eq, and_imp],
  rintro F hF hXF,
  apply sInter_subset_of_mem,
  split, assumption,
  apply sInter_subset_of_mem,
  exact ⟨hF, hXF⟩,
end )
(begin
  simp only [mem_diff, mem_sInter, mem_set_of_eq, and_imp, not_forall, exists_prop,
    forall_exists_index],
  refine λ X e f h F₀ hF₀ hXF₀ hfF₀, ⟨λ Ff hFf hfXf, _,
    ⟨F₀, hF₀, hXF₀, λ heF₀, hfF₀ (h _ hF₀ (insert_subset.mpr ⟨heF₀,hXF₀⟩))⟩⟩,

  obtain ⟨hFX, hX'⟩    := matroid_of_flat_aux flat univ_flat flat_inter X,
  obtain ⟨hFXe, hXe'⟩  := matroid_of_flat_aux flat univ_flat flat_inter (insert e X),
  obtain ⟨hFXf, hXf'⟩  := matroid_of_flat_aux flat univ_flat flat_inter (insert f X),

  set FX := sInter {F | flat F ∧ X ⊆ F} with hFX_def,
  set FXe := sInter {F | flat F ∧ insert e X ⊆ F} with hFXe_def,
  set FXf := sInter {F | flat F ∧ insert f X ⊆ F} with hFXe_def,

  apply (hXf' Ff hFf).mpr hfXf,
  have heFXe : e ∈ FXe := mem_sInter.mpr (λ _ hF, hF.2 (mem_insert _ _)),
  have hfFXf : f ∈ FXf := mem_sInter.mpr (λ _ hF, hF.2 (mem_insert _ _)),

  have hXFX : X ⊆ FX := subset_sInter (λ _, and.right),
  have hfFX : f ∉ FX := λ hfFX, hfF₀ ((hX' F₀ hF₀).mpr hXF₀ hfFX),
  have heFX : e ∉ FX := λ heFX, hfFX (h _ hFX (insert_subset.mpr ⟨heFX, hXFX⟩)),
  have hFXFXe : FX ⊆ FXe,
  { rw [hX' FXe hFXe], exact subset_sInter (λ F hF, (subset_insert _ _).trans hF.2)},
  have hFXFXf : FX ⊆ FXf,
  { rw [hX' FXf hFXf], exact subset_sInter (λ F hF, (subset_insert _ _).trans hF.2)},

  have hfFXe := h FXe hFXe (insert_subset.mpr ⟨heFXe,hXFX.trans hFXFXe⟩),

  have hss := (hXf' _ hFXe).mpr (insert_subset.mpr ⟨hfFXe, hXFX.trans hFXFXe⟩),

  suffices h_eq : FXf = FXe, by rwa h_eq,
  by_contra h_ne, apply hfFX,
  have hssu := ssubset_of_subset_of_ne hss h_ne,

  obtain ⟨FXe',⟨hFXe',heFX',hmin⟩, hunique⟩ := flat_partition FX e hFX heFX,

  have hFXemin : ∀ (F : set E), flat F → FX ⊆ F → F ⊂ FXe → FX = F, from
  λ F hF hFXF hFFXe, hmin _ hF hFXF
    (hFFXe.trans_subset ((hXe' _ hFXe').mpr ((insert_subset_insert hXFX).trans heFX'))),

  rw hunique FXe ⟨hFXe, insert_subset.mpr ⟨heFXe, hFXFXe⟩, hFXemin⟩ at hssu,
  rwa ← (hmin _ hFXf hFXFXf hssu) at hfFXf,
end)

@[simp] lemma matroid_of_flat_apply (flat : set E → Prop) (univ_flat : flat univ)
(flat_inter : ∀ F₁ F₂, flat F₁ → flat F₂ → flat (F₁ ∩ F₂))
(flat_partition : ∀ F₀ e, flat F₀ → e ∉ F₀ →
∃! F₁, flat F₁ ∧ insert e F₀ ⊆ F₁ ∧ ∀ F, flat F → F₀ ⊆ F → F ⊂ F₁ → F₀ = F) :
  (matroid_of_flat flat univ_flat flat_inter flat_partition).flat = flat :=
begin
  ext F,
  simp_rw [matroid_of_flat, matroid.flat_iff_cl_self, matroid_of_cl_apply],
  refine ⟨λ hF, _, λ hF, _⟩,
  { rw ←hF, exact (matroid_of_flat_aux flat univ_flat flat_inter _).1},
  exact (subset_sInter (λ F', and.right)).antisymm' (sInter_subset_of_mem ⟨hF,rfl.subset⟩),
end


end from_axioms