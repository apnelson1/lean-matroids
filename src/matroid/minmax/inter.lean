import ..pseudominor
import ..constructions.direct_sum

/- Here we prove Edmonds' matroid intersection theorem: given two matroids `M₁` and `M₂` on `α`, the
  largest set that is independent in both matroids has size equal to the min of `M₁.r X + M₂.r Xᶜ`,
  taken over all `X ⊆ E`. We also derive Rado's theorem as a corollary. -/

open_locale classical

open matroid set

variables {E : Type*} [finite E] {M M₁ M₂ : matroid E} {I A : set E}

section intersection

/-- the easy direction of matroid intersection; the rank in `M₁` of `A` plus the rank in `M₂` of
  `Aᶜ` is an upper bound for the size of a common independent set of `M₁` and `M₂` . -/
theorem common_ind_le_r_add_r_compl (hI₁ : M₁.indep I) (hI₂ : M₂.indep I) (A : set E) :
  I.ncard ≤ M₁.r A + M₂.r Aᶜ :=
begin
  rw [←ncard_inter_add_ncard_diff_eq_ncard I A, ←(hI₁.inter_right A).r, ←(hI₂.diff A).r,
    diff_eq_compl_inter],
  exact add_le_add (M₁.r_inter_right_le_r I A) (M₂.r_inter_left_le_r Aᶜ I),
end

/-- A common independent set attaining the bound must intersect `A` and `Aᶜ` in bases in the
  respective matroids -/
lemma common_ind_eq_spec (hI₁ : M₁.indep I) (hI₂ : M₂.indep I) {A : set E}
(h : M₁.r A + M₂.r Aᶜ ≤ I.ncard) :
  M₁.basis (I ∩ A) A ∧ M₂.basis (I ∩ Aᶜ) Aᶜ :=
begin
  have h₁i := hI₁.inter_right A,
  have h₂i := hI₂.inter_right Aᶜ,
  simp_rw [basis_iff_indep_card, ←h₁i.r, ←h₂i.r],
  rw [←ncard_inter_add_ncard_diff_eq_ncard I A, diff_eq_compl_inter, inter_comm Aᶜ,
    ←h₁i.r, ←h₂i.r] at h,
  refine ⟨⟨hI₁.inter_right A, inter_subset_right _ _, _⟩,
    ⟨hI₂.inter_right _,inter_subset_right _ _,_⟩⟩;
  linarith [M₁.r_inter_right_le_r I A, M₂.r_inter_right_le_r I Aᶜ],
end

/-- The hard direction of matroid intersection : existence -/
lemma exists_common_ind (M₁ M₂ : matroid E) :
  ∃ I X, M₁.indep I ∧ M₂.indep I ∧ I.ncard = M₁.r X + M₂.r Xᶜ :=
begin
  -- Suppose not. Then we get strict inequality for all choices of I, X.
  by_contra' hcon,
  have hcon' : ∀ I X, M₁.indep I → M₂.indep I → I.ncard < M₁.r X + M₂.r Xᶜ, from
    λ I X hI₁ hI₂, lt_of_le_of_ne (common_ind_le_r_add_r_compl hI₁ hI₂ X) (hcon I X hI₁ hI₂),

  -- Construct a minimal counterexample (wrt the number of nonloops of `M₁`)
  obtain ⟨M,hM,hpmin⟩ := (to_finite _ : {M | ∃ M', _}.finite).exists_minimal_wrt
    (ncard ∘ matroid.nonloops) ⟨M₁, ⟨M₂, hcon'⟩⟩,

  clear hcon hcon' M₁ M₂,
  obtain ⟨M₁,M₂,hcon⟩ := ⟨M,hM⟩,

  -- There is a common nonloop of `M₁` and `M₂`, otherwise the result is easy
  have hne : ∃ e, M₁.nonloop e ∧ M₂.nonloop e,
  { simp_rw [←not_loop_iff], by_contra' he,
    simp_rw [loop_iff_mem_cl_empty, ←mem_compl_iff, ←subset_def] at he,
    specialize hcon ∅ (M₁.cl ∅) M₁.empty_indep M₂.empty_indep,
    rw [ncard_empty, r_cl, r_empty, zero_add] at hcon,
    exact (hcon.trans_le (M₂.r_mono he)).ne (by rw [r_cl, r_empty])},

  obtain ⟨e, he₁,he₂⟩ := hne,

  -- Projecting/loopifying `e` gives non-counterexamples (by minimality), so there exist pairs
  -- with equality in these minors.
  have hd' := ncard_lt_ncard (strict_pminor_of_loopify_nonloop he₁).nonloops_ssubset_nonloops,
  refine hd'.ne.symm (hpmin (M₁ ⟍ e) ⟨M₂ ⟍ e,_⟩ hd'.le),
  by_contra' hd,
  obtain ⟨Id,Xd, hId₁, hId₂, hId⟩ := hd,

  have hc' := ncard_lt_ncard (strict_pminor_of_project_nonloop he₁).nonloops_ssubset_nonloops,
  refine hc'.ne.symm (hpmin (M₁ ⟋ e) ⟨M₂ ⟋ e,_⟩ hc'.le),
  by_contra' hc,
  obtain ⟨Ic,Xc, hIc₁, hIc₂, hIc⟩ := hc,

  -- Use these pairs to get rank lower bounds ...
  have hi := (hId.trans_lt (hcon _ ((Xc ∩ Xd) \ {e}) hId₁.of_loopify hId₂.of_loopify)),

  have hic : (Xc ∩ Xd \ {e})ᶜ = (insert e (Xcᶜ ∪ Xdᶜ)),
  { apply compl_injective,
    simp_rw [←union_singleton, compl_union, compl_compl, diff_eq_compl_inter, inter_comm {e}ᶜ]},
  
  simp_rw [loopify_elem, loopify.r_eq, hic] at hi,
  zify at hIc hId hcon,

  have hu := hcon (insert e Ic) (insert e (Xc ∪ Xd))
    (by rwa ← he₁.indep_project_iff (not_mem_of_indep_project_singleton hIc₁))
    (by rwa ← he₂.indep_project_iff (not_mem_of_indep_project_singleton hIc₁)),

  have huc : (insert e (Xc ∪ Xd))ᶜ = Xcᶜ ∩ Xdᶜ \ {e},
  { apply compl_injective,
    simp_rw [diff_eq_compl_inter, compl_inter, compl_compl, singleton_union]},

  simp_rw [ncard_insert_of_not_mem (not_mem_of_indep_project_singleton hIc₁),
    nat.cast_add, nat.cast_one, huc] at hu,

  rw [he₁.cast_r_project_eq, he₂.cast_r_project_eq] at hIc,

  -- ... and contradict them with submodularity bounds.
  have sm1 := M₁.r_submod (insert e Xc) (Xd \ {e}),
  have sm2 := M₂.r_submod (insert e Xcᶜ) (Xdᶜ \ {e}),

  rw [insert_union, insert_union_distrib, insert_diff_singleton, ←insert_union_distrib,
    insert_inter_of_not_mem (not_mem_diff_singleton _ _), ←inter_diff_assoc] at sm1 sm2,

  linarith,
end

/-- We can choose a minimizing pair `I,X` where `X` is a flat of `M₁` -/
lemma exists_common_ind_with_flat_left (M₁ M₂ : matroid E) :
  ∃ I X, M₁.indep I ∧ M₂.indep I ∧ I.ncard = M₁.r X + M₂.r Xᶜ ∧ M₁.flat X :=
begin
  obtain ⟨I,X₀, h₀⟩ := exists_common_ind M₁ M₂,
  rw [←M₁.r_cl X₀] at h₀,
  refine ⟨I,M₁.cl X₀,h₀.1, h₀.2.1, le_antisymm _ _, M₁.flat_of_cl _⟩,
  { apply common_ind_le_r_add_r_compl h₀.1 h₀.2.1 },
  rw h₀.2.2,
  simp only [add_le_add_iff_left],
  exact M₂.r_mono (compl_subset_compl.mpr (subset_cl _ _)),
end

lemma exists_common_ind_with_flat_right (M₁ M₂ : matroid E) :
  ∃ I X, M₁.indep I ∧ M₂.indep I ∧ I.ncard = M₁.r X + M₂.r Xᶜ ∧ M₂.flat Xᶜ :=
begin
  obtain ⟨I,X₀,h₀,h₁,hX₀,hF⟩ := exists_common_ind_with_flat_left M₂ M₁,
  exact ⟨I, X₀ᶜ,h₁,h₀,by rwa [add_comm, compl_compl],by rwa compl_compl⟩,
end

/-- The cardinality of a largest common independent set of matroids `M₁,M₂`.
  Is `find_greatest` really the right way to define this?  -/
noncomputable def max_common_ind (M₁ M₂ : matroid E) :=
nat.find_greatest (λ n, ∃ I, M₁.indep I ∧ M₂.indep I ∧ I.ncard = n) ((univ : set E).ncard)

lemma max_common_ind_eq_iff (M₁ M₂ : matroid E) {n : ℕ} :
  max_common_ind M₁ M₂ = n ↔ (∃ I, M₁.indep I ∧ M₂.indep I ∧ n ≤ I.ncard) ∧
    (∀ I, M₁.indep I → M₂.indep I → I.ncard ≤ n)  :=
begin
  rw [max_common_ind, nat.find_greatest_eq_iff],
  obtain (rfl | n) := n,
  { simp only [nat.nat_zero_eq_zero, zero_le', ne.def, eq_self_iff_true, not_true, ncard_eq_zero,
    exists_eq_right_right, is_empty.forall_iff, not_exists, not_and, true_and, le_zero_iff,
    and_true],
    split,
    {
      refine λ h, ⟨⟨_, M₁.empty_indep, M₂.empty_indep⟩, λ I hI₁ hI₂, _⟩,
      suffices hcI : ¬(0 < I.ncard), by rwa [not_lt, le_zero_iff, ncard_eq_zero] at hcI,
      exact λ hcI, h hcI (ncard_mono (subset_univ _)) I hI₁ hI₂ rfl},
    refine λ h n hpos hn I hI₁ hI₂ hcard, _,
    rw [←hcard, h.2 I hI₁ hI₂] at hpos,
    simpa using hpos},

  simp only [ne.def, nat.succ_ne_zero, not_false_iff, forall_true_left, not_exists, not_and,
    nat.succ_eq_add_one],
  split,
  { rintro ⟨hn, ⟨I, hI₁, hI₂, hIcard⟩, h'⟩,
    refine ⟨⟨I, hI₁, hI₂, hIcard.symm.le⟩, λ J hJ₁ hJ₂, _⟩,
    by_contra' hJcard,
    exact h' hJcard (ncard_mono (subset_univ _)) J hJ₁ hJ₂ rfl},
  simp only [and_imp, forall_exists_index],
  refine λ I hI₁ hI₂ hIcard h, ⟨_,⟨I, hI₁,hI₂,_⟩ ,λ n' hn' hn'' J hJ₁ hJ₂ hJcard, _⟩,
  { rw ←(h I hI₁ hI₂).antisymm hIcard, exact ncard_mono (subset_univ _)},
  { rw ←(h I hI₁ hI₂).antisymm hIcard},
  subst hJcard,
  exact (h J hJ₁ hJ₂).not_lt hn',
end

theorem matroid_intersection_minmax (M₁ M₂ : matroid E) :
  max_common_ind M₁ M₂ = ⨅ X, M₁.r X + M₂.r Xᶜ :=
begin
  rw [max_common_ind_eq_iff],
  obtain ⟨I, X, hI₁, hI₂, heq⟩ := exists_common_ind M₁ M₂,
  refine ⟨⟨I, hI₁, hI₂, (cinfi_le' _ _).trans_eq heq.symm⟩, λ J hJ₁ hJ₂, _ ⟩,
  exact (le_cinfi_iff (order_bot.bdd_below _)).mpr (common_ind_le_r_add_r_compl hJ₁ hJ₂),
end

end intersection

section rado

variables {ι : Type} [finite ι]

lemma rado_necessary {f : E → ι} {x : ι → E} (hx : ∀ i, f (x i) = i) (h_ind : M.indep (range x))
(S : set ι) :
  S.ncard ≤ M.r (f ⁻¹' S) :=
begin
  have hS := (h_ind.subset (image_subset_range x S)).r,
  rw [ncard_image_of_injective _ (λ i j hij, by rw [←hx i, hij, hx j] : x.injective)] at hS,
  rw ←hS,
  refine M.r_mono _,
  rintro f ⟨i, hi, rfl⟩,
  rwa [mem_preimage, hx],
end

lemma rado_sufficient (f : E → ι) (h : ∀ (S : set ι), S.ncard ≤ M.r (f ⁻¹' S)) :
  ∃ (x : ι → E), (∀ i, f (x i) = i) ∧ M.indep (range x) :=
begin
  set M' := partition_matroid_on f 1 with hM',
  obtain ⟨I, X, hI₁, hI₂, hIX, hF⟩ := exists_common_ind_with_flat_right M M',
  obtain ⟨hIb₁,hIb₂⟩ := common_ind_eq_spec hI₁ hI₂ hIX.symm.le,

  have h_inj : inj_on f I,
  { refine λ a ha b hb hab, by_contra (λ (hne : a ≠ b), _),
    have hcard := (partition_matroid_on_indep_iff.mp hI₂) (f a),
    rw [pi.one_apply, ncard_le_one_iff] at hcard,
    exact hne (hcard ⟨ha, (by simp)⟩ ⟨hb, by simp [hab]⟩)},

  have hXc := (h (f '' Xᶜ)ᶜ).trans (M.r_mono _ : _ ≤ M.r X), swap,
  { simp only [preimage_subset_iff, mem_compl_iff, mem_image, not_exists, not_and, not_imp_not],
    exact λ a h, h _ rfl},

  simp only [partition_matroid_on_one_r_eq, pi.one_apply] at hIX,
  have hineq := (add_le_add_right hXc _).trans_eq hIX.symm,
  rw [add_comm, ncard_add_ncard_compl, ←ncard_univ, ←ncard_image_of_inj_on h_inj] at hineq,
  have himage := eq_of_subset_of_ncard_le (subset_univ _) hineq,

  have hinv : ∀ i, ∃ e ∈ I, f e = i,
  { simp_rw [←mem_image_iff_bex, himage], exact mem_univ},

  choose x hx using hinv,
  refine ⟨x, λi, (hx i).2, hI₁.subset _⟩,
  rintro e ⟨i,hi,rfl⟩,
  exact (hx i).1,
end

/-- Rado's theorem: Given a partition `f : E → ι` of the ground set `E` of a matroid `M`, there is a
  transversal of `f` that is independent in `M` if and only if the rank of the preimage of every set
  `S` in `ι` is at least its cardinality. -/
theorem rado_iff {M : matroid E} {f : E → ι} :
  (∃ (x : ι → E), (∀ i, f (x i) = i) ∧ M.indep (range x)) ↔ ∀ S, ncard S ≤ M.r (f ⁻¹' S) :=
⟨λ h S, exists.elim h (λ x hx, rado_necessary hx.1 hx.2 _) , rado_sufficient _⟩


end rado

