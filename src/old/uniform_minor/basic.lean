import prelim.collections prelim.embed prelim.size prelim.induction prelim.minmax finsum.fin_api
import matroid.pointcount matroid.simple
import matroid.submatroid.projection matroid.submatroid.minor_iso
import matroid.constructions.uniform

noncomputable theory
open_locale classical big_operators

open set matroid

universes u v w

section uniform

variables {α : Type*} [fintype α] {M N : matroid α} {a b : ℤ}

/-- the property of having a `U_{a,b}` -minor -/
def matroid.has_unif_minor (M : matroid α) (a b : ℤ) :=
  M.has_iminor (canonical_unif a b)

lemma has_unif_minor_def :
  M.has_unif_minor a b ↔ (canonical_unif a b).is_iminor_of M :=
iff.rfl

lemma has_unif_minor_def' :
  M.has_unif_minor a b ↔ M.has_iminor (canonical_unif a b) :=
iff.rfl

lemma has_unif_minor_iff (ha : 0 ≤ a) (hb : 0 ≤ b) :
  M.has_unif_minor a b ↔
    ∃ S C : set α,  disjoint S C
                  ∧ size S = b
                  ∧ ∀ X ⊆ S, min a (size X) = M.r (X ∪ C) - M.r C :=
begin
  rw [has_unif_minor_def, iminor_of_iff_exists_embedding],
  split,
  { rintros ⟨ φ, C, hdisj, hr⟩,
    refine ⟨range φ, C, hdisj, _, λ X hX, _⟩,
    { rwa [← image_univ, size_image_emb, size_fin'_univ],  },
    convert hr (φ ⁻¹' X),
    rw [canonical_unif_r ha, size_preimage_embed_subset_range _ _ hX],
    rw image_preimage_eq_of_subset hX, },
  rintros ⟨S, C, hdisj, hsize, hr⟩,
  rw [eq_comm, ← size_fin' _ hb] at hsize,
  obtain ⟨φ, rfl⟩ := exists_emb_of_type_size_eq_size_set hsize,  
  refine ⟨φ, C, hdisj, λ F, _⟩,
  convert hr (φ '' F) (λ x, by tidy),
  rw [size_image_emb, canonical_unif_r ha],
end

lemma has_good_C_of_has_unif_minor (ha : 0 ≤ a) (hab : a ≤ b) :
  M.has_unif_minor a b →
    ∃ S C : set α,  disjoint S C
                  ∧ size S = b
                  ∧ (∀ X ⊆ S, min a (size X) = M.r (X ∪ C) - M.r C)
                  ∧ M.is_indep C
                  ∧ M.r C = M.r univ - a :=
begin
  rw [has_unif_minor_def, iminor_of_iff_exists_good_C],
  rintros ⟨ φ, C, hdisj, hr, hind, hrank⟩,
  refine ⟨range φ, C, (disjoint_iff_inter_eq_empty.mpr hdisj), _, λ X hX, _, hind, _⟩,
  { rw [← image_univ, size_image_emb, size_fin'_univ], exact le_trans ha hab,  },
  { convert hr (φ ⁻¹' X),
    rw [canonical_unif_r ha, size_preimage_embed_subset_range _ _ hX],
    rw image_preimage_eq_of_subset hX},
  rw [canonical_unif_r ha, ← type_size_eq, size_fin' _ (le_trans ha hab), min_eq_left hab] at hrank,
  linarith, 
end

def matroid.has_unif_restr (M : matroid α) (a b : ℤ) :=
  M.has_irestr (canonical_unif a b)

lemma has_unif_restr_def :
  M.has_unif_restr a b ↔ (canonical_unif a b).is_irestr_of M :=
iff.rfl

lemma has_unif_restr_iff (ha : 0 ≤ a) (hb : 0 ≤ b) :
  M.has_unif_restr a b ↔ ∃ S : set α, (size S = b) ∧ (∀ X ⊆ S, M.r X = min a (size X)) :=
begin
  rw [has_unif_restr_def, irestr_of_iff_exists_map], 
  split,
  { rintros ⟨φ, hr⟩,
    refine ⟨range φ, _, λ X hX, _⟩,
    { rw [← image_univ, size_image_emb], convert size_fin' _ hb},
    convert (hr (φ ⁻¹' X)).symm using 1,
    rw image_preimage_eq_of_subset hX,
    rw [canonical_unif_r ha, size_preimage_embed_subset_range _ _ hX],  },
  rintros ⟨S, hsize, hr⟩,
  rw [eq_comm, ← size_fin' _ hb] at hsize,
  obtain ⟨φ, rfl⟩ := exists_emb_of_type_size_eq_size_set hsize,  
  refine ⟨φ, λ F, _⟩,
  convert (hr (φ '' F) (λ x, by tidy)).symm using 1,
  rw [size_image_emb, canonical_unif_r ha],
end

lemma matroid.has_unif_minor_iff_si_has_unif_minor (ha : 2 ≤ a) :
  M.has_unif_minor a b ↔ (si M).has_unif_minor a b :=
(iminor_iff_iminor_si (canonical_unif_simple_of_two_le_r ha)).symm

lemma has_uniform_minor_of_has_unif_restriction (h : M.has_unif_restr a b):
  M.has_unif_minor a b :=
iminor_of_irestr h

def matroid.has_no_uniform_minor (M : matroid α)(a b : ℤ) :=
  ¬ M.has_unif_minor a b

def pminor_has_no_uniform_minor (ha : 1 ≤ a) (hb : 2 ≤ b) (hNM : N.is_pminor_of M):
  (M.has_no_uniform_minor a b) → (N.has_no_uniform_minor a b) :=
begin
  simp_rw [matroid.has_no_uniform_minor, matroid.has_unif_minor], contrapose!, intro hN,
  apply iminor_of_iminor_of_pminor _ hN hNM,
  rwa canonical_unif_loopless_iff (by linarith : 0 ≤ a) (by linarith : 1 ≤ b),
end

end uniform

section line

variables {α : Type*} [fintype α] {M : matroid α} {l a b: ℤ} {X Y L : set α}

/-- the property of not having a rank-2 uniform matroid on n elements as a minor -/
def matroid.has_no_line_minor (M : matroid α) (n : ℤ) :=
  ¬ M.has_unif_minor 2 n

lemma line_restr_of_simple_set (hl : 0 ≤ l)(hr : M.r L ≤ 2) (hL : M.is_simple_set L)
(hsize : l ≤ size L):
  M.has_unif_restr 2 l :=
begin
  rw has_unif_restr_iff (by norm_num : (0 : ℤ) ≤ 2) hl,
  obtain ⟨L', hL', hsizeL'⟩ := has_subset_of_size (by linarith : 0 ≤ l) hsize,
  refine ⟨L', hsizeL', λ X hXL', _⟩,
  rcases le_or_lt (size X) 2 with (hX | hX),
  { rw [rank_subset_simple_set hL (subset.trans hXL' hL') hX, min_eq_right hX]},
  rw min_eq_left (le_of_lt hX),
  refine le_antisymm (le_trans (M.rank_mono (subset.trans hXL' hL')) hr) _, 
  convert rank_subset_simple_set_lb hL (subset.trans hXL' hL'),
  rw min_eq_left (le_of_lt hX),
end

lemma line_restr_of_ε {L : set α}(hl : 0 ≤ l)(hr : M.r L ≤ 2)(hL : l ≤ M.ε L):
  M.has_unif_restr 2 l :=
begin
  rw ε_eq_largest_simple_subset at hL,
  obtain ⟨⟨L₀,hL₀⟩, h', -⟩ := max_spec (λ (S : M.simple_subset_of L), size (S : set α)),
  rw ← h' at hL,
  exact line_restr_of_simple_set hl (le_trans (M.rank_mono hL₀.2) hr) hL₀.1 hL,
end

lemma line_restr_ub_ε (hl : 0 ≤ l){L : set α}(hM : M.has_no_line_minor (l+2))(hL : M.is_line L):
  M.ε L ≤ l+1 :=
begin
  by_contra hn, push_neg at hn,
  refine hM (has_uniform_minor_of_has_unif_restriction
    (line_restr_of_ε (by linarith : 0 ≤ l+2) (hL.r.le) _)),
  have := (int.add_one_le_of_lt hn), 
  rwa [add_assoc] at this,
end





end line 