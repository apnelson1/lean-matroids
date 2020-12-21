import .basic
namespace boolalg 
-- Singles
local attribute [instance] classical.prop_decidable

variables {A : boolalg}

def single (A : boolalg): Type := {X : A // size X = 1}

instance coe_single {A : boolalg} : has_coe (single A) A := ⟨λ e, e.val⟩  

def elem : (single A) → A → Prop := λ e X, (e:A) ⊆ X 
def nonelem : (single A) → A → Prop := λ e X, ¬elem e X 

infix ∈ := elem 
infix ∉ := nonelem 

@[simp] lemma nonelem_simp {e : single A}{X : A}: 
  ¬(e ∈ X) ↔ e ∉ X := by refl  

lemma elem_iff {e : single A}{X : A} :
   e ∈ X ↔ (e:A) ⊆ X := 
  by unfold elem

lemma nonelem_iff {e : single A}{X : A} : 
  e ∉ X ↔ ¬(e:A) ⊆ X := 
  by trivial 

@[simp] lemma size_single {A : boolalg} (e : single A) :
   size (e : A) = 1 := e.2 

@[simp] lemma single_ne_bot (e : single A) : 
  (e:A) ≠ ⊥ := 
  λ h, by {have := size_single e, rw [h,size_bot] at this, linarith}

@[simp] lemma nonelem_bot (e : single A) : 
  e ∉ (⊥:A) := 
  by {rw nonelem_iff, intro h, replace h := size_monotone h, simp at h, linarith}

@[simp] lemma nonelem_compl (e : single A) :
  e ∉ (e:A)ᶜ := 
  λ h, single_ne_bot e (subset_own_compl h)

lemma nonempty_has_elem {X : A}  : 
  X ≠ ⊥ → ∃ e, e ∈ X := 
  λ hX, by {rcases single_subset_nonempty hX with ⟨Y,Z ,⟨hI,hU,h1⟩⟩, use ⟨Y,h1⟩, 
                rw ←hU, exact subset_union_left Y Z}

lemma nonempty_iff_has_elem {X : A} : 
  X ≠ ⊥ ↔ ∃ e, e ∈ X :=
  ⟨λ h, nonempty_has_elem h, λ h, λ hb, by {cases h with e he, rw hb at he, exact nonelem_bot e he}⟩ 

lemma size_pos_has_elem {X : A}: 
  0 < size X → ∃ e, e ∈ X := 
  λ h, (nonempty_iff_has_elem.mp (λ h', by {rw [h',size_bot] at h, exact lt_irrefl 0 h}))

lemma size_pos_iff_has_elem {X : A}: 
  0 < size X ↔ ∃ e, e ∈ X := 
  ⟨λ h, size_pos_has_elem h, λ h, by {cases h with e he, have := size_monotone he, rw size_single at this, linarith}⟩ 

lemma size_zero_iff_has_no_elem {X : A}:
  size X = 0 ↔ ¬ ∃ e, e ∈ X := 
  begin
    rw [iff.comm, ←not_iff, ←size_pos_iff_has_elem, not_iff], 
    refine ⟨λ h, _, λ h, by linarith ⟩ ,
    linarith [size_nonneg X, not_lt.mp h]
  end

lemma nested_singles_eq {e f: single A} :
  (e: A) ⊆ (f :A) → e = f :=
  begin
    intro hef, ext, refine eq_of_eq_size_subset hef _,
    calc _ = 1 :size_single e ... = _: (size_single f).symm, 
  end

lemma nonelem_disjoint {e : single A} {X : A}: 
  e ∉ X → (e ∩ X :A) = ⊥ :=
  begin
    intro heX, by_contra, rcases nonempty_has_elem a with ⟨f,hf⟩, 
    rcases subset_of_inter_mp hf with ⟨hfe, hfx⟩, 
    rw nested_singles_eq hfe at hfx, exact heX hfx, 
  end

lemma nonelem_disjoint_iff {e : single A} {X : A}: 
  e ∉ X ↔ (e ∩ X : A) = ⊥ := 
  by {refine ⟨λ h, nonelem_disjoint h, λ h he, _⟩, rw [elem_iff, subset_def_inter, h, eq_comm] at he, exact single_ne_bot _ he}

lemma inter_distinct_singles {e f : single A}: 
  e ≠ f → (e ∩ f : A) = ⊥ := 
  λ hef, by {apply nonelem_disjoint, exact λ h, hef (nested_singles_eq h)} 

lemma elem_compl_iff {X : A}{e : single A} :
  e ∈ Xᶜ ↔ e ∉ X := 
  begin
    refine ⟨λ h, λ he, _, λ h, _⟩, 
    have := subset_of_inter_mpr  he h, rw inter_compl at this, have := size_monotone this, linarith [size_single e, size_bot A],   
    have := nonelem_disjoint h, rw ← subset_of_compl_iff_disjoint at this, assumption,  
  end

lemma nonelem_compl_iff {X : A}{e : single A} :
   e ∉ Xᶜ ↔ e ∈ X  := 
  by {rw ←elem_compl_iff, rw [compl_compl]}

lemma elem_union_iff {e : single A} {X Y : A} : 
  e ∈ X ∪ Y ↔ e ∈ X ∨ e ∈ Y :=
   begin 
     refine ⟨λ h, _, λ h, _⟩, by_contra, push_neg at a, 
     repeat {rw [nonelem_simp] at a, rw ←elem_compl_iff at a}, 
     have h' := subset_of_inter_mpr a.1 h, nth_rewrite 1 ←(compl_compl X) at h', 
     rw [inter_compl_union, inter_comm] at h', 
     exact single_ne_bot _ (subset_of_set_and_compl (subset_trans h' (inter_subset_left Y Xᶜ)) a.2),
     cases h, exact subset_trans h (subset_union_left X Y), 
     exact subset_trans h (subset_union_right X Y)
   end

lemma nonelem_inter_iff {e : single A} {X Y : A} :
   e ∉ X ∩ Y ↔ e ∉ X ∨ e ∉ Y := 
  by rw [←elem_compl_iff, compl_inter, elem_union_iff, elem_compl_iff, elem_compl_iff] 

lemma elem_diff_iff {e : single A}{X Y : A} : 
  e ∈ X \ Y ↔ e ∈ X ∧ e ∉ Y :=
  begin
    refine ⟨λ h ,⟨subset_trans h (diff_subset _ _),λ heY,_⟩, λ h, _⟩, 
    have := subset_of_inter_mpr  h heY, rw diff_inter at this, 
    linarith [size_monotone this, size_bot A, size_single e], 
    rw [diff_def, elem_iff, subset_of_inter_iff], 
    rw [ ←elem_compl_iff, elem_iff, elem_iff] at h, exact h
  end

lemma subset_iff_elems_contained {X Y : A} :
  X ⊆ Y ↔ ∀ e, e ∈ X → e ∈ Y := 
  begin
    rw [←diff_bot_iff_subset, ←not_iff_not, (_: ¬(X \ Y) = ⊥ ↔ X\Y ≠ ⊥),nonempty_iff_has_elem],
    simp_rw elem_diff_iff, rw not_forall, simp_rw not_imp, exact iff.rfl, exact iff.rfl, 
  end


lemma elem_subset {X Y: A}{e : single A}:
  X ⊆ Y → e ∈ X → e ∈ Y := 
  λ h he, subset_iff_elems_contained.mp h e he 


lemma nonelem_of_nonelem_diff {X Y : A}{e : single A} :
  e ∉ X \ Y → e ∉ Y → e ∉ X := 
  λ hXY hY hX, by {rw ←elem_compl_iff at hY, have := subset_of_inter_mpr hX hY, 
                                            rw ←diff_def at this,  exact hXY this }


lemma nonelem_diff_of_nonelem {X : A}(Y : A){e : single A}: 
  e ∉ X → e ∉ X\Y :=
  by {repeat {rw nonelem_iff}, rw not_imp_not, exact elem_subset (diff_subset X Y)}


lemma eq_iff_same_elems {X Y : A} :
  X = Y ↔ ∀ e, e ∈ X ↔ e ∈ Y :=
  begin
    refine ⟨λ h, λ e, by rw h, λ h, subset_antisymm _ _ ⟩, 
    rw subset_iff_elems_contained, exact λ e, (h e).mp, 
    rw subset_iff_elems_contained, exact λ e, (h e).mpr
  end

lemma nonelem_removal (X : A)(e : single A) :
  e ∉ X \ e := 
  λ h, by {rw [diff_def] at h, from nonelem_compl _ (subset_trans h (inter_subset_right _ _))}

lemma subset_of_removal {X Y : A}{e : single A} :
  X ⊆ Y → e ∉ X → X ⊆ Y \ e :=
  λ hXY heX, by {rw [diff_def], rw [←elem_compl_iff] at heX, exact subset_of_inter_mpr hXY (subset_compl_right heX)}


--lemma removal_subset_of {X Y : A}{e : single A} :
--  X ⊆ Y → 

lemma subset_of_subset_add_nonelem {X Y: A}{e : single A} :
  X ⊆ Y ∪ e → e ∉ X → X ⊆ Y :=
  begin
      intros hXY heX, 
      simp only [subset_def_inter] at hXY ⊢, 
      rw [nonelem_disjoint_iff, inter_comm] at heX,
      rw [inter_distrib_left, heX, union_bot] at hXY, 
      from hXY, 
  end


lemma removal_subset_of {X Y : A}{e : single A} :
  X ⊆ Y ∪ e → X \ e ⊆ Y :=
  begin
    intro h, 
    simp only [subset_def_inter, diff_def] at h ⊢, 
    nth_rewrite 1 ← h,
    rw [inter_distrib_left, inter_distrib_right, inter_assoc _ (e:A), inter_right_comm _ _ Y], 
    simp only [inter_compl, union_bot, inter_bot], 
  end

lemma ssub_of_add_compl {X : A} {e : single A} : 
  e ∈ Xᶜ → X ⊂ X ∪ e := 
  begin
     refine λ hXe, ⟨subset_union_left _ _, _⟩, intro h, rw [h, compl_union] at hXe, 
     have ebot := subset_trans hXe (inter_subset_right Xᶜ _), 
     rw [subset_def_inter, inter_compl] at ebot,  
     have := size_single e, rw ←ebot at this, linarith [size_bot A], 
  end

lemma ssub_of_add_nonelem {X : A} {e : single A}: 
  e ∉ X → X ⊂ X ∪ e := 
  λ hXe, ssub_of_add_compl (elem_compl_iff.mpr hXe)

lemma ssubset_of_add_nonelem_iff {X : A} {e : single A} :
  e ∉ X ↔ X ⊂ X ∪ e :=
  by {refine ⟨λ h, ssub_of_add_nonelem h, λ h, λ hex, _⟩, rw [elem_iff, subset_def_union, union_comm] at hex, rw hex at h, from ssubset_irrefl _ h}

lemma add_elem {X : A} {e : single A}: 
  e ∈ X → X ∪ e = X := 
  λ h, by {have := subset_def_union_mp h, rw union_comm at this, assumption}

lemma elem_diff_ssubset {X Y : A} : 
  X ⊂ Y → ∃ e, e ∈ Y \ X :=
  λ h, by {have := ssubset_diff_nonempty h, rw ←nonempty_iff_has_elem, assumption}

lemma elem_only_larger_ssubset {X Y : A} :
  X ⊂ Y → ∃ e, e ∈ Y ∧ e ∉ X :=
  λ h, by {have := elem_diff_ssubset h, simp_rw elem_diff_iff at this, assumption}


lemma add_compl_single_size {X : A} {e : single A} :
  e ∈ Xᶜ → size (X ∪ e) = size X + 1 := 
begin
  intro hXe, have := size_modular X e, 
  rw [inter_comm X, nonelem_disjoint (elem_compl_iff.mp hXe), size_single, size_bot] at this, 
  linarith, 
end

lemma add_nonelem_size {X : A} {e : single A}: 
  e ∉ X →  size (X ∪ e) = size X + 1 := 
  λ hXe, by {apply add_compl_single_size, exact elem_compl_iff.mpr hXe}

lemma compl_single_remove {X : A} {e : single A} : 
  e ∈ X → (X \ e)ᶜ = Xᶜ ∪ e := 
  λ _, by rw [diff_def, compl_inter, compl_compl]

lemma remove_add_elem {X : A} {e : single A}: 
  e ∈ X → (X\e) ∪ e = X := 
  λ heX, by {rw [elem_iff, subset_def_union,union_comm] at heX, 
             rw [diff_def, union_distrib_right, union_compl_left, inter_top, heX]}
   
lemma add_remove_nonelem {X : A} {e : single A}: 
  e ∉ X → (X ∪ e) \ e = X := 
  begin
    intro h, 
    rw [←elem_compl_iff, elem_iff, subset_def_union] at h, 
    rw [diff_def, inter_distrib_right], 
    simp only [inter_compl, union_bot], 
    rw [←compl_compl_inter_left, inter_comm, compl_inj_iff] at h, 
    from h, 
  end

lemma remove_single_size {X :A}{e : single A} :
  e ∈ X → size (X \ e) = size X - 1 := 
begin
  intro heX, 
  have h: e ∈ (X\e)ᶜ := by {rw compl_single_remove heX, apply subset_union_right}, 
  nth_rewrite 1 ←remove_add_elem  heX, linarith [add_compl_single_size h], 
end

lemma remove_single_subset (X : A) (e : single A) : 
  X \ e ⊆ X := 
  diff_subset X e 

lemma nonelem_of_subset_remove_single (X : A) (e : single A):
  X ⊆ X \ e → e ∉ X :=
  λ h h', nonelem_removal _ e (subset_trans h' h)

lemma remove_single_ssubset {X : A} {e : single A} :
  e ∈ X → X \ e ⊂ X := 
  λ heX, ⟨diff_subset _ _, λ h, by {have := remove_single_size heX, rw h at this, linarith}⟩

lemma nonbot_single_removal {X : A}:
  X ≠ ⊥ → ∃ Y :A, Y ⊂ X ∧ size Y = size X - 1 := 
  λ hX, by {cases nonempty_has_elem hX with e he, exact ⟨X\e, ⟨remove_single_ssubset he,remove_single_size he⟩ ⟩}

lemma nontop_single_addition {X : A}:
  X ≠ ⊤ → ∃ Y, X ⊂ Y ∧ size Y = size X + 1 := 
  begin
    intro hX, rcases nonbot_single_removal (λ h, _ : Xᶜ ≠ ⊥) with ⟨Y, ⟨h₁,h₂⟩ ⟩, 
    refine ⟨Yᶜ , ⟨ssubset_compl_right h₁, _⟩⟩,
    linarith [size_compl X, size_compl Y], 
    exact hX (top_of_compl_bot h), 
  end

lemma add_from_nonempty_diff {X Y : A} :
  X ⊂ Y ↔ ∃e, e ∉ X ∧ X ∪ e ⊆ Y := 
  begin
    refine ⟨λ h,_, λ h, _⟩, 
    cases nonempty_has_elem (ssubset_diff_nonempty h) with e he, use e, 
    exact ⟨(elem_diff_iff.mp he).2, union_of_subsets h.1 (subset_trans he (diff_subset _ _))⟩ ,  
    rcases h with ⟨e,⟨he1,he2⟩⟩, 
    exact ssubset_subset_trans (ssub_of_add_nonelem he1) he2,
  end

 
lemma aug_of_ssubset {X Y : A} : 
  X ⊂ Y → ∃ Z (e : single A), X ⊆ Z ∧ Z ⊂ Y ∧ Z ∪ e = Y :=
  begin
    intro hXY, 
    rcases elem_only_larger_ssubset hXY with ⟨e, ⟨heY, heX⟩⟩, 
    refine ⟨Y \ e, e, ⟨subset_of_removal hXY.1 heX ,⟨ _, _⟩ ⟩⟩,
    from remove_single_ssubset heY, 
    from remove_add_elem heY, 
  end 

lemma exchange_comm {X : A}{e f : single A} : 
  e ∈ X → f ∉ X → (X \ e) ∪ f = (X ∪ f) \ e := 
  begin
    intros he hf, 
    simp only [diff_def], rw [inter_distrib_right],
    have : (f ∩ eᶜ : A) = f := 
      by {rw [←subset_def_inter, ←disjoint_iff_subset_compl, inter_distinct_singles], by_contra h, push_neg at h, rw h at hf, from hf he},
    rw this, 
  end

lemma exchange_size {X : A}{e f : single A} : 
  e ∈ X → f ∉ X → size ((X \ e) ∪ f) = size X := 
  λ he hf, by linarith [add_nonelem_size (nonelem_diff_of_nonelem (e:A) hf),remove_single_size he]

lemma exchange_pair_sizes {X Y : A}{e f : single A}: 
  size X = size Y → e ∈ X\Y → f ∈ Y \ X → size ((X\e) ∪ f) = size ((Y \ f) ∪ e) :=
  λ h he hf, by {rw elem_diff_iff at he hf, rw [exchange_size hf.1 he.2, exchange_size he.1 hf.2], exact h}

lemma size_union_distinct_singles {e f : single A}: 
  e ≠ f → size (e ∪ f :A) = 2 :=
  begin
    intros hef, 
    have : ¬((e:A) ⊆ (f:A)) := λ h, hef (nested_singles_eq h), 
    have := add_nonelem_size this, 
    rw [union_comm, size_single] at this, 
    linarith, 
  end 

lemma size_union_singles_lb (e f : single A): 
  1 ≤ size (e ∪ f : A) := 
  by {linarith [size_monotone (subset_union_left (e:A) f), size_single e]}

lemma size_union_singles_ub (e f : single A):
  size (e ∪ f :A) ≤ 2 := 
  by {by_cases e = f, rw [h, union_idem, size_single], linarith, linarith [size_union_distinct_singles h]}

lemma subset_single {e : single A}{X : A} :
  X ⊆ e → X = ⊥ ∨ X = e := 
  begin
    intro h, cases lt_or_ge 0 (size X), 
    apply or.inr, exact eq_of_eq_size_subset h (by linarith [size_single e, size_monotone h]), 
    apply or.inl, exact (size_zero_bot (by linarith [size_nonneg X])),
  end

lemma ssubset_pair {e f : single A}{X : A}:
  X ⊂ (e ∪ f : A) → X = ⊥ ∨ (X = e) ∨ (X = f) :=
  begin
    intro h, cases h with hs hne, rw [subset_def_inter, inter_distrib_left] at hs,
    cases subset_single (inter_subset_right X e),
    rw [h, bot_union, ←subset_def_inter] at hs, cases subset_single hs, exact or.inl h_1, apply or.inr, exact or.inr h_1,
    rw [inter_comm, ←subset_def_inter] at h, apply or.inr, cases subset_single (inter_subset_right X f),
    rw [h_1, union_bot, ←subset_def_inter] at hs,  exact or.inl (subset_antisymm hs h), 
    rw [subset_def_inter, inter_comm] at h,
    rw [h_1, h] at hs, exfalso, exact hne hs.symm, 
  end

lemma equal_or_single_in_diff {X Y : A} :
  size X = size Y → X = Y ∨  ∃ e, e ∈ X \ Y :=
  begin
    intros hs, by_contra h, rw not_or_distrib at h, cases h with h1 h2, 
    rw ←nonempty_iff_has_elem at h2, push_neg at h2,  
    rw diff_bot_iff_subset at h2, 
    from h1 (eq_of_eq_size_subset h2 hs),
  end

end boolalg 