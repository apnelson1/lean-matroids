import .restriction
import mathlib.data.set.basic 

noncomputable theory
open_locale classical
open_locale big_operators

open set

namespace matroid_in

variables {α : Type*} {M : matroid_in α} {I J B C X Y : set α} {e f x y : α}

/-- The notion of 2-connectedness for graphs can
    be extended to matroids. For each element `e`
    of a matroid `M`, let
    `gamma_set(e) = { e } ∪ { f : M has a circuit containing both e and f }`.  -/
def gamma_set (M : matroid_in α) (e : α) := { e } ∪ { f | ∃ C, M.circuit C ∧ e ∈ C ∧ f ∈ C }

/-- Define the relation `gamma` on `E` by `e gamma f` if and only if
    `e ∈ gamma f` -/
def gamma (M : matroid_in α) (e f : α) := e ∈ M.gamma_set f

/-- `gamma` is an equivalence relation on `E(M)` -/
theorem gamma_refl (M : matroid_in α) (e : α) : M.gamma e e :=
by { left, exact mem_singleton e }

theorem gamma_symm (h : M.gamma e f) : M.gamma f e :=
begin
  cases h with h,
  { rw mem_singleton_iff.mp h,
    exact M.gamma_refl f },
  { rcases h with ⟨C, hC, fC, eC⟩,
    right,
    use [C, hC, eC, fC] }
end

lemma gamma_exists_circuit_of_neq (h : M.gamma e f) (h' : e ≠ f) :
  ∃ C, M.circuit C ∧ e ∈ C ∧ f ∈ C  :=
begin
  cases h with h,
  { have := eq_of_mem_singleton h,
    contradiction, },
  { obtain ⟨C, hC, hfC, heC⟩ := h,
    use [C, hC, heC, hfC], }
end

theorem gamma_trans (e f g : α)
  (hef : M.gamma e f) (hfg : M.gamma f g) : M.gamma e g :=
sorry

def direct_sum' (M₁ : matroid_in α) (M₂ : matroid_in α)
  (hE : M₁.ground ∩ M₂.ground = ∅) :
  matroid_in α :=
   matroid_of_indep
    (M₁.ground ∪ M₂.ground)
    (λ I, ∃ I₁ I₂, M₁.indep I₁ ∧ M₂.indep I₂ ∧ I = I₁ ∪ I₂)
    (by { use [∅, ∅, empty_indep _, empty_indep _], simp, })
    (begin
      rintro I J ⟨J₁, J₂, ⟨hJ₁, hJ₂, Jeq⟩⟩ hIJ,
      use [I ∩ J₁, I ∩ J₂, hJ₁.subset (inter_subset_right I J₁),
        hJ₂.subset (inter_subset_right I J₂)],
      rw [←inter_distrib_left, ←Jeq],
      symmetry, exact inter_eq_self_of_subset_left hIJ,
    end)
    (begin
      dsimp at hE,
      rintro I X ⟨I₁, I₂, hI₁, hI₂, Ieq⟩ hI_not_max ⟨⟨X₁, X₂, hX₁, hX₂, Xeq⟩, hX_max⟩,

      -- at least one of I₁, I₂ not maximal
      have hI : ¬ M₁.base I₁ ∨ ¬ M₂.base I₂,
      {
        by_contra', obtain ⟨h₁, h₂⟩ := this,
        apply hI_not_max,
        split,
        { use [I₁, I₂, hI₁, hI₂, Ieq], },
        { simp only [exists_and_distrib_left],
          rintro S ⟨S₁, hS₁, S₂, hS₂, Seq⟩ hIS,
          have hI₁S₁ : I₁ ⊆ S₁,
          { subst Seq, subst Ieq,
            rintro e he,
            cases hIS ((subset_union_left I₁ I₂) he) with g,
            { exact g, },
            { exfalso,
              have : e ∈ (M₁.E ∩ M₂.E) := ⟨hI₁.subset_ground he, hS₂.subset_ground h⟩,
              rw hE at this, exact not_mem_empty e this } },
          have hI₂S₂ : I₂ ⊆ S₂,
          { subst Seq, subst Ieq,
            rintro e he,
            cases hIS ((subset_union_right I₁ I₂) he) with g,
            { exfalso,
              have : e ∈ (M₁.E ∩ M₂.E) := ⟨hS₁.subset_ground g, hI₂.subset_ground he⟩,
              rw hE at this, exact not_mem_empty e this },
            { exact h, } },
          rw [Seq, Ieq, h₁.eq_of_subset_indep hS₁ hI₁S₁, h₂.eq_of_subset_indep hS₂ hI₂S₂] }
      },

      -- both X₁, X₂ maximal
      have hX₁base : M₁.base X₁,
      { by_contra h,
        obtain ⟨B, hB⟩ := M₁.exists_base,
        obtain ⟨e, he, heX₁⟩ := hX₁.exists_insert_of_not_base h hB,
        apply he.2,
        have h₁ : ((insert e X₁) ∪ X₂) ⊆ X,
        { apply hX_max,
          { use [(insert e X₁), X₂, heX₁, hX₂], },
          { rw Xeq, exact union_subset_union (subset_insert e X₁) (subset_refl X₂), } },
        have h₂ := ((insert e X₁).subset_union_left X₂) (mem_insert e X₁),
        rw [Xeq, union_subset_iff] at h₁,
        obtain ⟨h₁, _⟩ := h₁,
        have : (insert e X₁) ⊆ X₁,
        { -- TODO: rephrase in terms of sets
          rintro x hx,
          cases hx with hx,
          { cases h₁ (mem_insert e X₁) with g,
            { rw hx, exact g },
            { exfalso,
              have : e ∈ M₁.E ∩ M₂.E := ⟨hB.subset_ground he.1, hX₂.subset_ground h_1⟩,
              rw hE at this, exact not_mem_empty e this, } },
          { exact hx, } },
        exact this (mem_insert e X₁), },
      have hX₂base : M₂.base X₂,
      { sorry, },

      cases hI with hI,
      { obtain ⟨e, he, heI₁⟩ := hI₁.exists_insert_of_not_base hI hX₁base,
        use e,
        split,
        { split,
          { rw [Xeq, mem_union],
            left, use he.1 },
          { have : e ∉ I₁ := he.2,
            have : e ∉ I₂,
            { intro h,
              have : e ∈ M₁.E ∩ M₂.E := ⟨heI₁.subset_ground (mem_insert e I₁), hI₂.subset_ground h⟩,
              rw hE at this, exact not_mem_empty e this, },
            
            rw [Ieq, mem_union],
            intro g, cases g with g;
            contradiction } },
        { use [(insert e I₁), I₂, heI₁, hI₂],
          rw [Ieq, ←insert_union] } },
        { obtain ⟨e, he, heI₂⟩ := hI₂.exists_insert_of_not_base hI hX₂base,
          use e,
          split,
          { split,
            { rw [Xeq, mem_union],
              right, use he.1 },
            { have : e ∉ I₂ := he.2,
              have : e ∉ I₁,
              { intro h,
                have : e ∈ M₁.E ∩ M₂.E := ⟨hI₁.subset_ground h, heI₂.subset_ground (mem_insert e I₂)⟩,
                rw hE at this,
                exact not_mem_empty e this, },
              rw [Ieq, mem_union],
              intro g, cases g with g;
              contradiction } },
          { use [I₁, (insert e I₂), hI₁, heI₂],
            rw [Ieq, union_comm _ (insert _ _), insert_union, union_comm],
          } },
    end)
    (begin
      rintro X Y ⟨X₁, X₂, ⟨hX₁, hX₂, Xeq⟩⟩ hXY,
      subst Xeq,

      have : X₁ ⊆ Y ∩ M₁.E := subset_inter ((subset_union_left X₁ X₂).trans hXY)
                                (hX₁.subset_ground),
      obtain ⟨B₁, ⟨hB₁, hX₁B₁⟩⟩ := hX₁.subset_basis_of_subset this,

      have : X₂ ⊆ Y ∩ M₂.E := subset_inter ((subset_union_right X₁ X₂).trans hXY)
                                (hX₂.subset_ground),
      obtain ⟨B₂, ⟨hB₂, hX₂B₂⟩⟩ := hX₂.subset_basis_of_subset this,

      use B₁ ∪ B₂,
      split,
      { simp only [exists_and_distrib_left, union_subset_iff, mem_set_of_eq],
        use [B₁, hB₁.indep, B₂, hB₂.indep, (hX₁B₁.trans (subset_union_left B₁ B₂)),
            (hX₂B₂.trans (subset_union_right B₁ B₂)), hB₁.subset.trans (inter_subset_left Y (M₁.E)),
            hB₂.subset.trans (inter_subset_left Y (M₂.E))],
      },
      { simp only [exists_and_distrib_left, union_subset_iff, mem_set_of_eq,
                and_imp, forall_exists_index],
        rintro S T₁ hT₁ T₂ hT₂ rfl hS₁ hS₂ hSY hB₁S hB₂S,

        have B₁eq : B₁ = T₁,
        { have hB₁T₁ : B₁ ⊆ T₁,
          { -- TODO: rephrase only in terms of sets
            rintro b hb,
            have hb' := hB₁S hb,
            cases hb' with hb',
            { exact hb' },
            { exfalso,
              have : b ∈ M₁.E ∩ M₂.E := ⟨hB₁.subset_ground_left hb, hT₂.subset_ground hb'⟩,
              simp only [ground_eq_E] at hE,
              rw hE at this,
              exact not_mem_empty b this }
          },
          have hT₁' : T₁ ⊆ Y ∩ M₁.E := subset_inter ((subset_union_left T₁ T₂).trans hSY) (hT₁.subset_ground),
          exact hB₁.eq_of_subset_indep hT₁ hB₁T₁ hT₁' },
        have B₂eq : B₂ = T₂,
        { have hB₂T₂ : B₂ ⊆ T₂,
          { rintro b hb,
            have hb' := hB₂S hb,
            cases hb' with hb',
            { exfalso,
              have : b ∈ M₁.E ∩ M₂.E := ⟨hT₁.subset_ground hb', hB₂.subset_ground_left hb⟩,
              dsimp at hE,
              rw hE at this,
              exact not_mem_empty b this },
            { exact hb' },
          },
          have hT₂' : T₂ ⊆ Y ∩ M₂.E := subset_inter ((subset_union_right T₁ T₂).trans hSY) (hT₂.subset_ground),
          exact hB₂.eq_of_subset_indep hT₂ hB₂T₂ hT₂', },
        rw [B₁eq, B₂eq]} 
    end)
    (begin
      rintro I ⟨I₁, I₂, ⟨hI₁, hI₂, Ieq⟩⟩,
      rw [ground_eq_E, Ieq, union_subset_iff],
      exact ⟨(hI₁.subset_ground).trans ((M₁.E).subset_union_left (M₂.E)),
             (hI₂.subset_ground).trans ((M₁.E).subset_union_right (M₂.E))⟩,
    end)

end matroid_in
