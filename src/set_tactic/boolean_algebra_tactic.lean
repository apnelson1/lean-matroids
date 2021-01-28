import order.boolean_algebra
import order.zorn
import tactic.ext
import .extensionality
open_locale classical

namespace order.boolean_algebra

variables {α : Type*} [boolean_algebra α] {x y : α}

@[ext] structure filter (α : Type*) [boolean_algebra α] :=
(pred : set α)
(pred_top : pred ⊤)
(pred_inf : ∀ (x y : α), pred x → pred y → pred (x ⊓ y))
(pred_monotone : ∀ (x y : α), x ≤ y → pred x → pred y)

namespace filter

instance : partial_order (filter α) :=
{ le          := λ f g, f.pred ⊆ g.pred,
  le_refl     := λ f, set.subset.rfl,
  le_trans    := λ f g h, set.subset.trans,
  le_antisymm := λ f g h₁ h₂, filter.ext _ _ (set.subset.antisymm h₁ h₂) }

instance : has_inf (filter α) :=
⟨λ f g,
{ pred          := f.pred ∩ g.pred,
  pred_top      := by split; apply filter.pred_top,
  pred_inf      := λ x y ⟨h₁, h₂⟩ ⟨h₃, h₄⟩, by split; apply filter.pred_inf; assumption,
  pred_monotone := λ x y h₁ ⟨h₂, h₃⟩, by split; apply filter.pred_monotone; assumption }⟩

instance : semilattice_inf (filter α) :=
{ inf_le_left  := λ f g, set.inter_subset_left _ _,
  inf_le_right := λ f g, set.inter_subset_right _ _,
  le_inf       := λ f g h, set.subset_inter,
  .. filter.has_inf, .. filter.partial_order }

def principal (x : α) : filter α :=
{ pred          := λ y, x ≤ y,
  pred_top      := le_top,
  pred_inf      := λ y z, le_inf,
  pred_monotone := λ y z, function.swap le_trans }

instance : order_top (filter α) :=
{ top := principal ⊥,
  le_top := λ f x (h : f.pred x), bot_le,
  .. filter.partial_order }

instance : order_bot (filter α) :=
{ bot := principal ⊤,
  bot_le := λ f x (h : ⊤ ≤ x), (top_unique h).substr f.pred_top,
  .. filter.partial_order }

def insert (x : α) (f : filter α) : filter α :=
{ pred          := λ y, ∃ z, (f.pred z) ∧ (x ⊓ z ≤ y),
  pred_top      := ⟨⊤, f.pred_top, inf_le_right⟩,
  pred_inf      := λ y z ⟨y', h_fy', h_xy'⟩ ⟨z', h_fz', h_xz'⟩,
    ⟨y' ⊓ z',
     f.pred_inf _ _ h_fy' h_fz',
     le_inf
       (calc x ⊓ (y' ⊓ z') ≤ x ⊓ y' : inf_le_inf_left _ inf_le_left
        ...                ≤ y      : h_xy')
       (calc x ⊓ (y' ⊓ z') ≤ x ⊓ z' : inf_le_inf_left _ inf_le_right
        ...                ≤ z      : h_xz')⟩,
  pred_monotone := λ y z h_yz ⟨y', h_fy', h_xy'⟩, ⟨y', h_fy', le_trans h_xy' h_yz⟩ }

lemma mem_insert (x : α) (f : filter α) : (insert x f).pred x :=
⟨⊤, f.pred_top, inf_le_left⟩

lemma le_insert (x : α) (f : filter α) : f ≤ (insert x f) :=
λ y h, ⟨y, h, inf_le_right⟩

end filter

structure ultrafilter (α : Type*) [boolean_algebra α] extends filter α :=
(or_compl      : ∀ (x : α),   pred x ∨ pred xᶜ)
(not_and_compl : ∀ (x : α), ¬(pred x ∧ pred xᶜ))

variables {u : ultrafilter α}

namespace ultrafilter

instance : has_mem (ultrafilter α) α := ⟨λ u x, u.pred x⟩

lemma mem_monotone : x ≤ y → u ∈ x → u ∈ y :=
u.pred_monotone x y

lemma mem_top : u ∈ (⊤ : α) :=
u.pred_top

lemma not_mem_bot : u ∉ (⊥ : α) :=
λ h, u.not_and_compl ⊥ ⟨h, compl_bot.substr mem_top⟩

lemma mem_sup_left : u ∈ x → u ∈ (x ⊔ y) :=
mem_monotone le_sup_left

lemma mem_sup_right : u ∈ y → u ∈ (x ⊔ y) :=
mem_monotone le_sup_right

lemma or_of_mem_sup : u ∈ (x ⊔ y) → (u ∈ x) ∨ (u ∈ y) :=
λ h, or.imp_right
  (λ hc, mem_monotone
    (calc
      (x ⊔ y) ⊓ xᶜ = y ⊓ xᶜ : by rw [inf_sup_right, inf_compl_eq_bot, bot_sup_eq]
      ...          ≤ y      : inf_le_left)
    (u.pred_inf _ _ h hc))
  (u.or_compl x)

lemma inf_mem_left : u ∈ (x ⊓ y) → u ∈ x :=
λ h, mem_monotone inf_le_left h

lemma inf_mem_right : u ∈ (x ⊓ y) → u ∈ y :=
λ h, mem_monotone inf_le_right h

lemma mem_inf : u ∈ x → u ∈ y → u ∈ (x ⊓ y) :=
u.pred_inf x y

lemma exists_of_not_le : ¬(x ≤ y) → ∃ u, (u ∈ x) ∧ (u ∉ y) :=
λ h_not_le,
let filters := {f : filter α // f.pred x ∧ ¬(f.pred y)},
    le : filters → filters → Prop :=
      λ f g, f.val ≤ g.val,
    bot : filters :=
      ⟨filter.principal x, le_refl x, h_not_le⟩,
    bot_le {f : filters} : le bot f :=
      λ z (h_le : x ≤ z), f.val.pred_monotone x z h_le f.prop.left,
    bound c (hc : zorn.chain le c) : filters :=
      let c' := insert bot c,
          hc' := zorn.chain_insert hc (λ f _ _, or.inl bot_le),
          h_bot : c' bot := set.mem_insert bot c in
      ⟨{ pred          := λ z, ∃ f, (c' f) ∧ (f.val.pred z),
         pred_top      := ⟨bot, h_bot, (le_top : x ≤ ⊤)⟩,
         pred_inf      := λ z w ⟨f, h_cf, h_fz⟩ ⟨g, h_cg, h_gw⟩,
           or.elim
             (zorn.chain.total hc' h_cf h_cg)
             (λ h_fg, ⟨g, h_cg, g.val.pred_inf _ _ (h_fg h_fz) h_gw⟩)
             (λ h_gf, ⟨f, h_cf, f.val.pred_inf _ _ h_fz (h_gf h_gw)⟩),
         pred_monotone := λ z w h_zw ⟨f, h_cf, h_fz⟩,
           ⟨f, h_cf, f.val.pred_monotone _ _ h_zw h_fz⟩ },
       ⟨bot, h_bot, bot.prop.left⟩,
       (λ ⟨f, h_cf, h_fy⟩, f.prop.right h_fy)⟩,
    ⟨⟨m, h_mx, h_my⟩, is_max⟩ := zorn.exists_maximal_of_chains_bounded
      (λ c hc, ⟨bound c hc, λ f h_cf z h_fz, ⟨f, set.mem_insert_of_mem _ h_cf, h_fz⟩⟩)
      (λ f g h, set.subset.trans) in
⟨{ or_compl      := λ z,
     if h_z : (filter.insert z m).pred y
     then if h_zc : (filter.insert zᶜ m).pred y
          then let ⟨w,  h_mw,  h_zw⟩  := h_z,
                   ⟨wc, h_mwc, h_zwc⟩ := h_zc in
               false.elim (h_my (m.pred_monotone _ _
                 (calc
                   w ⊓ wc = (z ⊔ zᶜ) ⊓ (w ⊓ wc)              : by simp
                   ...    = (z ⊓ (w ⊓ wc)) ⊔ (zᶜ ⊓ (w ⊓ wc)) : inf_sup_right
                   ...    ≤ (z ⊓ w)        ⊔ (zᶜ ⊓ wc)       : sup_le_sup
                                                               (inf_le_inf_left _ inf_le_left)
                                                               (inf_le_inf_left _ inf_le_right)
                   ...    ≤ y                                : sup_le h_zw h_zwc)
                 (m.pred_inf _ _ h_mw h_mwc)))
          else or.inr
            ((is_max
              ⟨filter.insert zᶜ m, filter.le_insert zᶜ m h_mx, h_zc⟩
              (filter.le_insert zᶜ m))
            (filter.mem_insert zᶜ m))
     else or.inl
       ((is_max
          ⟨filter.insert z m, filter.le_insert z m h_mx, h_z⟩
          (filter.le_insert z m))
        (filter.mem_insert z m)),
   not_and_compl := λ z ⟨h_z, h_zc⟩,
     h_my (m.pred_monotone _ _ (by simp) (m.pred_inf _ _ h_z h_zc)),
   .. m },
 h_mx,
 h_my⟩

end ultrafilter

namespace extensionality
open ultrafilter



lemma rw_eq : (x = y) ↔ (x ≤ y) ∧ (y ≤ x) :=
le_antisymm_iff

lemma rw_le : (x ≤ y) ↔ ∀ u, u ∈ x → u ∈ y :=
⟨λ h u, mem_monotone h,
 λ h_forall, not_not.mp (λ h_not_le,
   let ⟨u, hx, hy⟩ := exists_of_not_le h_not_le in hy (h_forall u hx))⟩

lemma rw_bot : u ∈ (⊥ : α) ↔ false :=
iff_false_intro not_mem_bot

lemma rw_top : u ∈ (⊤ : α) ↔ true :=
iff_true_intro mem_top

lemma rw_sup : u ∈ (x ⊔ y) ↔ (u ∈ x) ∨ (u ∈ y) :=
⟨or_of_mem_sup,
 or.rec mem_sup_left mem_sup_right⟩

lemma rw_inf : u ∈ (x ⊓ y) ↔ (u ∈ x) ∧ (u ∈ y) :=
⟨λ h, ⟨inf_mem_left h, inf_mem_right h⟩,
 λ h, mem_inf h.left h.right⟩

lemma rw_compl : u ∈ xᶜ ↔ ¬(u ∈ x) :=
⟨(λ hc h, u.not_and_compl x ⟨h, hc⟩),
 (or.resolve_left (u.or_compl x))⟩

lemma rw_sdiff : u ∈ x \ y ↔ u ∈ x ∧ u ∉ y := begin
  rewrite sdiff_eq,
  rewrite <- rw_compl,  
  rw rw_inf,
end

instance boolalg_base_ext_lemmas (α : Type) [boolean_algebra α] 
  : (boolalg_ext_lemmas α (ultrafilter α)) := 
{
  simpl_eq := by apply rw_eq,
  ext_bot := by apply rw_bot,
  ext_sdiff := by apply rw_sdiff, 
  ext_le := by apply rw_le, 
  ext_meet := by apply rw_sup,
  ext_join := by apply rw_inf,
}

instance boolalg_base_ext_lemmas_compl (α : Type) [boolean_algebra α]  :
  (boolalg_ext_lemmas_compl  α (ultrafilter α)) :=
{
  ext_compl := by apply rw_compl,
}

instance boolalg_base_ext_lemmas_top (α : Type) [boolean_algebra α]  :
  (boolalg_ext_lemmas_top  α (ultrafilter α)) :=
{
  ext_top := by apply rw_top,
}

end extensionality

end order.boolean_algebra
