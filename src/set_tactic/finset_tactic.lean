import data.finset.basic
import data.fintype.basic 
import extensionality

namespace extensionality
instance finset_ext_lemmas (T : Type) [decidable_eq T] :
  (boolalg_ext_lemmas (finset T) T) :=
{
  simpl_eq := by tidy,
  ext_bot := by tidy,
  ext_sdiff := by tidy,
  ext_le := by tidy, 
  ext_meet := by tidy,
  ext_join := by simp only [finset.inf_eq_inter, forall_const, iff_self, finset.mem_inter, forall_true_iff],
}

instance finset_ext_lemmas_compl (T : Type) [fintype T] [decidable_eq T] :
  (boolalg_ext_lemmas_compl (finset T) T) :=
{
  ext_compl := by apply finset.mem_compl
}

instance finset_ext_lemmas_top (T : Type) [fintype T] [decidable_eq T] :
  (boolalg_ext_lemmas_top (finset T) T) :=
{
  ext_top := by unfold_projs; finish,
}
end extensionality