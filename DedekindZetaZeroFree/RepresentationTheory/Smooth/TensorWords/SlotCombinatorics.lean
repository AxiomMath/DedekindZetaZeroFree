module

public import DedekindZetaZeroFree.Eisenstein.ConstantTerms.Residual.UpperFinitePureTensors

@[expose] public section

noncomputable section
open scoped Classical BigOperators
namespace DedekindZetaZeroFree.FourierContinuation.ResidualPrincipalSlices
variable {ι : Type} [Fintype ι] [DecidableEq ι]
theorem slotWords_append (i : ι) (w u : List (MatrixLetter ι)) :
    slotWords i (w++u) = slotWords i w ++ slotWords i u := by
  induction w with
  | nil => rfl
  | cons b w hw => simp only [List.cons_append,slotWords,hw]; split_ifs <;> rfl

theorem slotWords_reverse (i : ι) (w : List (MatrixLetter ι)) :
    slotWords i w.reverse = (slotWords i w).reverse := by
  induction w with
  | nil => rfl
  | cons b w hw =>
    simp only [List.reverse_cons,slotWords_append,hw,slotWords]
    split_ifs <;> simp

theorem slotWords_lengths (w : List (MatrixLetter ι)) :
    ∑i, (slotWords i w).length = w.length := by
  induction w with
  | nil => simp [slotWords]
  | cons b w hw =>
    have he (i : ι) : (slotWords i (b::w)).length =
        (if b.1=i then 1 else 0) + (slotWords i w).length := by
      simp only [slotWords]
      split_ifs <;> simp [Nat.add_comm]
    simp_rw [he]
    rw [Finset.sum_add_distrib,hw]
    simp [Nat.add_comm]
end DedekindZetaZeroFree.FourierContinuation.ResidualPrincipalSlices

end
