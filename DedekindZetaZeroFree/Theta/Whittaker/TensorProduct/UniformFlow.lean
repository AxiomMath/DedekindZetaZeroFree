module

public import DedekindZetaZeroFree.Theta.Whittaker.TensorProduct.ProductJets

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.SheetRescaling.WeylTensorTransport
open MomentSources NumberField
open scoped Classical
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)
variable {N : TraceHaarTransport R} (C : JointDigitDescentSources R N)

lemma uniform_exp_add (t u : ℝ) :
    R.A.radialSection (Real.exp (t + u)) (Real.exp_pos _) =
      R.A.radialSection (Real.exp t) (Real.exp_pos _) *
        R.A.radialSection (Real.exp u) (Real.exp_pos _) := by
  simpa only [Real.exp_add] using
    R.A.radialSection_mul _ _ (Real.exp_pos t) (Real.exp_pos u)

theorem archJet_rebase (v : R.A.UnitQuotient) (w : InfinitePlace F)
    (z : w.Completionˣ) (u : ℝ) (j : ℕ) :
    iteratedDeriv j (fun t : ℝ => ThetaExpansion.normalizedLocalWeylValue R C v (Sum.inl w)
      (z * (R.A.radialSection (Real.exp t) (Real.exp_pos t)).1 w)) u =
    ThetaExpansion.localWeylArchJet R C v w j
      (z * (R.A.radialSection (Real.exp u) (Real.exp_pos u)).1 w) := by
  unfold ThetaExpansion.localWeylArchJet
  have he : (fun t : ℝ => ThetaExpansion.normalizedLocalWeylValue R C v (Sum.inl w)
      ((z * (R.A.radialSection (Real.exp u) (Real.exp_pos u)).1 w) *
        (R.A.radialSection (Real.exp t) (Real.exp_pos t)).1 w)) =
      fun t : ℝ => ThetaExpansion.normalizedLocalWeylValue R C v (Sum.inl w)
        (z * (R.A.radialSection (Real.exp (t + u)) (Real.exp_pos (t + u))).1 w) := by
    funext t
    rw [uniform_exp_add]
    simp only [Prod.fst_mul, Pi.mul_apply]
    congr 1
    ac_rfl
  rw [he]
  have h := congrFun (iteratedDeriv_comp_add_const j
    (fun t : ℝ => ThetaExpansion.normalizedLocalWeylValue R C v (Sum.inl w)
      (z * (R.A.radialSection (Real.exp t) (Real.exp_pos t)).1 w)) u) 0
  simpa only [zero_add] using h.symm

theorem finite_value_radial (v : R.A.UnitQuotient) (p : R.A.Sf) (z : R.A.G) (u : ℝ) :
    ThetaExpansion.normalizedLocalWeylValue R C v (Sum.inr p.val)
      ((z * R.A.radialSection (Real.exp u) (Real.exp_pos u)).2 p) =
    ThetaExpansion.normalizedLocalWeylValue R C v (Sum.inr p.val) (z.2 p) := by
  have he : (z * R.A.radialSection (Real.exp u) (Real.exp_pos u)).2 p = z.2 p := by
    change z.2 p * 1 = z.2 p
    exact mul_one _
  rw [he]

theorem arch_product_jet_le (v : R.A.UnitQuotient) (z : R.A.G)
    (hf : ∀ w : InfinitePlace F, ContDiff ℝ 2 (fun t : ℝ =>
      ThetaExpansion.normalizedLocalWeylValue R C v (Sum.inl w)
        (z.1 w * (R.A.radialSection (Real.exp t) (Real.exp_pos t)).1 w)))
    (u : ℝ) (j : ℕ) (hj : j ≤ 2) :
    ‖iteratedDeriv j (fun t : ℝ => ∏ w : InfinitePlace F,
      ThetaExpansion.normalizedLocalWeylValue R C v (Sum.inl w)
        (z.1 w * (R.A.radialSection (Real.exp t) (Real.exp_pos t)).1 w)) u‖ ≤
      4 ^ Fintype.card (InfinitePlace F) *
        ∑ a : InfinitePlace F → Fin 3, ∏ w : InfinitePlace F,
          ‖ThetaExpansion.localWeylArchJet R C v w (a w).val
            ((z * R.A.radialSection (Real.exp u) (Real.exp_pos u)).1 w)‖ := by
  have h := norm_uniform_product_jet_le
    (fun w t => ThetaExpansion.normalizedLocalWeylValue R C v (Sum.inl w)
      (z.1 w * (R.A.radialSection (Real.exp t) (Real.exp_pos t)).1 w)) hf u j hj
  simpa only [archJet_rebase, Prod.fst_mul, Pi.mul_apply] using h

end DedekindZetaZeroFree.SheetRescaling.WeylTensorTransport

end
