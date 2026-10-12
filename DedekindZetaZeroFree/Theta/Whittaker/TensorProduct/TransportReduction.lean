module

public import DedekindZetaZeroFree.Theta.Whittaker.TensorProduct.LocalRegularity
public import DedekindZetaZeroFree.Theta.Whittaker.TensorProduct.RadialPhase
public import DedekindZetaZeroFree.Theta.Whittaker.TensorProduct.Normalization

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.SheetRescaling.WeylTensorTransport
open MomentSources NumberField MeasureTheory
open scoped Classical Topology
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)
variable {N : TraceHaarTransport R} (C : JointDigitDescentSources R N)

theorem same_source_transport_of_weyl_factorization
    (hfactor : ∀ (v : R.A.UnitQuotient) (z : R.A.G),
      fourier R C.sources.dq (C.realization.theta v)
        (diagonal R z * KPRationalAdelicSplitting.pglW F R.A.zeta12 R.A.primitive_zeta12) =
      fourier R C.sources.dq (C.realization.theta v) 1 *
        (∏ p : R.A.Sf, ThetaExpansion.normalizedLocalWeylValue R C v (Sum.inr p.val) (z.2 p)) *
        ∏ w : InfinitePlace F,
          ThetaExpansion.normalizedLocalWeylValue R C v (Sum.inl w) (z.1 w)) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ v κ (j : ℕ), j ≤ 2 → ∀ u : ℝ, ∀ y : R.A.G1,
      let z := y.val * R.A.radialSection (Real.exp u) (Real.exp_pos u)
      ‖iteratedDeriv j (fun t => ThetaExpansion.radialSheetIntegrand R C v κ t y) u‖ ≤
        D * ((∏ p : R.A.Sf,
          ‖ThetaExpansion.normalizedLocalWeylValue R C v (Sum.inr p.val) (z.2 p)‖) *
          ∑ a : InfinitePlace F → Fin 3, ∏ w : InfinitePlace F,
            ‖ThetaExpansion.localWeylArchJet R C v w (a w).val (z.1 w)‖) := by
  let r := Fintype.card (InfinitePlace F)
  let b : ℝ := KThird (4 * Real.pi) ^ r
  let k : ℝ := 4 ^ r
  refine ⟨b * k, mul_nonneg (forward_scalar_pos (F := F)).le (by positivity), ?_⟩
  intro v κ j hj u y
  dsimp only
  have he : (fun t : ℝ => fourier R C.sources.dq (C.realization.theta v)
      (diagonal R (y.val * R.A.radialSection (Real.exp t) (Real.exp_pos t)) *
        KPRationalAdelicSplitting.pglW F R.A.zeta12 R.A.primitive_zeta12)) =
      fun t => fourier R C.sources.dq (C.realization.theta v) 1 *
        (∏ p : R.A.Sf,
          ThetaExpansion.normalizedLocalWeylValue R C v (Sum.inr p.val) (y.val.2 p)) *
        ∏ w : InfinitePlace F,
          ThetaExpansion.normalizedLocalWeylValue R C v (Sum.inl w)
            (y.val.1 w * (R.A.radialSection (Real.exp t) (Real.exp_pos t)).1 w) := by
    funext t
    rw [hfactor]
    simp only [finite_value_radial, Prod.fst_mul, Pi.mul_apply]
  have hp := arch_product_jet_le_unconditional R C v y.val u j hj
  calc
    _ ≤ ‖iteratedDeriv j (fun t => fourier R C.sources.dq (C.realization.theta v)
        (diagonal R (y.val * R.A.radialSection (Real.exp t) (Real.exp_pos t)) *
          KPRationalAdelicSplitting.pglW F R.A.zeta12 R.A.primitive_zeta12)) u‖ :=
      radialIntegrand_jet_le R C v κ y j u
    _ = b * (∏ p : R.A.Sf,
        ‖ThetaExpansion.normalizedLocalWeylValue R C v (Sum.inr p.val) (y.val.2 p)‖) *
        ‖iteratedDeriv j (fun t => ∏ w : InfinitePlace F,
          ThetaExpansion.normalizedLocalWeylValue R C v (Sum.inl w)
            (y.val.1 w * (R.A.radialSection (Real.exp t) (Real.exp_pos t)).1 w)) u‖ := by
      rw [he, iteratedDeriv_const_mul_field, norm_mul, norm_mul, norm_prod, forward_period_norm]
    _ ≤ b * (∏ p : R.A.Sf,
        ‖ThetaExpansion.normalizedLocalWeylValue R C v (Sum.inr p.val) (y.val.2 p)‖) *
        (k * ∑ a : InfinitePlace F → Fin 3, ∏ w : InfinitePlace F,
          ‖ThetaExpansion.localWeylArchJet R C v w (a w).val
            ((y.val * R.A.radialSection (Real.exp u) (Real.exp_pos u)).1 w)‖) := by
      apply mul_le_mul_of_nonneg_left hp
      exact mul_nonneg (forward_scalar_pos (F := F)).le (Finset.prod_nonneg (fun _ _ => norm_nonneg _))
    _ = _ := by
      simp only [finite_value_radial]
      ring

end DedekindZetaZeroFree.SheetRescaling.WeylTensorTransport

end
