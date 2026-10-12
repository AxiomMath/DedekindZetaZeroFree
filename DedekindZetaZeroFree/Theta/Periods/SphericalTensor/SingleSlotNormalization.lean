module

public import DedekindZetaZeroFree.Theta.Periods.SphericalTensor.SmoothGlobalization

@[expose] public section

noncomputable section
open scoped Classical NumberField
namespace DedekindZetaZeroFree.ThetaExpansion
open MomentSources NumberField MeasureTheory RootDerivatives
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}

structure NormalizedSphericalTensor (R : PrincipalMellin.ActualRecipe S η)
    {N : TraceHaarTransport R} (A : JointExteriorCoefficientSources R N) (D : SphericalTransportData R A) where
  scalar : ℂ
  scalar_nonzero : scalar ≠ 0
  slot_mem : Sum.inr A.factorization.scalarSlot.val ∈ D.tensor.stage.val
  entries : ∀ p : D.tensor.stage.val, actualLocal R A.factorization.finiteData p
  entries_exact : entries = Function.update D.tensor.entries
    ⟨Sum.inr A.factorization.scalarSlot.val, slot_mem⟩
    (scalar • D.tensor.entries ⟨Sum.inr A.factorization.scalarSlot.val, slot_mem⟩)
  realization_exact : tensorFunction R A.factorization D.tensor.stage entries = scalar • D.tensor.value
  realization_nonzero : tensorFunction R A.factorization D.tensor.stage entries ≠ 0
  period_nonzero : fourier R A.sources.dq (tensorFunction R A.factorization D.tensor.stage entries) 1 ≠ 0
  spherical_near : ∀ y : R.A.G, (∀ p, y.2 p ∈ D.tensor.neighborhood p) →
    fourier R A.sources.dq (tensorFunction R A.factorization D.tensor.stage entries) (diagonal R y) =
      firstRootSphericalProduct R y

theorem normalizedSphericalTensor_nonempty
    (R : PrincipalMellin.ActualRecipe S η) {N : TraceHaarTransport R}
    (A : JointExteriorCoefficientSources R N) (D : SphericalTransportData R A) :
    Nonempty (NormalizedSphericalTensor R A D) := by
  have hn (w : InfinitePlace F) : D.localForm w ≠ 0 := by
    intro hz
    exact D.seed_nonzero w (by rw [hz]; rfl)
  choose t ht he using fun w => sphericalSeed_completion_normalization R.A w
    (D.localForm w) (D.whittaker w) (hn w)
  let c : ℂ := ∏ w : InfinitePlace F, t w
  have hc : c ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun w _ => ht w)
  have hslot : Sum.inr A.factorization.scalarSlot.val ∈ D.tensor.stage.val := by
    rw [D.tensor.stage_exact]
    exact (A.factorization.bad_exact _).mpr
      (Or.inr ⟨_, rfl, A.factorization.scalarSlot.property⟩)
  let p : D.tensor.stage.val := ⟨Sum.inr A.factorization.scalarSlot.val, hslot⟩
  let x := Function.update D.tensor.entries p (c • D.tensor.entries p)
  have hx : tensorFunction R A.factorization D.tensor.stage x = c • D.tensor.value :=
    tensorFunction_update_smul R A.factorization D.tensor.stage D.tensor.entries p c
  have hper (g : Group R) : fourier R A.sources.dq (c • D.tensor.value) g =
      c * fourier R A.sources.dq D.tensor.value g := by
    unfold MomentSources.fourier
    simp only [Pi.smul_apply, smul_eq_mul, mul_assoc]
    exact integral_const_mul _ _
  refine ⟨⟨c, hc, hslot, x, rfl, hx, ?_, ?_, ?_⟩⟩
  · rw [hx]
    exact smul_ne_zero hc D.tensor.nonzero
  · rw [hx, hper]
    exact mul_ne_zero hc D.period_nonzero
  · intro y hy
    rw [hx, hper, (D.tensor.diagonal_near_period y hy).2.2, D.arch_product y]
    unfold c firstRootSphericalProduct
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl (fun w _ => he w (y.1 w))

end DedekindZetaZeroFree.ThetaExpansion

end
