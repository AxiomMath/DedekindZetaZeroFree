module

public import DedekindZetaZeroFree.Theta.Unfolding.TraceNormalizedSourceData

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace DedekindZetaZeroFree.ThetaExpansion
open MomentSources NumberField MeasureTheory
open scoped NumberField Classical
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}

def firstRootBranch (R : PrincipalMellin.ActualRecipe S η)
    (v : R.A.UnitQuotient) : R.A.G →* ℂ := by
  let c : R.A.G →* Circle := {
    toFun := R.A.correctionLS R.probe.correction.Λ R.probe.correction.G R.probe.correction.η_id
    map_one' := by simp [SArithmeticData.correctionLS, SArithmeticData.ideleSInverseProduct]
    map_mul' := by
      intro y z
      simp only [SArithmeticData.correctionLS, SArithmeticData.ideleSInverseProduct,
        Prod.fst_mul, Prod.snd_mul, Pi.mul_apply, map_mul, mul_inv, Finset.prod_mul_distrib]
      ac_rfl }
  exact (Circle.coeHom.comp c) *
    (R.σ.toMonoidHom.comp ((Units.coeHom F).comp ((rootsOfUnity 6 F).subtype.comp
      ((R.A.H_S6 (QuotientGroup.mk' R.A.sixthPowers
        (R.A.diagonal (R.probe.unitReps.representative v).val))).comp
          (QuotientGroup.mk' R.A.sixthPowers)))))

theorem firstRootBranch_apply (R : PrincipalMellin.ActualRecipe S η)
    (v : R.A.UnitQuotient) (y : R.A.G) : firstRootBranch R v y =
    (R.A.correctionLS R.probe.correction.Λ R.probe.correction.G R.probe.correction.η_id y : ℂ) *
      R.σ ((R.A.H_S (R.A.diagonal (R.probe.unitReps.representative v).val) y : Fˣ) : F) := rfl

structure FirstRootCutoffs (R : PrincipalMellin.ActualRecipe S η) where
  exponent : InfinitePlace F → ℤ
  sign : ∀ w, exponent w = 1 ∨ exponent w = -1
  cutoff : ∀ p : R.A.Sf, Subgroup (p.val.adicCompletion F)ˣ
  open_cutoff : ∀ p, IsOpen (cutoff p : Set (p.val.adicCompletion F)ˣ)
  compact_cutoff : ∀ p, IsCompact (cutoff p : Set (p.val.adicCompletion F)ˣ)
  sixth : ∀ p z, z ∈ cutoff p → ∃ t : (p.val.adicCompletion F)ˣ, t ^ 6 = z
  congruence : ∀ p : R.A.Sf, AddSubgroup (p.val.adicCompletion F)
  open_congruence : ∀ p, IsOpen (congruence p : Set (p.val.adicCompletion F))
  compact_congruence : ∀ p, IsCompact (congruence p : Set (p.val.adicCompletion F))
  congruence_exact : ∀ p z, z ∈ cutoff p ↔ (z : p.val.adicCompletion F) - 1 ∈ congruence p
  branch_exact : ∀ v y, (∀ p : R.A.Sf, y.2 p ∈ cutoff p) → firstRootBranch R v y =
    ∏ w : InfinitePlace F,
      DHCubic.angular (InfinitePlace.Completion.extensionEmbedding w (y.1 w : w.Completion)) ^ exponent w

theorem first_root_cutoffs_exist (R : PrincipalMellin.ActualRecipe S η) :
    Nonempty (FirstRootCutoffs R) := by
  let D := R.probe.correction
  choose e he hvalue using D.infinity_angular
  have hn (p : R.A.Sf) := D.finite_locallyConstant p 1
  choose V hVo hV1 hVconst using hn
  have hs (p : R.A.Sf) := ThetaFiniteCutoff.PhaseSublevels.small_sixth_power_congruence
    F p.val (V p) (hVo p) (hV1 p)
  choose H U hHc hHo hUc hUo hUV hU6 hUint hmem using hs
  refine ⟨{
    exponent := e
    sign := he
    cutoff := U
    open_cutoff := hUo
    compact_cutoff := hUc
    sixth := fun p z hz => hU6 p hz
    congruence := H
    open_congruence := hHo
    compact_congruence := hHc
    congruence_exact := hmem
    branch_exact := ?_ }⟩
  intro v y hy
  have hfin (p : R.A.Sf) : R.A.ideleFiniteComponent
      (R.A.correctionTheta D.Λ D.G D.η_id) p.val (y.2 p) = 1 := by
    rw [hVconst p (y.2 p) (hUV p (hy p)), map_one]
  have hHil : R.A.H_S (R.A.diagonal (R.probe.unitReps.representative v).val) y = 1 := by
    unfold SArithmeticData.H_S
    apply Finset.prod_eq_one
    intro p _
    have hp : QuotientGroup.mk' (powMonoidHom (α := (p.val.adicCompletion F)ˣ) 6).range
        (y.2 p) = 1 := (QuotientGroup.eq_one_iff _).mpr (hU6 p (hy p))
    change R.A.actualLocalHilbert p.val 6 _ _
      (QuotientGroup.mk' (powMonoidHom (α := (p.val.adicCompletion F)ˣ) 6).range (y.2 p)) = 1
    rw [hp, map_one]
  rw [firstRootBranch_apply, hHil]
  simp only [OneMemClass.coe_one, Units.val_one, map_one, mul_one]
  change (R.A.ideleSInverseProduct (R.A.correctionTheta D.Λ D.G D.η_id) y : ℂ) = _
  unfold SArithmeticData.ideleSInverseProduct
  simp only [hfin, inv_one, Finset.prod_const_one, mul_one]
  change Circle.coeHom (∏ w : InfinitePlace F,
    (R.A.ideleInfiniteComponent (R.A.correctionTheta D.Λ D.G D.η_id) w (y.1 w))⁻¹) = _
  rw [map_prod]
  apply Finset.prod_congr rfl
  intro w _
  exact (hvalue w (y.1 w)).1

theorem FirstRootCutoffs.kernel {R : PrincipalMellin.ActualRecipe S η}
    (B : FirstRootCutoffs R) (v : R.A.UnitQuotient) (y : R.A.G)
    (hinf : ∀ w, y.1 w = 1) (hfin : ∀ p, y.2 p ∈ B.cutoff p) :
    firstRootBranch R v y = 1 := by
  rw [B.branch_exact v y hfin]
  apply Finset.prod_eq_one
  intro w _
  rw [hinf w]
  simp [DHCubic.angular]

def firstRootSphericalProduct (R : PrincipalMellin.ActualRecipe S η) (y : R.A.G) : ℂ :=
  ∏ w : InfinitePlace F, (‖(y.1 w : w.Completion)‖ : ℂ) *
    (KThird (4 * Real.pi * Real.sqrt (‖(y.1 w : w.Completion)‖ ^ 2)) : ℂ)

def firstRootMultiplier (R : PrincipalMellin.ActualRecipe S η)
    (B : FirstRootCutoffs R) (y : R.A.G) : ℂ :=
  ∏ w : InfinitePlace F, (‖(y.1 w : w.Completion)‖ : ℂ) *
    DHCubic.angular (InfinitePlace.Completion.extensionEmbedding w (y.1 w : w.Completion)) ^ B.exponent w

def firstRootRadialProfile (R : PrincipalMellin.ActualRecipe S η)
    (B : FirstRootCutoffs R) (y : R.A.G) : ℂ :=
  (if ∀ p : R.A.Sf, y.2 p ∈ B.cutoff p then 1 else 0) * firstRootSphericalProduct R y

end DedekindZetaZeroFree.ThetaExpansion

end
