module

public import DedekindZetaZeroFree.Theta.Whittaker.FirstRootSphericalSeedData

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.ThetaExpansion
open MomentSources NumberField MeasureTheory
open scoped NumberField Classical
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}

theorem FirstRootCutoffs.shrink {R : PrincipalMellin.ActualRecipe S η}
    (B : FirstRootCutoffs R) (V : ∀ p : R.A.Sf, Set (p.val.adicCompletion F)ˣ)
    (hV : ∀ p, IsOpen (V p)) (h1 : ∀ p, (1 : (p.val.adicCompletion F)ˣ) ∈ V p) :
    ∃ B' : FirstRootCutoffs R, B'.exponent = B.exponent ∧
      (∀ p, B'.cutoff p ≤ B.cutoff p) ∧ (∀ p, (B'.cutoff p : Set _) ⊆ V p) := by
  have h p := ThetaFiniteCutoff.PhaseSublevels.small_sixth_power_congruence F p.val
    ((B.cutoff p : Set _) ∩ V p) ((B.open_cutoff p).inter (hV p))
    ⟨(B.cutoff p).one_mem, h1 p⟩
  choose H U hHc hHo hUc hUo hsub hsix hint hmem using h
  let B' : FirstRootCutoffs R := {
    exponent := B.exponent
    sign := B.sign
    cutoff := U
    open_cutoff := hUo
    compact_cutoff := hUc
    sixth := fun p z hz => hsix p hz
    congruence := H
    open_congruence := hHo
    compact_congruence := hHc
    congruence_exact := hmem
    branch_exact := fun v y hy => B.branch_exact v y (fun p => (hsub p (hy p)).1) }
  exact ⟨B', rfl, fun p z hz => (hsub p hz).1, fun p z hz => (hsub p hz).2⟩

structure FirstRootProjected (R : PrincipalMellin.ActualRecipe S η)
    (N : TraceHaarTransport R) (A : FirstRootSphericalSeed R N) (B : FirstRootCutoffs R) where
  cutoffs : FirstRootCutoffs R
  exponent_exact : cutoffs.exponent = B.exponent
  cutoff_le : ∀ p, cutoffs.cutoff p ≤ B.cutoff p
  cutoff_neighborhood : ∀ p, (cutoffs.cutoff p : Set _) ⊆ A.neighborhood p
  base : JointExteriorCoefficientSources R N
  radial : ∀ v y, fourier R base.sources.dq (base.realization.theta v) (diagonal R y) =
    firstRootRadialProfile R cutoffs y

end DedekindZetaZeroFree.ThetaExpansion

end
