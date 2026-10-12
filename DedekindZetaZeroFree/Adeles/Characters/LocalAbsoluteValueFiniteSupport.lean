module

public import DedekindZetaZeroFree.Metaplectic.Torus.RationalCenterCharacterData

@[expose] public section

open scoped NumberField Classical BigOperators NNReal
open NumberField IsDedekindDomain
namespace DedekindZetaZeroFree.KPGlobalCenterRationalCharacterExtension.CubeDiagonalProduct
noncomputable section
set_option autoImplicit false
variable (F : Type) [Field F] [NumberField F]

theorem idele_localAbs_hasFiniteMulSupport (y : Ideles F) :
    Function.HasFiniteMulSupport (fun v : KPHilbert.Place F =>
      Units.mk0 (localAbs F v (KPGlobalCubicIdelePairing.ideleEval F v y))
        (ne_of_gt (localAbs_pos F v (KPGlobalCubicIdelePairing.ideleEval F v y)))) := by
  rw [Function.HasFiniteMulSupport, Function.mulSupport]

  let z : (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F)ˣ := (MulEquiv.prodUnits y).2
  have hz : {q : HeightOneSpectrum (𝓞 F) |
      ‖(z : IsDedekindDomain.FiniteAdeleRing (𝓞 F) F) q‖ ≠ 1}.Finite := by
    have h := FiniteAdeleRing.hasFiniteMulSupport_norm z
    rwa [Function.HasFiniteMulSupport, Function.mulSupport] at h
  refine ((Set.finite_univ : (Set.univ : Set (InfinitePlace F)).Finite).image
    (Sum.inl : InfinitePlace F → KPHilbert.Place F)).union (hz.image Sum.inr) |>.subset ?_
  intro v hv
  rcases v with w | q
  · exact Or.inl ⟨w, trivial, rfl⟩
  · refine Or.inr ⟨q, ?_, rfl⟩
    intro h1
    have hnorm : ‖((KPGlobalCubicIdelePairing.ideleEval F (Sum.inr q) y :
        (KPHilbert.Completion F (Sum.inr q))ˣ) :
          KPHilbert.Completion F (Sum.inr q))‖ =
        ‖(z : IsDedekindDomain.FiniteAdeleRing (𝓞 F) F) q‖ :=
      rfl
    have hreal : ‖((KPGlobalCubicIdelePairing.ideleEval F (Sum.inr q) y :
        (KPHilbert.Completion F (Sum.inr q))ˣ) :
          KPHilbert.Completion F (Sum.inr q))‖ = 1 := by
      rw [hnorm]; exact h1
    have hnn : ‖((KPGlobalCubicIdelePairing.ideleEval F (Sum.inr q) y :
        (KPHilbert.Completion F (Sum.inr q))ˣ) :
          KPHilbert.Completion F (Sum.inr q))‖₊ = 1 := by
      apply NNReal.coe_injective
      rw [coe_nnnorm, hreal]
      simp
    have hf1 : Units.mk0 (localAbs F (Sum.inr q)
        (KPGlobalCubicIdelePairing.ideleEval F (Sum.inr q) y))
        (ne_of_gt (localAbs_pos F (Sum.inr q)
          (KPGlobalCubicIdelePairing.ideleEval F (Sum.inr q) y))) = 1 := by
      refine Units.ext ?_
      rw [Units.val_mk0, Units.val_one]
      exact hnn
    exact hv hf1

end
end DedekindZetaZeroFree.KPGlobalCenterRationalCharacterExtension.CubeDiagonalProduct
