module

public import DedekindZetaZeroFree.Theta.Whittaker.NonnegativeRadialValues

@[expose] public section

noncomputable section
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency true
open scoped NumberField Classical ValuativeRel
open NumberField IsDedekindDomain ValuativeRel
namespace DedekindZetaZeroFree.ExteriorWhittakerValues.ActualStoredShells
open MomentSources ThetaExpansion ActualSpherical ActualJacquet ActualShellNormalization ActualShellValues
open KPLocalExceptionalConstruction KPLocalPrincipalSeries KPExteriorUnitShellIntegrals
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}

theorem reference_fixed (R : PrincipalMellin.ActualRecipe S η)
    {N : TraceHaarTransport R} (C : JointHaarFactorizedSources R N) (p : ThetaBranch.ExteriorPrime R.A)
    (ht : ringChar (KPTameCompact.O F p.val ⧸ KPTameCompact.p F p.val) ≠ 3)
    (hn : ¬ KPAdelicCoverRestrictedProduct.Bad F p.val) :
    C.factorization.references (Sum.inr p.val) ∈
      ImageFixed F R.A.zeta12 R.A.primitive_zeta12 p.val
        (C.factorization.finiteData p.val).inducing
        (C.factorization.finiteData p.val).inducing.polarization
        (C.factorization.finiteData p.val).haar (C.factorization.finiteData p.val).haar_integer ht := by
  intro k
  obtain ⟨a, ha⟩ := k.property
  have hh := (C.factorization.spherical_reference p.val p.property).2
    (KPGoodCompactSplitting.kStar F R.A.zeta12 R.A.primitive_zeta12 p.val ht a) (by
      change _ ∈ KPAdelicCoverRestrictedProduct.finiteCompact F R.A.zeta12 R.A.primitive_zeta12 p.val
      rw [KPAdelicCoverRestrictedProduct.finiteCompact, dif_neg hn]
      exact ⟨a, rfl⟩)
  change exteriorImageAction R C p k.val _ = _
  have hk : KPPGLLocalCover.coverQuotient F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p.val)
      (KPGoodCompactSplitting.kStar F R.A.zeta12 R.A.primitive_zeta12 p.val ht a) = k.val := ha
  simpa only [hk] using hh

theorem stored_nonnegative_values (R : PrincipalMellin.ActualRecipe S η)
    {N : TraceHaarTransport R} (C : JointHaarFactorizedSources R N) (hW : ExteriorWhittakerEquivariance R C)
    (p : ThetaBranch.ExteriorPrime R.A)
    [Fintype (IsLocalRing.ResidueField (valuation (p.val.adicCompletion F)).integer)]
    (ht : ringChar (KPTameCompact.O F p.val ⧸ KPTameCompact.p F p.val) ≠ 3)
    (hn : ¬ KPAdelicCoverRestrictedProduct.Bad F p.val)
    (hgood : valuation (p.val.adicCompletion F) (6 : p.val.adicCompletion F) = 1)
    (π : (valuation (p.val.adicCompletion F)).integer) (hπ : Irreducible π)
    (ψ : AddChar (p.val.adicCompletion F) ℂ) (hψcont : Continuous ψ)
    (hψunitary : ∀ x, ‖ψ x‖ = 1) (hcond : ConductorZero ψ π)
    (hψ : ∀ x, ψ x = (ResidueTrace.localTraceCharacter p.val x : ℂ))
    (χκ : MulChar (IsLocalRing.ResidueField (valuation (p.val.adicCompletion F)).integer) ℂ)
    (hactual : ∀ u, unitCharacter χκ u = arithmeticUnitCharacter F R.A.zeta12 R.A.primitive_zeta12 p.val hgood u)
    (ψbar : AddChar (IsLocalRing.ResidueField (valuation (p.val.adicCompletion F)).integer) ℂ)
    (hbar : ∀ u : (valuation (p.val.adicCompletion F)).integer,
      ψbar (IsLocalRing.residue _ u) = ψ ((π : p.val.adicCompletion F)⁻¹ * (u : p.val.adicCompletion F)))
    (e : ℕ) :
    exteriorWhittakerValue R C p (uniformizerUnit F p.val π hπ ^ (e : ℤ)) =
      radialValue F p.val (g χκ ψbar 2) (e : ℤ) := by
  let M := C.factorization.finiteData p.val
  have hL : IsWhittaker F R.A.zeta12 R.A.primitive_zeta12 p.val M.inducing
      M.inducing.polarization M.haar M.haar_integer ψ (C.factorization.ell (Sum.inr p.val)) := by
    intro t f
    have hu : (M.inducing.borel.upperRoot (Multiplicative.ofAdd t) :
        ActualCover F R.A.zeta12 R.A.primitive_zeta12 p.val) =
        KPPGLLocalCover.N F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p.val) t :=
      (M.inducing.openCell M.inducing.polarization).upper_eq t
    exact (congrArg (fun g : ActualCover F R.A.zeta12 R.A.primitive_zeta12 p.val =>
      C.factorization.ell (Sum.inr p.val) (exteriorImageAction R C p g f)) hu).trans
        ((hW p t f).trans (congrArg (fun z : ℂ => z * C.factorization.ell (Sum.inr p.val) f)
          (hψ t).symm))
  unfold exteriorWhittakerValue
  rw [exterior_diagonal_eq_standard_lift]
  exact (nonnegative_values F R.A.zeta12 R.A.primitive_zeta12 p.val M.inducing M.inducing.polarization
      M.haar M.haar_integer ht hgood π hπ ψ hψcont hψunitary hcond χκ hactual ψbar hbar
      (C.factorization.references (Sum.inr p.val)) (reference_fixed R C p ht hn)
      (C.factorization.spherical_reference p.val p.property).1
      (C.factorization.ell (Sum.inr p.val)) hL (exterior_reference_value_eq_one R C p) e)

end DedekindZetaZeroFree.ExteriorWhittakerValues.ActualStoredShells

end
