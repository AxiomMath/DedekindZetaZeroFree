module

public import DedekindZetaZeroFree.Theta.Unfolding.TameTransposeKernel

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.KPTameTransposeLiteral

open scoped NumberField Classical
open NumberField IsDedekindDomain MeasureTheory ValuativeRel
open KPLocalExceptionalConstruction KPLocalStoneVonNeumann KPLocalPrincipalSeries
open KPRankOneRootParameter KPTameJacquetTestDuality
open KPTameTransposeKernelUnfolding KPTameValuationCoordinates

variable (F : Type) [Field F] [NumberField F]
  (ζ : F) (hζ : IsPrimitiveRoot ζ 12) (q : HeightOneSpectrum (𝓞 F))

abbrev RawResidue := IsLocalRing.ResidueField (KPTameCompact.O F q)

def RawPiFirstOrientation (π : (LocalField F q)ˣ)
    (κ : MulChar (RawResidue F q) ℂ) : Prop :=
  ∀ u : (KPTameCompact.O F q)ˣ,
    κ (IsLocalRing.residue (KPTameCompact.O F q) (u : KPTameCompact.O F q)) =
      (ordinaryIota F ζ hζ
        (KPHilbert.B3 F ζ hζ (Sum.inr q) π
          (KPTameCompact.unitInclusion F q u)) : ℂ)

variable (S : CanonicalFiniteInducingData F ζ hζ q) (P : Polarization S.heisenberg)
  (hP : IsTamePolarization F ζ hζ q S P)
  (μ : Measure (LocalField F q)) [μ.IsAddHaarMeasure]
  (hμ : μ ((valuation (LocalField F q)).integer : Set (LocalField F q)) = 1)
  (ξ : (valuation (LocalField F q)).integer) (hξ : IsPrimitiveRoot ξ 3)

 def aLift (y : (LocalField F q)ˣ) : actualTorus F ζ hζ q :=
 ⟨KPPGLLocalCover.A F ζ hζ (Sum.inr q) y, by
   refine ⟨KubotaRankTwo.d (LocalField F q) y 1, ?_, ?_, ?_⟩
   · rfl
   · simp [KubotaRankTwo.d]
   · simp [KubotaRankTwo.d]⟩
private theorem abs_unit (u : (KPTameCompact.O F q)ˣ) :
 localAbs (LocalField F q) (KPTameCompact.unitInclusion F q u) = 1 := by
 have hv : valuation (LocalField F q) (KPTameCompact.unitInclusion F q u : LocalField F q) = 1 :=
   (Valuation.integer.integers (valuation (LocalField F q))).valuation_unit u
 simp [localAbs, hv]
private theorem class_units : unitCubeClasses (LocalField F q) =
 ((QuotientGroup.mk' (CubicCharacters.cubes (LocalField F q)ˣ)).comp
 (KPTameCompact.unitInclusion F q)).range := by
 rw [unitCubeClasses, Subgroup.map_sup]
 have hz : (CubicCharacters.cubes (LocalField F q)ˣ).map
   (QuotientGroup.mk' (CubicCharacters.cubes (LocalField F q)ˣ)) = ⊥ := by
   rw [Subgroup.map_eq_bot_iff]
   simp
 rw [hz, sup_bot_eq]
 exact (MonoidHom.range_comp _ _).symm

 def unitLift (ht : ringChar (KPTameCompact.O F q ⧸ KPTameCompact.p F q) ≠ 3) : (KPTameCompact.O F q)ˣ →* actualTorus F ζ hζ q where
 toFun u := aLift F ζ hζ q (KPTameCompact.unitInclusion F q u)
 map_one' := by
   apply Subtype.ext
   change KPPGLLocalCover.A F ζ hζ (Sum.inr q) _ = 1
   rw [map_one]
   have h1 : KPPGLLocalCover.A F ζ hζ (Sum.inr q) 1 =
     ((S.borel.cubeLift 1 : actualTorus F ζ hζ q) : ActualCover F ζ hζ q) := by
     rw [S.cube_actual]; simp
   rw [h1, map_one]; rfl
 map_mul' u v := by
   apply Subtype.ext
   change KPPGLLocalCover.A F ζ hζ (Sum.inr q) _ =
     KPPGLLocalCover.A F ζ hζ (Sum.inr q) _ * KPPGLLocalCover.A F ζ hζ (Sum.inr q) _
   rw [map_mul, KPPGLLocalCover.A_mul,
     KPTameCompact.B3_units F q ζ hζ ht u v]
   simp

private theorem unit_center_value
 (ht : ringChar (KPTameCompact.O F q ⧸ KPTameCompact.p F q) ≠ 3) (u : (KPTameCompact.O F q)ˣ)
 (hu : (unitLift F ζ hζ q S ht u) ∈ S.heisenberg.C) :
 S.heisenberg.ω ⟨unitLift F ζ hζ q S ht u, hu⟩ = 1 := by
 have hc : QuotientGroup.mk' (CubicCharacters.cubes (LocalField F q)ˣ)
   (KPTameCompact.unitInclusion F q u) = 1 := by
   have hk : S.heisenberg.π (unitLift F ζ hζ q S ht u) = 1 := by
     change unitLift F ζ hζ q S ht u ∈ S.heisenberg.π.ker
     rwa [S.heisenberg.quotient_kernel]
   have h := S.cube_class (unitLift F ζ hζ q S ht u)
   rw [hk, map_one, S.coordinate_lift _ _ rfl] at h
   exact h.symm
 have hm := (QuotientGroup.eq_one_iff _).mp hc
 obtain ⟨y, hy⟩ := hm
 have hy' : y ^ 3 = KPTameCompact.unitInclusion F q u := hy
 have he : (⟨unitLift F ζ hζ q S ht u, hu⟩ : S.heisenberg.C) = S.borel.cubeLift y := by
   apply Subtype.ext
   apply Subtype.ext
   rw [S.cube_actual, hy']
   rfl
 apply Units.ext
 rw [he, S.borel.exceptional_cube, hy']
 simp [normPower, abs_unit F q u]

theorem normalized_extension_exists
    (htame : ringChar (KPTameCompact.O F q ⧸ KPTameCompact.p F q) ≠ 3) :
    ∃ P' : Polarization S.heisenberg,
      IsTamePolarization F ζ hζ q S P' ∧
        RawNormalizedExtension F ζ hζ q S P' := by
 classical
 obtain ⟨Q, hQ⟩ := KPLocalTameValuationWhittakerBasis.exists_canonical_tame_polarization F ζ hζ q S htame
 have hmap : Q.L.map S.cubeClassEquiv.toMonoidHom = unitCubeClasses (LocalField F q) := by
   rw [hQ, Subgroup.map_comap_eq_self_of_surjective S.cubeClassEquiv.surjective]
 let U := unitLift F ζ hζ q S htame
 have hUm (u : (KPTameCompact.O F q)ˣ) : U u ∈ Q.L.comap S.heisenberg.π := by
   change S.heisenberg.π (U u) ∈ Q.L
   rw [hQ]
   change S.cubeClassEquiv (S.heisenberg.π (U u)) ∈ unitCubeClasses (LocalField F q)
   rw [S.cube_class, S.coordinate_lift _ _ rfl, class_units F q]
   exact ⟨u, rfl⟩
 let UA : (KPTameCompact.O F q)ˣ →* Q.L.comap S.heisenberg.π := U.codRestrict _ hUm
 let pA : Q.L.comap S.heisenberg.π →* Q.L :=
   (S.heisenberg.π.comp (Q.L.comap S.heisenberg.π).subtype).codRestrict _ (fun a => a.property)
 let pU := pA.comp UA
 have hsurj : Function.Surjective pU := by
   intro d
   have hm : S.cubeClassEquiv d ∈ unitCubeClasses (LocalField F q) := by
     rw [← hmap]; exact ⟨d, d.property, rfl⟩
   rw [class_units F q] at hm
   obtain ⟨u, hu⟩ := hm
   refine ⟨u, ?_⟩
   apply Subtype.ext
   apply S.cubeClassEquiv.injective
   change S.cubeClassEquiv (S.heisenberg.π (U u)) = S.cubeClassEquiv d
   rw [S.cube_class, S.coordinate_lift _ _ rfl]
   exact hu
 let f := Q.ωL.toMonoidHom.comp UA
 have hk : pU.ker ≤ f.ker := by
   intro u hu
   have hc : U u ∈ S.heisenberg.C := by
     rw [← S.heisenberg.quotient_kernel]
     change S.heisenberg.π (U u) = 1
     exact congrArg Subtype.val hu
   change Q.ωL (UA u) = 1
   rw [Q.extends_center _ hc]
   exact unit_center_value F ζ hζ q S htame u hc
 let c := pU.liftOfSurjective hsurj ⟨f, hk⟩
 have hcu (u) : c (pU u) = f u := by
   exact MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ _
 let corr : Q.L.comap S.heisenberg.π →* ℂˣ := c.comp pA
 have hcorr (a : Q.L.comap S.heisenberg.π) (ha : (a : actualTorus F ζ hζ q) ∈ S.heisenberg.C) : corr a = 1 := by
   have hp : pA a = 1 := by
     apply Subtype.ext
     change S.heisenberg.π a = 1
     change (a : actualTorus F ζ hζ q) ∈ S.heisenberg.π.ker
     rwa [S.heisenberg.quotient_kernel]
   change c (pA a) = 1
   rw [hp, map_one]
 have hcont : Continuous corr := by
   apply continuous_of_continuousAt_one corr
   have hopen : IsOpen {a : Q.L.comap S.heisenberg.π | (a : actualTorus F ζ hζ q) ∈ S.heisenberg.C} :=
     S.heisenberg.center_open.preimage continuous_subtype_val
   have hevent : ∀ᶠ a in nhds (1 : Q.L.comap S.heisenberg.π), corr a = 1 := by
     filter_upwards [hopen.mem_nhds S.heisenberg.C.one_mem] with a ha
     exact hcorr a ha
   simpa using (continuousAt_const (y := (1 : ℂˣ))).congr_of_eventuallyEq hevent
 let corrC : Q.L.comap S.heisenberg.π →ₜ* ℂˣ := ⟨corr, hcont⟩
 let ωnew := Q.ωL * corrC⁻¹
 have hext (a : Q.L.comap S.heisenberg.π) (ha : (a : actualTorus F ζ hζ q) ∈ S.heisenberg.C) :
   ωnew a = S.heisenberg.ω ⟨a, ha⟩ := by
   change Q.ωL a * (corr a)⁻¹ = _
   rw [hcorr a ha, inv_one, mul_one, Q.extends_center a ha]
 let P' : Polarization S.heisenberg := ⟨Q.L, Q.maximal, ωnew, hext⟩
 have hun (u) : ωnew (UA u) = 1 := by
   change Q.ωL (UA u) * (c (pU u))⁻¹ = 1
   rw [hcu]
   exact mul_inv_cancel _
 refine ⟨P', hmap, ?_⟩
 intro h e u y hh
 let ce := S.central e * S.borel.cubeLift y
 have hce : (ce : actualTorus F ζ hζ q) ∈ Q.L.comap S.heisenberg.π := by
   change S.heisenberg.π ce ∈ Q.L
   have hk : S.heisenberg.π ce = 1 := by
     change (ce : actualTorus F ζ hζ q) ∈ S.heisenberg.π.ker
     rw [S.heisenberg.quotient_kernel]; exact ce.property
   rw [hk]; exact Q.L.one_mem
 let ca : Q.L.comap S.heisenberg.π := ⟨ce, hce⟩
 have heq : h = ca * UA u := by
   apply Subtype.ext
   apply Subtype.ext
   change (h.val : ActualCover F ζ hζ q) =
     ((ce : actualTorus F ζ hζ q) : ActualCover F ζ hζ q) *
     (U u : ActualCover F ζ hζ q)
   rw [hh]
   change _ = (((S.central e : actualTorus F ζ hζ q) : ActualCover F ζ hζ q) *
     ((S.borel.cubeLift y : actualTorus F ζ hζ q) : ActualCover F ζ hζ q)) * _
   rw [S.central_actual, S.cube_actual]
   have hc : Commute (S.borel.cubeLift y : actualTorus F ζ hζ q) (U u) :=
     (Subgroup.mem_center_iff.mp (S.heisenberg.central (S.borel.cubeLift y).property) (U u)).symm
   have hc' := congrArg (fun t : actualTorus F ζ hζ q => (t : ActualCover F ζ hζ q)) hc.eq
   simp only [Subgroup.coe_mul, S.cube_actual] at hc'
   change KPPGLLocalCover.A F ζ hζ (Sum.inr q) (y ^ 3) *
     KPPGLLocalCover.A F ζ hζ (Sum.inr q) ((KPTameCompact.unitInclusion F q) u) =
     KPPGLLocalCover.A F ζ hζ (Sum.inr q) ((KPTameCompact.unitInclusion F q) u) *
     KPPGLLocalCover.A F ζ hζ (Sum.inr q) (y ^ 3) at hc'
   rw [mul_assoc, mul_assoc, ← hc']
   rfl
 change (ωnew h : ℂ) = _
 rw [heq, map_mul, hun, mul_one, hext ca ce.property]
 change (S.heisenberg.ω (S.central e * S.borel.cubeLift y) : ℂ) = _
 rw [map_mul, Units.val_mul, S.central_character, S.borel.exceptional_cube]

end DedekindZetaZeroFree.KPTameTransposeLiteral

end
