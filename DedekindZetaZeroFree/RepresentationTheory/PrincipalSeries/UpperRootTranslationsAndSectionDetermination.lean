module

public import DedekindZetaZeroFree.Metaplectic.Intertwining.Cubic.CenterTranslatedPureSectionSpanning

@[expose] public section

open scoped NumberField Valued Topology
open NumberField IsDedekindDomain ValuativeRel
namespace DedekindZetaZeroFree.KPActualScalarBinding
open KPLocalStoneVonNeumann KPLocalPrincipalSeries KPRankOneOpenCellKernel
open KPRankOneCenterInducedDiagonalComparison KPRankOneReverseRegulatorShells KPActualScalarBinding
noncomputable section
set_option autoImplicit false
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (q : HeightOneSpectrum (𝓞 F)) (S : ActualKPBinding F ζ hζ q)
variable (P : Polarization S.heisenberg) [DecidableEq S.D]
private theorem upper_shift_coordinate (x s : LocalField F q) :
    openCoordinate F ζ hζ q x * nLift F ζ hζ q s = openCoordinate F ζ hζ q (x+s) := by
  simp only [openCoordinate, mul_assoc, nLift, ← KPPGLLocalCover.N_add]

theorem shifted_profile_lc (φ : LocalField F q → ℂ) (hφ : IsLocallyConstant φ)
    (s : LocalField F q) : IsLocallyConstant (fun x => φ (x+s)) :=
  hφ.comp_continuous (continuous_id.add continuous_const)

theorem shifted_profile_compact (φ : LocalField F q → ℂ) (hcφ : HasCompactSupport φ)
    (s : LocalField F q) : HasCompactSupport (fun x => φ (x+s)) :=
  hcφ.comp_homeomorph (Homeomorph.addRight s)

theorem actual_pure_upper_shift
    (rep : S.D → KPExceptionalRaw.actualTorus F ζ hζ q)
    (hrep : ∀ d, S.heisenberg.π (rep d) = d) (d : S.D)
    (φ : LocalField F q → ℂ) (hφ : IsLocallyConstant φ) (hcφ : HasCompactSupport φ)
    (r : ℂˣ) (s : LocalField F q) :
    centerPrincipalSeries F ζ hζ q S.heisenberg S.borel .plus (additiveParameter F q r)
      (nLift F ζ hζ q s)
      (actualSection F ζ hζ q S.heisenberg S.borel P (S.openCell P) rep hrep d φ hφ hcφ r) =
    actualSection F ζ hζ q S.heisenberg S.borel P (S.openCell P) rep hrep d
      (fun x => φ (x+s)) (shifted_profile_lc F q φ hφ s)
      (shifted_profile_compact F q φ hcφ s) r := by
  apply centerSection_open_cell_ext F ζ hζ q S.heisenberg S.borel .plus
    (additiveParameter F q r)
  · intro x
    apply (centerCoordinates S.heisenberg rep hrep).injective
    change centerCoordinates S.heisenberg rep hrep
      ((actualSection F ζ hζ q S.heisenberg S.borel P (S.openCell P) rep hrep d φ hφ hcφ r).val
        (openCoordinate F ζ hζ q x * nLift F ζ hζ q s)) = _
    rw [upper_shift_coordinate]
    rw [(actualSection_spec F ζ hζ q S.heisenberg S.borel P (S.openCell P)
      rep hrep d φ hφ hcφ r).1 (x+s)]
    exact ((actualSection_spec F ζ hζ q S.heisenberg S.borel P (S.openCell P)
      rep hrep d (fun x => φ (x+s)) _ _ r).1 x).symm
  · intro g hg
    change (actualSection F ζ hζ q S.heisenberg S.borel P (S.openCell P)
      rep hrep d φ hφ hcφ r).val (g * nLift F ζ hζ q s) = 0
    apply (actualSection_spec F ζ hζ q S.heisenberg S.borel P (S.openCell P)
      rep hrep d φ hφ hcφ r).2
    rintro ⟨b,x,he⟩
    have hn : nLift F ζ hζ q s * nLift F ζ hζ q (-s) = 1 := by
      rw [nLift, nLift, ← KPPGLLocalCover.N_add]; simp [KPPGLLocalCover.N]
    apply hg
    refine ⟨b,x-s,?_⟩
    have h := congrArg (fun a : Cover F ζ hζ q => a*nLift F ζ hζ q (-s)) he
    simpa [mul_assoc, hn, upper_shift_coordinate, sub_eq_add_neg] using h
  · exact (actualSection_spec F ζ hζ q S.heisenberg S.borel P (S.openCell P)
      rep hrep d (fun x => φ (x+s)) _ _ r).2
 abbrev K := LocalField F q
 abbrev G := Cover F ζ hζ q
open KPJacquetBruhatCharts KPLocalSmoothRepresentation
 def mu (s : K F q) : KPRankOneInduction.GL2 F q :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![0,1;-1,-s] (by simp [Matrix.det_fin_two])
private theorem proj_mu (s : K F q) :
    projection F ζ hζ q (openCoordinate F ζ hζ q s) = Matrix.ProjGenLinGroup.mk (mu F q s) := by
  have hp : projection F ζ hζ q (signedWeyl F ζ hζ q) =
      Matrix.ProjGenLinGroup.mk (KubotaRankTwo.w (K F q)) := by
    change Matrix.ProjGenLinGroup.mk (signedWeylRaw F ζ hζ q).g = _
    rw [signedWeyl_matrix]
  have hn : projection F ζ hζ q (nLift F ζ hζ q s) =
      Matrix.ProjGenLinGroup.mk (KubotaRankTwo.n (K F q) s) := rfl
  have hm : (KubotaRankTwo.w (K F q))⁻¹ * KubotaRankTwo.n (K F q) s = mu F q s := by
    apply inv_mul_eq_of_eq_mul
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [KubotaRankTwo.coe_w, KubotaRankTwo.coe_n, mu, Matrix.mul_apply]
  rw [openCoordinate, map_mul, map_inv, hp, hn, ← map_inv, ← map_mul, hm]
private theorem omega_signed_factor (x : G F ζ hζ q) (hx : x ∈ omega F ζ hζ q) :
    ∃ b : Borel F ζ hζ q, x = b.val * openCoordinate F ζ hζ q
      (omegaCoordinate F ζ hζ q ⟨x,hx⟩) := by
  let s := omegaCoordinate F ζ hζ q ⟨x,hx⟩
  have hb : x * (openCoordinate F ζ hζ q s)⁻¹ ∈ Borel F ζ hζ q := by
    obtain ⟨A,hA,hc⟩ := hx
    have hs : s = A 1 1 / A 1 0 := omegaCoordinate_eq F ζ hζ q ⟨x,⟨A,hA,hc⟩⟩ A hA
    refine ⟨A * (mu F q s)⁻¹, ?_, ?_⟩
    · simp only [map_mul, map_inv, proj_mu, hA]
    · have hi : (mu F q s)⁻¹ = Matrix.GeneralLinearGroup.mkOfDetNeZero
          !![-s,-1;1,0] (by simp [Matrix.det_fin_two]) := by
        apply inv_eq_of_mul_eq_one_right
        ext i j
        fin_cases i <;> fin_cases j <;> simp [mu, Matrix.mul_apply]
      rw [hi]
      simp [Matrix.mul_apply, Fin.sum_univ_two, hs]
      field_simp
      ring
  exact ⟨⟨_,hb⟩, by simp [s, mul_assoc]⟩

private theorem nonzero_near_zero (U : Set (K F q)) (hU : U ∈ nhds 0) :
    ∃ y : K F q, y ∈ U ∧ y ≠ 0 := by
  obtain ⟨γ,hγ,hsub⟩ := (IsValuativeTopology.hasBasis_nhds_zero' (K F q)).mem_iff.mp hU
  obtain ⟨δ,hδ,hδ1⟩ := Valuation.IsNontrivial.exists_lt_one (v := valuation (K F q))
  obtain ⟨y,hy⟩ := ValuativeRel.valuation_surjective (min γ 1 * valuation (K F q) δ)
  have hp : 0 < min γ 1 := lt_min (zero_lt_iff.mpr hγ) (by simp)
  have hdy : valuation (K F q) δ ≠ 0 := by simpa
  have hlt : valuation (K F q) y < γ := by
    rw [hy]
    exact (mul_lt_of_lt_one_right hp hδ1).trans_le (min_le_left _ _)
  exact ⟨y,hsub hlt,by
    intro hz
    rw [hz,map_zero] at hy
    exact (mul_ne_zero hp.ne' hdy) hy.symm⟩

omit [DecidableEq S.D] in

theorem actual_open_coordinate_injective (z : ℂ)
    (a b : centerSectionSpace F ζ hζ q S.heisenberg S.borel .plus z)
    (he : ∀ s : LocalField F q,
      a.val (openCoordinate F ζ hζ q s) = b.val (openCoordinate F ζ hζ q s)) : a = b := by
  have ho : ∀ x ∈ omega F ζ hζ q, a.val x = b.val x := by
    intro x hx
    obtain ⟨c,hc⟩ := omega_signed_factor F ζ hζ q x hx
    let c' : S.borel.B := ⟨c.val,by
      rw [S.borel_eq]; exact c.property⟩
    rw [hc]
    exact (a.property.1 c' _).trans
      ((congrArg (centerInducingAction F ζ hζ q S.heisenberg S.borel .plus z c') (he _)).trans
        (b.property.1 c' _).symm)
  apply Subtype.ext
  funext x
  by_cases hx : x ∈ omega F ζ hζ q
  · exact ho x hx
  · have hxB : x ∈ Borel F ζ hζ q := by
      change x ∈ (Borel F ζ hζ q : Set (G F ζ hζ q))
      rw [← omega_complement F ζ hζ q]; exact hx
    obtain ⟨U,hU⟩ := a.property.2
    obtain ⟨V,hV⟩ := b.property.2
    have hL := (KPPGLLocalCover.finite_lifts_continuous F ζ hζ q _
      (KPAdelicCoverRestrictedProduct.depth_admissible F ζ hζ q)).2.1
    have hn : {y : K F q | KPPGLLocalCover.LowerN F ζ hζ (Sum.inr q) y ∈ U ⊓ V} ∈ nhds 0 := by
      apply hL.continuousAt.preimage_mem_nhds
      simpa [KPPGLLocalCover.LowerN] using (U ⊓ V).isOpen.mem_nhds (U ⊓ V).one_mem
    obtain ⟨y,hy,hy0⟩ := nonzero_near_zero F q _ hn
    have hxy : x * KPPGLLocalCover.LowerN F ζ hζ (Sum.inr q) y ∈ omega F ζ hζ q := by
      obtain ⟨A,hA,hc⟩ := hxB
      have hd : A 1 1 ≠ 0 := by
        intro hd; exact A.det_ne_zero (by simp [Matrix.det_fin_two,hc,hd])
      refine ⟨A * KPStandardLocalRootLifts.lowerN (K F q) y,?_,?_⟩
      · have hl : projection F ζ hζ q (KPPGLLocalCover.LowerN F ζ hζ (Sum.inr q) y) =
            Matrix.ProjGenLinGroup.mk (KPStandardLocalRootLifts.lowerN (K F q) y) := rfl
        rw [map_mul,map_mul,hA,hl]
      · simpa [KPStandardLocalRootLifts.lowerN, Matrix.mul_apply, Fin.sum_univ_two,hc] using mul_ne_zero hd hy0
    have ha := congrFun (hU _ hy.1) x
    have hb := congrFun (hV _ hy.2) x
    exact ha.symm.trans ((ho _ hxy).trans hb)

end
end DedekindZetaZeroFree.KPActualScalarBinding
