module

public import DedekindZetaZeroFree.RepresentationTheory.Jacquet.TameBruhatTestDuality

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.ActualFiniteBorel.LowShellUnitCharts
open scoped NumberField Classical commutatorElement
open NumberField IsDedekindDomain ValuativeRel
open KPLocalExceptionalConstruction KPTameJacquetTestDuality
set_option backward.isDefEq.respectTransparency false
variable (F : Type) [Field F] [NumberField F]
  (ζ : F) (hζ : IsPrimitiveRoot ζ 12) (q : HeightOneSpectrum (𝓞 F))

theorem torus_conjugate (a : actualTorus F ζ hζ q) (v : (LocalField F q)ˣ) :
    (a : ActualCover F ζ hζ q) * KPPGLLocalCover.A F ζ hζ (Sum.inr q) v *
        (a : ActualCover F ζ hζ q)⁻¹ =
    KPPGLLocalCover.centralInjection F ζ hζ (Sum.inr q)
      (KPHilbert.B3 F ζ hζ (Sum.inr q) (ActualFiniteTorus.coordinate F ζ hζ q a) v) *
        KPPGLLocalCover.A F ζ hζ (Sum.inr q) v := by
  let u : actualTorus F ζ hζ q := ActualFiniteTorus.torusLift F ζ hζ q v
  have hu : ActualFiniteTorus.coordinate F ζ hζ q u = v :=
    ((ActualFiniteTorus.actual_torus_normal_form F ζ hζ q).2.2.2.2.2.2 1 v u (by
      simp [u, ActualFiniteTorus.torusLift, ActualFiniteTorus.normalWord])).1
  have hc := (ActualFiniteTorus.actual_cube_quotient_pairing F ζ hζ q).2.2.2.2.2.1 a u
  have hcv := congrArg (fun z : actualTorus F ζ hζ q => (z : ActualCover F ζ hζ q)) hc
  simp only [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv, hu] at hcv
  have he := congrArg (fun z : ActualCover F ζ hζ q => z * (u : ActualCover F ζ hζ q)) hcv
  simpa only [mul_assoc, inv_mul_cancel, mul_one, u, ActualFiniteTorus.torusLift,
    ActualFiniteTorus.normalWord, map_one, one_mul, ActualFiniteTorus.central,
    MonoidHom.codRestrict_apply] using he

theorem outer_chart (e : actualTorus F ζ hζ q) (v : (LocalField F q)ˣ)
    (x : LocalField F q) :
    ((e : ActualCover F ζ hζ q) * KPPGLLocalCover.W F ζ hζ (Sum.inr q) *
        KPPGLLocalCover.N F ζ hζ (Sum.inr q) (x / (v : LocalField F q))) *
      KPPGLLocalCover.A F ζ hζ (Sum.inr q) v⁻¹ =
    ((e : ActualCover F ζ hζ q) * KPPGLLocalCover.A F ζ hζ (Sum.inr q) v *
        (e : ActualCover F ζ hζ q)⁻¹) *
      ((e : ActualCover F ζ hζ q) * KPPGLLocalCover.W F ζ hζ (Sum.inr q) *
        KPPGLLocalCover.N F ζ hζ (Sum.inr q) x) := by
  rw [mul_assoc, KPCorrectedBruhatLifts.quotient_upper_diagonal,
    mul_assoc (e : ActualCover F ζ hζ q),
    ← mul_assoc (KPPGLLocalCover.W F ζ hζ (Sum.inr q)),
    KPCorrectedBruhatLifts.quotient_weyl_diagonal]
  simp only [inv_inv, Units.val_inv_eq_inv_val, div_inv_eq_mul, div_mul_cancel₀ x v.ne_zero]
  group
variable (S : CanonicalFiniteInducingData F ζ hζ q)

theorem actual_weyl_word (h : actualTorus F ζ hζ q) :
    ((S.borel.weyl h : actualTorus F ζ hζ q) : ActualCover F ζ hζ q) =
      (KPPGLLocalCover.W F ζ hζ (Sum.inr q))⁻¹ * (h : ActualCover F ζ hζ q) *
        KPPGLLocalCover.W F ζ hζ (Sum.inr q) := by
  have hn : ((S.borel.cubeLift (-1) : actualTorus F ζ hζ q) : ActualCover F ζ hζ q) =
      KPPGLLocalCover.A F ζ hζ (Sum.inr q) (-1) := by
    rw [S.cube_actual]
    congr 1
    apply Units.ext
    change (-1 : LocalField F q) ^ 3 = -1
    ring
  have hc : Commute (h : ActualCover F ζ hζ q)
      (KPPGLLocalCover.A F ζ hζ (Sum.inr q) (-1)) := by
    have ht := Subgroup.mem_center_iff.mp (S.heisenberg.central
      (S.borel.cubeLift (-1)).property) h
    have ht' := congrArg (fun z : actualTorus F ζ hζ q => (z : ActualCover F ζ hζ q)) ht
    change _ * _ = _ * _ at ht'
    rw [hn] at ht'
    exact ht'
  rw [← S.torus_full, S.borel.weyl_from_lift, S.torus_full,
    (S.openCell S.polarization).weyl_eq]
  simp only [KPRankOneOpenCellKernel.signedWeyl,
    KPRankOneOpenCellKernel.signedWeylRaw, map_mul]
  change (KPPGLLocalCover.A F ζ hζ (Sum.inr q) (-1) *
      KPPGLLocalCover.W F ζ hζ (Sum.inr q))⁻¹ * (h : ActualCover F ζ hζ q) *
      (KPPGLLocalCover.A F ζ hζ (Sum.inr q) (-1) *
        KPPGLLocalCover.W F ζ hζ (Sum.inr q)) = _
  rw [mul_inv_rev]
  calc
    _ = (KPPGLLocalCover.W F ζ hζ (Sum.inr q))⁻¹ *
        ((KPPGLLocalCover.A F ζ hζ (Sum.inr q) (-1))⁻¹ *
          ((h : ActualCover F ζ hζ q) * KPPGLLocalCover.A F ζ hζ (Sum.inr q) (-1))) *
        KPPGLLocalCover.W F ζ hζ (Sum.inr q) := by group
    _ = _ := by rw [hc.eq, inv_mul_cancel_left]

theorem coordinate_normal_word (h : actualTorus F ζ hζ q)
    (e : rootsOfUnity 3 F) (v : (LocalField F q)ˣ)
    (hh : (h : ActualCover F ζ hζ q) =
      KPPGLLocalCover.centralInjection F ζ hζ (Sum.inr q) e *
        KPPGLLocalCover.A F ζ hζ (Sum.inr q) v) : S.borel.coordinate h = v := by
  let a : actualTorus F ζ hζ q := ActualFiniteTorus.torusLift F ζ hζ q v
  have ha : (a : ActualCover F ζ hζ q) = KPPGLLocalCover.A F ζ hζ (Sum.inr q) v := by
    simp [a, ActualFiniteTorus.torusLift, ActualFiniteTorus.normalWord]
  have he : h = (S.central e : actualTorus F ζ hζ q) * a := by
    apply Subtype.ext
    simpa only [Subgroup.coe_mul, S.central_actual, ha] using hh
  have hce : (S.central e : actualTorus F ζ hζ q) =
      (S.openCell S.polarization).centralTorus e := by
    apply Subtype.ext
    rw [S.central_actual, ← S.torus_full,
      (S.openCell S.polarization).central_eq]
  rw [he, map_mul, hce, (S.openCell S.polarization).central_coordinate,
    S.coordinate_lift a v ha, one_mul]

theorem normalized_chiH_word (P : KPLocalStoneVonNeumann.Polarization S.heisenberg)
    (hP : IsTamePolarization F ζ hζ q S P)
    (hnorm : ∀ (h : HL F ζ hζ q S P) (e : rootsOfUnity 3 F)
      (u : (KPTameCompact.O F q)ˣ) (y : (LocalField F q)ˣ),
      (h.val : ActualCover F ζ hζ q) =
        KPPGLLocalCover.centralInjection F ζ hζ (Sum.inr q) e *
          KPPGLLocalCover.A F ζ hζ (Sum.inr q) (KPTameCompact.unitInclusion F q u) *
          KPPGLLocalCover.A F ζ hζ (Sum.inr q) (y ^ 3) →
      (P.ωL h : ℂ) = (ordinaryIota F ζ hζ e : ℂ) *
        KPLocalPrincipalSeries.normPower (LocalField F q) (y ^ 3) (1 / 6))
    (h : HL F ζ hζ q S P) (e : rootsOfUnity 3 F) (u : (KPTameCompact.O F q)ˣ)
    (hh : (h.val : ActualCover F ζ hζ q) =
      KPPGLLocalCover.centralInjection F ζ hζ (Sum.inr q) e *
        KPPGLLocalCover.A F ζ hζ (Sum.inr q) (KPTameCompact.unitInclusion F q u))
    (ε : KPLocalPrincipalSeries.Sign) :
    chiH F ζ hζ q S P hP ε h = (ordinaryIota F ζ hζ e : ℂ) := by
  have hA1 : KPPGLLocalCover.A F ζ hζ (Sum.inr q) 1 = 1 := by
    change KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q)
      (KPStandardLocalRootLifts.A F ζ hζ (Sum.inr q) 1) = 1
    rw [KPStandardLocalRootLifts.A_one, map_one]
  have hv : KPLocalPrincipalSeries.localAbs (LocalField F q)
      (KPTameCompact.unitInclusion F q u) = 1 := by
    have hu : valuation (LocalField F q) (KPTameCompact.unitInclusion F q u : LocalField F q) = 1 :=
      (Valuation.integer.integers (valuation (LocalField F q))).valuation_unit u
    simp [KPLocalPrincipalSeries.localAbs, hu]
  have hn : KPLocalPrincipalSeries.normPower (LocalField F q)
      (S.borel.coordinate h.val) (1 / 2) = 1 := by
    rw [coordinate_normal_word F ζ hζ q S h.val e _ hh]
    simp [KPLocalPrincipalSeries.normPower, hv]
  have homega : (P.ωL h : ℂ) = (ordinaryIota F ζ hζ e : ℂ) := by
    have ho := hnorm h e u 1 (by simpa [hA1] using hh)
    simpa [KPLocalPrincipalSeries.normPower, KPLocalPrincipalSeries.localAbs_one] using ho
  have hw : ((weylHL F ζ hζ q S P hP h).val : ActualCover F ζ hζ q) =
      KPPGLLocalCover.centralInjection F ζ hζ (Sum.inr q) e *
        KPPGLLocalCover.A F ζ hζ (Sum.inr q) (KPTameCompact.unitInclusion F q u⁻¹) := by
    change ((S.borel.weyl h.val : actualTorus F ζ hζ q) : ActualCover F ζ hζ q) = _
    rw [actual_weyl_word F ζ hζ q S, hh]
    have hz := Subgroup.mem_center_iff.mp
      (KPPGLLocalCover.centralInjection_range_le_center F ζ hζ (Sum.inr q) ⟨e, rfl⟩)
      (KPPGLLocalCover.W F ζ hζ (Sum.inr q))⁻¹
    rw [← mul_assoc, hz, mul_assoc, ← mul_assoc]
    have hW : (KPPGLLocalCover.W F ζ hζ (Sum.inr q))⁻¹ =
        KPPGLLocalCover.W F ζ hζ (Sum.inr q) :=
      inv_eq_of_mul_eq_one_right (by simpa [pow_two] using KPPGLLocalCover.W_sq F ζ hζ (Sum.inr q))
    rw [hW, mul_assoc (KPPGLLocalCover.centralInjection F ζ hζ (Sum.inr q) e),
      KPCorrectedBruhatLifts.quotient_weyl_diagonal, mul_assoc]
    rw [mul_assoc (KPPGLLocalCover.A F ζ hζ (Sum.inr q) _),
      show KPPGLLocalCover.W F ζ hζ (Sum.inr q) *
        KPPGLLocalCover.W F ζ hζ (Sum.inr q) = 1 from
        (by simpa [pow_two] using KPPGLLocalCover.W_sq F ζ hζ (Sum.inr q)), mul_one]
    congr 2
  have hminus : (P.ωL (weylHL F ζ hζ q S P hP h) : ℂ) =
      (ordinaryIota F ζ hζ e : ℂ) := by
    have ho := hnorm (weylHL F ζ hζ q S P hP h) e u⁻¹ 1 (by simpa [hA1] using hw)
    simpa [KPLocalPrincipalSeries.normPower, KPLocalPrincipalSeries.localAbs_one] using ho
  cases ε <;> simp only [chiH, hn, homega, hminus, mul_one]

local instance : (KPPGLLocalCover.scalarSubgroup F (Sum.inr q)).Normal :=
  KPPGLLocalCover.scalarSubgroup_normal F (Sum.inr q)

theorem diagonal_coordinate (x y : (LocalField F q)ˣ)
    (a : actualTorus F ζ hζ q)
    (ha : (a : ActualCover F ζ hζ q) =
      KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q)
        (KPLocalCover.sectionMap F ζ hζ (Sum.inr q) (KubotaRankTwo.d (LocalField F q) x y))) :
    ActualFiniteTorus.coordinate F ζ hζ q a = x / y := by
  obtain ⟨⟨e, v⟩, he, _⟩ := (ActualFiniteTorus.actual_torus_normal_form F ζ hζ q).2.1 a
  have hp := congrArg (KPLocalSmoothRepresentation.projection F ζ hζ q) (he.symm.trans ha)
  have hz : KPLocalSmoothRepresentation.projection F ζ hζ q
      (KPPGLLocalCover.centralInjection F ζ hζ (Sum.inr q) e) = 1 := by
    change KPLocalSmoothRepresentation.ordinaryPGLMap F q
      (KPPGLLocalCover.projection F ζ hζ (Sum.inr q)
        (KPPGLLocalCover.centralInjection F ζ hζ (Sum.inr q) e)) = 1
    have hk : KPPGLLocalCover.centralInjection F ζ hζ (Sum.inr q) e ∈
        (KPPGLLocalCover.projection F ζ hζ (Sum.inr q)).ker := by
      rw [← KPPGLLocalCover.range_centralInjection_eq_ker_projection]
      exact ⟨e, rfl⟩
    rw [show KPPGLLocalCover.projection F ζ hζ (Sum.inr q)
      (KPPGLLocalCover.centralInjection F ζ hζ (Sum.inr q) e) = 1 from hk, map_one]
  simp only [ActualFiniteTorus.normalWord, map_mul, hz, one_mul] at hp
  change Matrix.ProjGenLinGroup.mk (KubotaRankTwo.d (LocalField F q) v 1) =
    Matrix.ProjGenLinGroup.mk (KubotaRankTwo.d (LocalField F q) x y) at hp
  obtain ⟨c, hc⟩ := Matrix.ProjGenLinGroup.mk_eq_mk_iff.mp hp
  have h00 := congrArg (fun g : Matrix.GeneralLinearGroup (Fin 2) (LocalField F q) =>
    g.val 0 0) hc
  have h11 := congrArg (fun g : Matrix.GeneralLinearGroup (Fin 2) (LocalField F q) =>
    g.val 1 1) hc
  simp [Matrix.mul_apply, Matrix.GeneralLinearGroup.coe_scalar,
    Matrix.scalar, Matrix.diagonal_apply, KubotaRankTwo.coe_d] at h00 h11
  have hv : v = x / y := by
    apply Units.ext
    simp only [Units.val_div_eq_div_val]
    apply (eq_div_iff y.ne_zero).mpr
    rw [← h11]
    exact h00
  rw [((ActualFiniteTorus.actual_torus_normal_form F ζ hζ q).2.2.2.2.2.2 e v a he).1, hv]

theorem unit_word_mem_HL
    (P : KPLocalStoneVonNeumann.Polarization S.heisenberg)
    (hP : IsTamePolarization F ζ hζ q S P) (e : rootsOfUnity 3 F)
    (u : (KPTameCompact.O F q)ˣ) :
    (⟨ActualFiniteTorus.normalWord F ζ hζ q e (KPTameCompact.unitInclusion F q u),
      (ActualFiniteTorus.actual_torus_normal_form F ζ hζ q).1 e _⟩ : actualTorus F ζ hζ q)
      ∈ HL F ζ hζ q S P := by
  let h : actualTorus F ζ hζ q := ⟨ActualFiniteTorus.normalWord F ζ hζ q e
    (KPTameCompact.unitInclusion F q u),
      (ActualFiniteTorus.actual_torus_normal_form F ζ hζ q).1 e _⟩
  have hc : S.borel.coordinate h = KPTameCompact.unitInclusion F q u :=
    coordinate_normal_word F ζ hζ q S h e _ rfl
  change S.heisenberg.π h ∈ P.L
  have hu : S.cubeClassEquiv (S.heisenberg.π h) ∈
      KPTameValuationCoordinates.unitCubeClasses (LocalField F q) := by
    rw [S.cube_class, hc]
    exact ⟨KPTameCompact.unitInclusion F q u,
      (Subgroup.mem_sup_left ⟨u, rfl⟩), rfl⟩
  rw [← hP] at hu
  obtain ⟨d, hd, he⟩ := hu
  exact S.cubeClassEquiv.injective he ▸ hd

theorem literal_chi_ratio
    (P : KPLocalStoneVonNeumann.Polarization S.heisenberg)
    (hP : IsTamePolarization F ζ hζ q S P)
    (hnorm : ∀ (h : HL F ζ hζ q S P) (e : rootsOfUnity 3 F)
      (u : (KPTameCompact.O F q)ˣ) (y : (LocalField F q)ˣ),
      (h.val : ActualCover F ζ hζ q) =
        KPPGLLocalCover.centralInjection F ζ hζ (Sum.inr q) e *
          KPPGLLocalCover.A F ζ hζ (Sum.inr q) (KPTameCompact.unitInclusion F q u) *
          KPPGLLocalCover.A F ζ hζ (Sum.inr q) (y ^ 3) →
      (P.ωL h : ℂ) = (ordinaryIota F ζ hζ e : ℂ) *
        KPLocalPrincipalSeries.normPower (LocalField F q) (y ^ 3) (1 / 6))
    (bm bp : BL F ζ hζ q S P) (em ep : rootsOfUnity 3 F)
    (u : (KPTameCompact.O F q)ˣ)
    (hm : ((retractL F ζ hζ q S P bm).val : ActualCover F ζ hζ q) =
      KPPGLLocalCover.centralInjection F ζ hζ (Sum.inr q) em *
        KPPGLLocalCover.A F ζ hζ (Sum.inr q) (KPTameCompact.unitInclusion F q u))
    (hp : ((retractL F ζ hζ q S P bp).val : ActualCover F ζ hζ q) =
      KPPGLLocalCover.centralInjection F ζ hζ (Sum.inr q) ep *
        KPPGLLocalCover.A F ζ hζ (Sum.inr q) (KPTameCompact.unitInclusion F q u)) :
    chi F ζ hζ q S P hP .minus bm / chi F ζ hζ q S P hP .plus bp =
      (ordinaryIota F ζ hζ (em / ep) : ℂ) := by
  rw [chi, chi, normalized_chiH_word F ζ hζ q S P hP hnorm _ em u hm,
    normalized_chiH_word F ζ hζ q S P hP hnorm _ ep u hp, map_div,
    Units.val_div_eq_div_val]

end DedekindZetaZeroFree.ActualFiniteBorel.LowShellUnitCharts

end
