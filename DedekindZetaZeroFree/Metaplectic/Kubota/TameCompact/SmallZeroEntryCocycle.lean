module

public import DedekindZetaZeroFree.Metaplectic.Kubota.TameCompact.CorrectionAndDeterminantTwist

@[expose] public section

open scoped NumberField ValuativeRel Classical
open NumberField IsDedekindDomain

namespace DedekindZetaZeroFree.KPTameCompact

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000

private lemma entry_c (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) (g h : K0 F v) :
    c F v (g * h) = c F v g * a F v h + d F v g * c F v h := by
  simp [c, a, d, Matrix.mul_apply, Fin.sum_univ_two]

private lemma entry_a (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) (g h : K0 F v) :
    a F v (g * h) = a F v g * a F v h + b F v g * c F v h := by
  simp [c, a, b, Matrix.mul_apply, Fin.sum_univ_two]

private lemma entry_d (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) (g h : K0 F v) :
    d F v (g * h) = c F v g * b F v h + d F v g * d F v h := by
  simp [c, b, d, Matrix.mul_apply, Fin.sum_univ_two]

private lemma X_zero (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) (g : K0 F v) (hc : c F v g = 0)
    (D : (K F v)ˣ) (hD : (D : K F v) = d F v g) :
    KubotaRankTwo.X (K F v) (inclusion F v g) = D := by
  apply Units.ext
  simpa [KubotaRankTwo.X, KubotaRankTwo.x, inclusion,
    KPLocalCube.integerInclusion, hc] using hD.symm

private lemma X_nonzero (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) (g : K0 F v) (hc : c F v g ≠ 0)
    (C : (K F v)ˣ) (hC : (C : K F v) = c F v g) :
    KubotaRankTwo.X (K F v) (inclusion F v g) = C := by
  apply Units.ext
  simpa [KubotaRankTwo.X, KubotaRankTwo.x, inclusion,
    KPLocalCube.integerInclusion, hc] using hC.symm

private lemma kappa_raw (F : Type) [Field F] [NumberField F]
    (ζ : F) (hζ : IsPrimitiveRoot ζ 12) (v : HeightOneSpectrum (𝓞 F))
    (g : K0 F v) (hc : c F v g ≠ 0) (hn : ‖c F v g‖ < 1)
    (C D : (K F v)ˣ) (hC : (C : K F v) = c F v g)
    (hD : (D : K F v) = d F v g) :
    kappa F v ζ hζ g = KPHilbert.B3 F ζ hζ (Sum.inr v) C
      (D / Matrix.GeneralLinearGroup.det (inclusion F v g)) := by
  have hd : d F v g ≠ 0 := hD ▸ D.ne_zero
  simp only [kappa, dif_pos hc, dif_pos hd, dif_pos hn]
  congr 1
  · apply Units.ext; exact hC.symm
  · apply Units.ext; simp [hD]

theorem kappa_mul_small_zero
    (F : Type) [Field F] [NumberField F]
    (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (v : HeightOneSpectrum (𝓞 F))
    (hv : ringChar (O F v ⧸ p F v) ≠ 3)
    (g h : K0 F v)
    (hc : ‖c F v g‖ < 1) (he : ‖c F v h‖ < 1)
    (hzero : c F v g = 0 ∨ c F v h = 0) :
    kappa F v ζ hζ (g * h) =
      kappa F v ζ hζ g * kappa F v ζ hζ h *
        KPLocalCover.sigmaTwo F ζ hζ (Sum.inr v)
          (inclusion F v g) (inclusion F v h) := by
  let B := KPHilbert.B3 F ζ hζ (Sum.inr v)
  let i := unitInclusion F v
  obtain ⟨ag, hag⟩ := (diagonal_units F v g hc).1
  obtain ⟨dg, hdg⟩ := (diagonal_units F v g hc).2.1
  obtain ⟨ah, hah⟩ := (diagonal_units F v h he).1
  obtain ⟨dh, hdh⟩ := (diagonal_units F v h he).2.1
  let A := i ag
  let D := i dg
  let U := i ah
  let V := i dh
  let pg := Matrix.GeneralLinearGroup.det g
  let ph := Matrix.GeneralLinearGroup.det h
  let P := i pg
  let Q := i ph
  have hA : (A : K F v) = a F v g := congrArg (fun x : O F v => (x : K F v)) hag
  have hD : (D : K F v) = d F v g := congrArg (fun x : O F v => (x : K F v)) hdg
  have hU : (U : K F v) = a F v h := congrArg (fun x : O F v => (x : K F v)) hah
  have hV : (V : K F v) = d F v h := congrArg (fun x : O F v => (x : K F v)) hdh
  have hP : Matrix.GeneralLinearGroup.det (inclusion F v g) = P :=
    Matrix.GeneralLinearGroup.map_det _ _
  have hQ : Matrix.GeneralLinearGroup.det (inclusion F v h) = Q :=
    Matrix.GeneralLinearGroup.map_det _ _
  have hPQ : Matrix.GeneralLinearGroup.det (inclusion F v (g * h)) = P * Q := by
    rw [map_mul, map_mul, hP, hQ]
  have hL : ∀ x y z, B (x*y) z = B x z * B y z :=
    (KPHilbert.B3_laws F ζ hζ (Sum.inr v)).1
  have hR : ∀ x y z, B x (y*z) = B x y * B x z :=
    (KPHilbert.B3_laws F ζ hζ (Sum.inr v)).2.1
  have hSk : ∀ x y, B x y = (B y x)⁻¹ :=
    (KPHilbert.B3_laws F ζ hζ (Sum.inr v)).2.2.1
  have hInv : ∀ x y, B x y⁻¹ = (B x y)⁻¹ :=
    KubotaDefectSymbolAlgebra.inv_right (K F v) (rootsOfUnity 3 F) B hR
  have hUU : ∀ x y : (O F v)ˣ, B (i x) (i y) = 1 := B3_units F v ζ hζ hv
  have hSigma : KPLocalCover.sigmaTwo F ζ hζ (Sum.inr v)
      (inclusion F v g) (inclusion F v h) =
      B (KubotaRankTwo.X (K F v) (inclusion F v (g * h)) /
          KubotaRankTwo.X (K F v) (inclusion F v g))
        (KubotaRankTwo.X (K F v) (inclusion F v (g * h)) /
          (KubotaRankTwo.X (K F v) (inclusion F v h) * P)) := by
    unfold KPLocalCover.sigmaTwo
    rw [det_twist_trivial F v ζ hζ hv g h, mul_one]
    unfold KubotaElementaryLastArgument.tau
    rw [← map_mul, hP]
  rcases hzero with hcg | hch
  · have hzg : c F v (g * h) = d F v g * c F v h := by
      rw [entry_c, hcg, zero_mul, zero_add]
    have hn : ‖c F v (g * h)‖ < 1 := by
      rw [hzg, norm_mul]
      calc
        ‖d F v g‖ * ‖c F v h‖ ≤ 1 * ‖c F v h‖ :=
          mul_le_mul_of_nonneg_right ((det_norm_and_entries F v g).2 1 1) (norm_nonneg _)
        _ < 1 := by simpa using he
    rw [kappa_zero F v ζ hζ g hcg, one_mul]
    by_cases hch : c F v h = 0
    · have hz : c F v (g * h) = 0 := by rw [hzg, hch, mul_zero]
      rw [kappa_zero F v ζ hζ h hch, kappa_zero F v ζ hζ (g*h) hz, one_mul]
      have hdprod : ((D * V : (K F v)ˣ) : K F v) = d F v (g*h) := by
        simp [entry_d, hcg, hD, hV]
      rw [hSigma, X_zero F v (g*h) hz (D*V) hdprod,
        X_zero F v g hcg D hD, X_zero F v h hch V hV]
      have eq1 : D * V / D = V := by apply Units.ext; simp only [Units.val_div_eq_div_val, Units.val_mul]; field_simp
      have eq2 : D * V / (V * P) = D / P := by apply Units.ext; simp only [Units.val_div_eq_div_val, Units.val_mul]; field_simp
      rw [eq1, eq2]
      exact (hUU dh (dg / pg)).symm.trans (by simp [i, D, P, V])
    · let E := Units.mk0 (c F v h) hch
      have hz : c F v (g*h) ≠ 0 := by
        rw [hzg]; exact mul_ne_zero (diagonal_units F v g hc).2.2.2 hch
      have hDE : ((D*E : (K F v)ˣ) : K F v) = c F v (g*h) := by simp [E, hD, hzg]
      have hdprod : ((D*V : (K F v)ˣ) : K F v) = d F v (g*h) := by
        simp [entry_d, hcg, hD, hV]
      rw [kappa_raw F ζ hζ v (g*h) hz hn (D*E) (D*V) hDE hdprod,
        kappa_raw F ζ hζ v h hch he E V rfl hV, hPQ, hQ,
        hSigma, X_nonzero F v (g*h) hz (D*E) hDE,
        X_zero F v g hcg D hD, X_nonzero F v h hch E rfl]
      change B (D*E) ((D*V)/(P*Q)) = B E (V/Q) * B (D*E/D) (D*E/(E*P))
      have eq1 : D*E/D = E := by apply Units.ext; simp only [Units.val_div_eq_div_val, Units.val_mul]; field_simp
      have eq2 : D*E/(E*P) = D/P := by apply Units.ext; simp only [Units.val_div_eq_div_val, Units.val_mul]; field_simp
      have eq3 : (D*V)/(P*Q) = (D/P)*(V/Q) := by apply Units.ext; simp only [Units.val_div_eq_div_val, Units.val_mul]; field_simp
      rw [eq1, eq2, eq3, hL, hR, hR]
      have uu1 : B D (D/P) = 1 := by simpa [D, P, i] using hUU dg (dg/pg)
      have uu2 : B D (V/Q) = 1 := by simpa [D, V, Q, i] using hUU dg (dh/ph)
      rw [uu1, uu2, one_mul, one_mul]; exact mul_comm _ _
  · have hzg : c F v (g*h) = c F v g * a F v h := by
      rw [entry_c, hch, mul_zero, add_zero]
    have hn : ‖c F v (g*h)‖ < 1 := by
      rw [hzg, norm_mul]
      calc
        ‖c F v g‖ * ‖a F v h‖ ≤ ‖c F v g‖ * 1 :=
          mul_le_mul_of_nonneg_left ((det_norm_and_entries F v h).2 0 0) (norm_nonneg _)
        _ < 1 := by simpa using hc
    rw [kappa_zero F v ζ hζ h hch, mul_one]
    by_cases hcg : c F v g = 0
    · have hz : c F v (g*h) = 0 := by rw [hzg, hcg, zero_mul]
      rw [kappa_zero F v ζ hζ g hcg, kappa_zero F v ζ hζ (g*h) hz, one_mul]
      have hdprod : ((D * V : (K F v)ˣ) : K F v) = d F v (g*h) := by
        simp [entry_d, hcg, hD, hV]
      rw [hSigma, X_zero F v (g*h) hz (D*V) hdprod,
        X_zero F v g hcg D hD, X_zero F v h hch V hV]
      have eq1 : D * V / D = V := by
        apply Units.ext; simp only [Units.val_div_eq_div_val, Units.val_mul]; field_simp
      have eq2 : D * V / (V * P) = D / P := by
        apply Units.ext; simp only [Units.val_div_eq_div_val, Units.val_mul]; field_simp
      rw [eq1, eq2]
      exact (hUU dh (dg / pg)).symm.trans (by simp [i, D, P, V])
    · let C := Units.mk0 (c F v g) hcg
      have hz : c F v (g*h) ≠ 0 := by
        rw [hzg]; exact mul_ne_zero hcg (diagonal_units F v h he).2.2.1
      have hCU : ((C*U : (K F v)ˣ) : K F v) = c F v (g*h) := by simp [C, hU, hzg]
      have hAU : ((A*U : (K F v)ˣ) : K F v) = a F v (g*h) := by
        simp [entry_a, hch, hA, hU]
      have hgk : kappa F v ζ hζ g = B C A⁻¹ := by
        rw [kappa_active F v ζ hζ hv g hcg hc]
        congr 1
        apply Units.ext; simp only [Units.val_mk0, Units.val_inv_eq_inv_val, hA]
      have hghk : kappa F v ζ hζ (g*h) = B (C*U) (A*U)⁻¹ := by
        rw [kappa_active F v ζ hζ hv (g*h) hz hn]
        congr 1
        · apply Units.ext; exact hCU.symm
        · apply Units.ext; simp only [Units.val_mk0, Units.val_inv_eq_inv_val, hAU]
      rw [hgk, hghk, hSigma, X_nonzero F v (g*h) hz (C*U) hCU,
        X_nonzero F v g hcg C rfl, X_zero F v h hch V hV]
      change B (C*U) (A*U)⁻¹ = B C A⁻¹ * B (C*U/C) (C*U/(V*P))
      have eq1 : C*U/C = U := by
        apply Units.ext; simp only [Units.val_div_eq_div_val, Units.val_mul]; field_simp
      have eq2 : C*U/(V*P) = C * (U/(V*P)) := by
        apply Units.ext; simp only [Units.val_div_eq_div_val, Units.val_mul]; field_simp
      have eq3 : (A*U)⁻¹ = A⁻¹ * U⁻¹ := by
        apply Units.ext; simp only [Units.val_inv_eq_inv_val, Units.val_mul]; exact mul_inv _ _
      have uu1 : B U A⁻¹ = 1 := by simpa only [A, U, ← map_inv] using hUU ah ag⁻¹
      have uu2 : B U U⁻¹ = 1 := by simpa only [U, ← map_inv] using hUU ah ah⁻¹
      have uu3 : B U (U/(V*P)) = 1 := by
        simpa only [U, V, P, ← map_mul, ← map_div] using hUU ah (ah/(dh*pg))
      rw [eq1, eq2, eq3, hL, hR, hR, hR, uu1, uu2, uu3,
        one_mul, mul_one, mul_one, hSk U C, ← hInv C U]

end
end DedekindZetaZeroFree.KPTameCompact
