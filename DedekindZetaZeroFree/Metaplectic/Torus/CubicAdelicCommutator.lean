module

public import DedekindZetaZeroFree.Arithmetic.ResidueSymbols.Cubic.IdeleUnitValuationPairing

@[expose] public section

open scoped NumberField Classical BigOperators
open NumberField IsDedekindDomain
namespace DedekindZetaZeroFree.RepresentationTheory.KPGlobalCubicIdelePairingRaw
open KubotaRankTwo
noncomputable section
set_option autoImplicit false
variable (F : Type) [Field F] [NumberField F]
variable (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
private theorem diag_eval (v : KPHilbert.Place F) (a : Ideles F) :
    KPAdelicCoverRestrictedProduct.matrixEval F v (diagonalHom F a) =
      KubotaRankTwo.d (KPHilbert.Completion F v) (ideleEval F v a) 1 := by
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [KPAdelicCoverRestrictedProduct.matrixEval, diagonalHom, diagonalMatrix,
      Matrix.GeneralLinearGroup.map, ideleEval, KubotaRankTwo.coe_d]

private theorem d_mul (K : Type*) [Field K] (a b : Kˣ) :
    KubotaRankTwo.d K a 1 * KubotaRankTwo.d K b 1 = KubotaRankTwo.d K (a*b) 1 := by
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two]

private theorem local_sigma (v : KPHilbert.Place F) (a b : (KPHilbert.Completion F v)ˣ) :
    KPLocalCover.sigmaTwo F ζ hζ v
      (KubotaRankTwo.d (KPHilbert.Completion F v) a 1)
      (KubotaRankTwo.d (KPHilbert.Completion F v) b 1) =
      KPHilbert.B3 F ζ hζ v a b ^ 2 := by
  have hone : ∀ c, KPHilbert.B3 F ζ hζ v 1 c = 1 := by
    intro c
    have h := (KPHilbert.B3_laws F ζ hζ v).1 1 1 c
    simpa using h.symm
  simp [KPLocalCover.sigmaTwo, KubotaElementaryLastArgument.tau,
    d_mul, hone]

private theorem local_twist (v : KPHilbert.Place F)
    (x y : KPLocalCover.CubicGL2Raw F ζ hζ v)
    (a b : (KPHilbert.Completion F v)ˣ)
    (hx : x.g = KubotaRankTwo.d (KPHilbert.Completion F v) a 1)
    (hy : y.g = KubotaRankTwo.d (KPHilbert.Completion F v) b 1) :
    x * y = KPLocalCover.centralInjection F ζ hζ v
      (KPHilbert.B3 F ζ hζ v a b ^ 4) * (y * x) := by
  have ext_raw : ∀ (r s : KPLocalCover.CubicGL2Raw F ζ hζ v),
      r.g = s.g → r.epsilon = s.epsilon → r = s := by
    rintro ⟨_, _⟩ ⟨_, _⟩ hg he
    cases hg; cases he; rfl
  apply ext_raw
  · simp only [KPLocalCover.mul_g, KPLocalCover.centralInjection_g, one_mul, hx, hy, d_mul]
    rw [mul_comm a b]
  · simp only [KPLocalCover.mul_epsilon, KPLocalCover.centralInjection_epsilon,
      KPLocalCover.centralInjection_g, KPLocalCover.sigmaTwo_one_left, mul_one,
      hx, hy, local_sigma]
    rw [(KPHilbert.B3_laws F ζ hζ v).2.2.1 b a]
    simp [pow_succ, mul_assoc, mul_left_comm, mul_comm]

private theorem amalgamate_tuple (ε : KPAdelicCoverRestrictedProduct.CentralTuples F) :
    KPAdelicCoverRestrictedProduct.amalgamation F ζ hζ
      (KPAdelicCoverRestrictedProduct.centralTupleMap F ζ hζ ε) =
    KPAdelicCoverRestrictedProduct.centralInjection F ζ hζ
      (KPAdelicCoverRestrictedProduct.centralProduct F ε) := by
  let v := KPAdelicCoverRestrictedProduct.distinguishedPlace F
  let δ : KPAdelicCoverRestrictedProduct.CentralTuples F :=
    RestrictedProduct.mulSingle (fun _ => (⊥ : Subgroup (rootsOfUnity 3 F))) v
      (KPAdelicCoverRestrictedProduct.centralProduct F ε)
  have hδ : KPAdelicCoverRestrictedProduct.centralProduct F δ =
      KPAdelicCoverRestrictedProduct.centralProduct F ε := by
    change (∏ᶠ w, δ w) = _
    rw [finprod_eq_single _ v]
    · exact RestrictedProduct.mulSingle_eq_same _ _ _
    · intro w hw
      exact RestrictedProduct.mulSingle_eq_of_ne _ _ hw
  have ht : KPAdelicCoverRestrictedProduct.centralTupleMap F ζ hζ δ =
      KPAdelicCoverRestrictedProduct.localToRestricted F ζ hζ v
        (KPLocalCover.centralInjection F ζ hζ v
          (KPAdelicCoverRestrictedProduct.centralProduct F ε)) := by
    apply RestrictedProduct.ext
    intro w
    by_cases hw : w = v
    · subst w
      change KPLocalCover.centralInjection F ζ hζ v (δ v) = _
      rw [RestrictedProduct.mulSingle_eq_same]
      exact (RestrictedProduct.mulSingle_eq_same _ _ _).symm
    · change KPLocalCover.centralInjection F ζ hζ w (δ w) = _
      rw [RestrictedProduct.mulSingle_eq_of_ne _ _ hw]
      rw [map_one]
      exact (RestrictedProduct.mulSingle_eq_of_ne _ _ hw).symm
  change _ = KPAdelicCoverRestrictedProduct.amalgamation F ζ hζ
    (KPAdelicCoverRestrictedProduct.localToRestricted F ζ hζ v _)
  rw [← ht]
  apply div_eq_one.mp
  rw [← map_div, ← map_div]
  apply (QuotientGroup.eq_one_iff _).mpr
  refine ⟨ε / δ, ?_, rfl⟩
  change KPAdelicCoverRestrictedProduct.centralProduct F (ε / δ) = 1
  simp [hδ]

private theorem restricted_twist (a b : Ideles F)
    (r s : KPAdelicCoverRestrictedProduct.RestrictedCover F ζ hζ)
    (hr : KPAdelicCoverRestrictedProduct.restrictedProjection F ζ hζ r = diagonalHom F a)
    (hs : KPAdelicCoverRestrictedProduct.restrictedProjection F ζ hζ s = diagonalHom F b) :
    KPAdelicCoverRestrictedProduct.amalgamation F ζ hζ r *
      KPAdelicCoverRestrictedProduct.amalgamation F ζ hζ s =
    KPAdelicCoverRestrictedProduct.centralInjection F ζ hζ
      (beta3 F ζ hζ (QuotientGroup.mk' _ a) (QuotientGroup.mk' _ b) ^ 4) *
      (KPAdelicCoverRestrictedProduct.amalgamation F ζ hζ s *
        KPAdelicCoverRestrictedProduct.amalgamation F ζ hζ r) := by
  let f := fun v => KPHilbert.B3 F ζ hζ v (ideleEval F v a) (ideleEval F v b)
  have hf : Function.HasFiniteMulSupport f :=
    pairing_finiteSupport F ζ hζ (restrictedClassMap F a) (restrictedClassMap F b)
  let ε : KPAdelicCoverRestrictedProduct.CentralTuples F :=
    ⟨fun v => f v ^ 4, by
      have h := (hf.compl_mem_cofinite)
      filter_upwards [h] with v hv
      change f v ^ 4 = 1
      have hv' : f v = 1 := by simpa [Function.mulSupport] using hv
      simp [hv']⟩
  have he : KPAdelicCoverRestrictedProduct.centralProduct F ε =
      beta3 F ζ hζ (QuotientGroup.mk' _ a) (QuotientGroup.mk' _ b) ^ 4 := by
    change (∏ᶠ v, f v ^ 4) = (∏ᶠ v, f v) ^ 4
    exact (finprod_pow hf 4).symm
  have ht : r * s = KPAdelicCoverRestrictedProduct.centralTupleMap F ζ hζ ε * (s * r) := by
    apply RestrictedProduct.ext
    intro v
    apply local_twist F ζ hζ v (r v) (s v) (ideleEval F v a) (ideleEval F v b)
    · rw [← KPLocalCover.projection_apply,
        ← KPAdelicCoverRestrictedProduct.restrictedProjection_eval, hr, diag_eval]
    · rw [← KPLocalCover.projection_apply,
        ← KPAdelicCoverRestrictedProduct.restrictedProjection_eval, hs, diag_eval]
  rw [← map_mul, ht, map_mul, amalgamate_tuple, he, map_mul]

private theorem central_twist {G : Type*} [Group G] (c d z u v : G)
    (hc : c ∈ Subgroup.center G) (hd : d ∈ Subgroup.center G)
    (hz : z ∈ Subgroup.center G) (h : u * v = z * (v * u)) :
    (c * u) * (d * v) = z * ((d * v) * (c * u)) := by
  have ccomm := Subgroup.mem_center_iff.mp hc
  have dcomm := Subgroup.mem_center_iff.mp hd
  have zcomm := Subgroup.mem_center_iff.mp hz
  calc
    (c * u) * (d * v) = (c * d) * (u * v) := by
      calc
        _ = c * (u * d) * v := by simp only [mul_assoc]
        _ = c * (d * u) * v := by rw [dcomm u]
        _ = _ := by simp only [mul_assoc]
    _ = (c * d) * (z * (v * u)) := by rw [h]
    _ = z * ((d * c) * (v * u)) := by
      rw [← mul_assoc, zcomm (c*d), ccomm d, mul_assoc]
    _ = z * ((d * v) * (c * u)) := by
      calc
        _ = z * (d * (c * v) * u) := by simp only [mul_assoc]
        _ = z * (d * (v * c) * u) := by rw [ccomm v]
        _ = _ := by simp only [mul_assoc]

private theorem pgl_twist (a b : Ideles F)
    (x y : KPAdelicCoverRestrictedProduct.CubicPGL2Adelic F ζ hζ)
    (hx : KPAdelicCoverRestrictedProduct.pglProjection F ζ hζ x = diagonalPGL F a)
    (hy : KPAdelicCoverRestrictedProduct.pglProjection F ζ hζ y = diagonalPGL F b) :
    x * y = KPAdelicCoverRestrictedProduct.pglCentralInjection F ζ hζ
      (beta3 F ζ hζ (QuotientGroup.mk' _ a) (QuotientGroup.mk' _ b) ^ 4) * (y*x) := by
  obtain ⟨r, hr⟩ := KPAdelicCoverRestrictedProduct.restrictedProjection_surjective F ζ hζ (diagonalHom F a)
  obtain ⟨s, hs⟩ := KPAdelicCoverRestrictedProduct.restrictedProjection_surjective F ζ hζ (diagonalHom F b)
  let u := KPAdelicCoverRestrictedProduct.scalarQuotient F ζ hζ (KPAdelicCoverRestrictedProduct.amalgamation F ζ hζ r)
  let v := KPAdelicCoverRestrictedProduct.scalarQuotient F ζ hζ (KPAdelicCoverRestrictedProduct.amalgamation F ζ hζ s)
  have hu : KPAdelicCoverRestrictedProduct.pglProjection F ζ hζ u = diagonalPGL F a := by
    change QuotientGroup.mk' _ (KPAdelicCoverRestrictedProduct.restrictedProjection F ζ hζ r) = _
    rw [hr]; rfl
  have hv : KPAdelicCoverRestrictedProduct.pglProjection F ζ hζ v = diagonalPGL F b := by
    change QuotientGroup.mk' _ (KPAdelicCoverRestrictedProduct.restrictedProjection F ζ hζ s) = _
    rw [hs]; rfl
  have hcu : x / u ∈ (KPAdelicCoverRestrictedProduct.pglProjection F ζ hζ).ker := by
    change KPAdelicCoverRestrictedProduct.pglProjection F ζ hζ (x/u) = 1
    rw [map_div, hx, hu, div_self']
  have hdv : y / v ∈ (KPAdelicCoverRestrictedProduct.pglProjection F ζ hζ).ker := by
    change KPAdelicCoverRestrictedProduct.pglProjection F ζ hζ (y/v) = 1
    rw [map_div, hy, hv, div_self']
  have hc := KPAdelicCoverRestrictedProduct.pglCentralInjection_central F ζ hζ
    ((KPAdelicCoverRestrictedProduct.pglCentralInjection_kernel F ζ hζ).symm ▸ hcu)
  have hd := KPAdelicCoverRestrictedProduct.pglCentralInjection_central F ζ hζ
    ((KPAdelicCoverRestrictedProduct.pglCentralInjection_kernel F ζ hζ).symm ▸ hdv)
  have hz := KPAdelicCoverRestrictedProduct.pglCentralInjection_central F ζ hζ
    ⟨beta3 F ζ hζ (QuotientGroup.mk' _ a) (QuotientGroup.mk' _ b) ^ 4, rfl⟩
  have h := congrArg (KPAdelicCoverRestrictedProduct.scalarQuotient F ζ hζ)
    (restricted_twist F ζ hζ a b r s hr hs)
  simp only [map_mul] at h
  have ht := central_twist (x/u) (y/v) _ u v hc hd hz h
  simpa only [div_mul_cancel] using ht

theorem cover_torus_commutator (x y : E F ζ hζ) :
    x * y * x⁻¹ * y⁻¹ = torusCentralInjection F ζ hζ
      (beta3 F ζ hζ
        (QuotientGroup.mk' _ (torusProjection F ζ hζ x))
        (QuotientGroup.mk' _ (torusProjection F ζ hζ y)) ^ 4) := by
  apply Subtype.ext
  apply Prod.ext
  · have h := pgl_twist F ζ hζ x.val.2 y.val.2 x.val.1 y.val.1 x.property y.property
    change x.val.1 * y.val.1 * x.val.1⁻¹ * y.val.1⁻¹ = _
    rw [h]
    simp only [mul_assoc, mul_inv_cancel, mul_one]
    rfl
  · change x.val.2 * y.val.2 * x.val.2⁻¹ * y.val.2⁻¹ = 1
    simp [mul_assoc, mul_left_comm, mul_comm]
end
end DedekindZetaZeroFree.RepresentationTheory.KPGlobalCubicIdelePairingRaw
