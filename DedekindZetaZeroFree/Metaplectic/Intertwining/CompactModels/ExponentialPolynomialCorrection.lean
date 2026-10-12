module

public import DedekindZetaZeroFree.Metaplectic.Intertwining.ChamberIntegrals.FiniteIwasawaDisplacement

@[expose] public section

noncomputable section
open scoped NumberField Classical Topology
open NumberField ValuativeRel
set_option backward.isDefEq.respectTransparency false
namespace DedekindZetaZeroFree.KPGlobalResidualConstruction.StandardIntertwinerProducers.NonzeroResidue.LocalCompactChange
open KPLocalPrincipalSeries KPLocalExceptionalConstruction
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (q : IsDedekindDomain.HeightOneSpectrum (𝓞 F))
variable (S : CanonicalFiniteInducingData F ζ hζ q)

def forwardAbs (J : IwasawaData S.borel) (g : ActualCover F ζ hζ q) : ℝ :=
  localAbs (LocalField F q) (S.borel.coordinate (S.borel.retract (J.borelPart g)))

theorem forwardAbs_pos (J : IwasawaData S.borel) (g : ActualCover F ζ hζ q) :
    0 < forwardAbs F ζ hζ q S J g := localAbs_pos _ _

theorem forwardAbs_factorization (J : IwasawaData S.borel)
    (b : S.borel.B) (k : J.compact.toOpenSubgroup) :
    forwardAbs F ζ hζ q S J ((b : ActualCover F ζ hζ q) * k.val) =
      localAbs (LocalField F q) (S.borel.coordinate (S.borel.retract b)) := by
  let g : ActualCover F ζ hζ q := (b : ActualCover F ζ hζ q) * k.val
  let d : S.borel.B := (J.borelPart g)⁻¹ * b
  have hd : (d : ActualCover F ζ hζ q) = (J.compactPart g).val * k.val⁻¹ := by
    have hg := J.decomposition g
    change (J.borelPart g).val⁻¹ * b.val = _
    apply (mul_right_cancel_iff).mp
    change (J.borelPart g).val⁻¹ * b.val * k.val =
      ((J.compactPart g).val * k.val⁻¹) * k.val
    rw [mul_assoc, show b.val * k.val = g from rfl]
    calc
      (J.borelPart g).val⁻¹ * g =
          (J.borelPart g).val⁻¹ * ((J.borelPart g).val * (J.compactPart g).val) :=
        congrArg (fun z => (J.borelPart g).val⁻¹ * z) hg
      _ = ((J.compactPart g).val * k.val⁻¹) * k.val := by simp
  have hmem : (d : ActualCover F ζ hζ q) ∈ J.compact.toOpenSubgroup := by
    rw [hd]
    exact J.compact.toOpenSubgroup.mul_mem (J.compactPart g).property
      (J.compact.toOpenSubgroup.inv_mem k.property)
  have hnorm := J.intersection_norm d hmem
  have hb : b = J.borelPart g * d := by simp [d]
  change forwardAbs F ζ hζ q S J g = _
  conv_rhs => rw [hb, map_mul, map_mul, localAbs_mul, hnorm, mul_one]
  rfl

theorem forwardAbs_compact (J : IwasawaData S.borel) (k : J.compact.toOpenSubgroup) :
    forwardAbs F ζ hζ q S J k.val = 1 := by
  simp [forwardAbs, J.borelPart_compact, localAbs_one]

theorem forwardAbs_mul_compact (J : IwasawaData S.borel)
    (g : ActualCover F ζ hζ q) (k : J.compact.toOpenSubgroup) :
    forwardAbs F ζ hζ q S J (g * k.val) = forwardAbs F ζ hζ q S J g := by
  have hg : g * k.val = (J.borelPart g).val * (J.compactPart g * k).val := by
    conv_lhs => rw [J.decomposition g]
    exact mul_assoc _ _ _
  rw [hg]
  exact forwardAbs_factorization F ζ hζ q S J (J.borelPart g) (J.compactPart g * k)

theorem forwardAbs_borel_mul (J : IwasawaData S.borel)
    (b : S.borel.B) (g : ActualCover F ζ hζ q) :
    forwardAbs F ζ hζ q S J (b.val * g) =
      localAbs (LocalField F q) (S.borel.coordinate (S.borel.retract b)) *
        forwardAbs F ζ hζ q S J g := by
  have hg : b.val * g = (b * J.borelPart g).val * (J.compactPart g).val := by
    conv_lhs => rw [J.decomposition g]
    exact (mul_assoc _ _ _).symm
  rw [hg, forwardAbs_factorization, map_mul, map_mul, localAbs_mul]
  rfl

theorem forwardAbs_locallyConstant (J : IwasawaData S.borel) :
    IsLocallyConstant (forwardAbs F ζ hζ q S J) := by
  apply (IsLocallyConstant.iff_exists_open _).mpr
  intro g
  let U : Set (ActualCover F ζ hζ q) :=
    (fun x => g⁻¹ * x) ⁻¹' (J.compact.toOpenSubgroup : Set (ActualCover F ζ hζ q))
  refine ⟨U, J.compact.toOpenSubgroup.isOpen.preimage (continuous_const.mul continuous_id), ?_, ?_⟩
  · change g⁻¹ * g ∈ J.compact.toOpenSubgroup
    simpa using J.compact.toOpenSubgroup.one_mem
  · intro x hx
    let k : J.compact.toOpenSubgroup := ⟨g⁻¹ * x, hx⟩
    have hxg : x = g * k.val := by simp [k]
    rw [hxg]
    exact forwardAbs_mul_compact F ζ hζ q S J g k

def logCorrection (J J' : IwasawaData S.borel) (g : ActualCover F ζ hζ q) : ℝ :=
  Real.log (forwardAbs F ζ hζ q S J' g) - Real.log (forwardAbs F ζ hζ q S J g)

theorem logCorrection_locallyConstant (J J' : IwasawaData S.borel) :
    IsLocallyConstant (logCorrection F ζ hζ q S J J') := by
  exact ((forwardAbs_locallyConstant F ζ hζ q S J').comp Real.log).sub
    ((forwardAbs_locallyConstant F ζ hζ q S J).comp Real.log)

theorem logCorrection_compact_range_finite (J J' : IwasawaData S.borel) :
    (Set.range (fun k : J.compact.toOpenSubgroup =>
      logCorrection F ζ hζ q S J J' k.val)).Finite := by
  letI : CompactSpace J.compact.toOpenSubgroup :=
    isCompact_iff_compactSpace.mp J.compact.isCompact
  exact ((logCorrection_locallyConstant F ζ hζ q S J J').comp_continuous
    continuous_subtype_val).range_finite

theorem logCorrection_borel_mul (J J' : IwasawaData S.borel)
    (b : S.borel.B) (g : ActualCover F ζ hζ q) :
    logCorrection F ζ hζ q S J J' (b.val * g) =
      logCorrection F ζ hζ q S J J' g := by
  unfold logCorrection
  rw [forwardAbs_borel_mul, forwardAbs_borel_mul,
    Real.log_mul (localAbs_pos _ _).ne' (forwardAbs_pos F ζ hζ q S J' g).ne',
    Real.log_mul (localAbs_pos _ _).ne' (forwardAbs_pos F ζ hζ q S J g).ne']
  ring

theorem logCorrection_mul_common_compact (J J' : IwasawaData S.borel)
    (g : ActualCover F ζ hζ q) (k : J.compact.toOpenSubgroup)
    (hk : k.val ∈ J'.compact.toOpenSubgroup) :
    logCorrection F ζ hζ q S J J' (g * k.val) =
      logCorrection F ζ hζ q S J J' g := by
  unfold logCorrection
  rw [forwardAbs_mul_compact F ζ hζ q S J g k,
    forwardAbs_mul_compact F ζ hζ q S J' g ⟨k.val,hk⟩]

open KPLocalStoneVonNeumann

def correctedCompact (J J' : IwasawaData S.borel)
    (P : Polarization S.heisenberg) (s : ℂ) :
    compactPicture S.borel P J .plus →ₗ[ℂ] compactPicture S.borel P J .plus where
  toFun φ := ⟨fun k => Complex.exp (s * (logCorrection F ζ hζ q S J J' k.val : ℂ)) • φ.val k, by
    constructor
    · intro b k k' hk
      have he : logCorrection F ζ hζ q S J J' k'.val =
          logCorrection F ζ hζ q S J J' k.val := by
        rw [hk]
        exact logCorrection_borel_mul F ζ hζ q S J J' b k.val
      change Complex.exp (s * (logCorrection F ζ hζ q S J J' k'.val : ℂ)) • φ.val k' =
        inducingAction S.borel P .plus 0 b
          (Complex.exp (s * (logCorrection F ζ hζ q S J J' k.val : ℂ)) • φ.val k)
      rw [he, φ.property.1 b k k' hk, map_smul]
    · obtain ⟨U,hU⟩ := φ.property.2
      let V := J'.compact.toOpenSubgroup.comap J.compact.toOpenSubgroup.subtype
        continuous_subtype_val
      refine ⟨U ⊓ V, ?_⟩
      intro k hk
      apply funext
      intro x
      have hφ := congrFun (hU k hk.1) x
      change φ.val (x * k) = φ.val x at hφ
      change Complex.exp (s * (logCorrection F ζ hζ q S J J' (x * k).val : ℂ)) • φ.val (x * k) = _
      rw [hφ]
      change Complex.exp (s * (logCorrection F ζ hζ q S J J' (x.val * k.val) : ℂ)) • φ.val x = _
      rw [logCorrection_mul_common_compact F ζ hζ q S J J' x.val k hk.2]⟩
  map_add' φ ψ := by
    apply Subtype.ext
    funext k
    exact smul_add _ _ _
  map_smul' c φ := by
    apply Subtype.ext
    funext k
    change Complex.exp (s * (logCorrection F ζ hζ q S J J' k.val : ℂ)) • (c • φ.val k) =
      c • (Complex.exp (s * (logCorrection F ζ hζ q S J J' k.val : ℂ)) • φ.val k)
    exact smul_comm _ _ _

@[simp] theorem correctedCompact_zero (J J' : IwasawaData S.borel)
    (P : Polarization S.heisenberg) (φ : compactPicture S.borel P J .plus) :
    correctedCompact F ζ hζ q S J J' P 0 φ = φ := by
  apply Subtype.ext
  funext k
  simp [correctedCompact]

theorem correctedCompact_displacement (J J' : IwasawaData S.borel)
    (P : Polarization S.heisenberg) (φ : compactPicture S.borel P J .plus)
    (s : ℂ) (g : ActualCover F ζ hζ q) :
    (compactTrivialization S.borel P J .plus s
      (correctedCompact F ζ hζ q S J J' P s φ)).val g =
      Complex.exp (s * (Real.log (forwardAbs F ζ hζ q S J' g) : ℂ)) •
        (compactTrivialization S.borel P J .plus 0 φ).val g := by
  have hcorr : logCorrection F ζ hζ q S J J' g =
      logCorrection F ζ hζ q S J J' (J.compactPart g).val := by
    conv_lhs => rw [J.decomposition g]
    exact logCorrection_borel_mul F ζ hζ q S J J' (J.borelPart g) (J.compactPart g).val
  change inducingAction S.borel P .plus s (J.borelPart g)
    (Complex.exp (s * (logCorrection F ζ hζ q S J J' (J.compactPart g).val : ℂ)) • φ.val (J.compactPart g)) = _
  rw [map_smul, ← hcorr]
  change _ = Complex.exp (s * (Real.log (forwardAbs F ζ hζ q S J' g) : ℂ)) •
    (inducingAction S.borel P .plus 0 (J.borelPart g) (φ.val (J.compactPart g)))
  change Complex.exp (s * (logCorrection F ζ hζ q S J J' g : ℂ)) •
      ((inducingScalar S.borel s (J.borelPart g)) •
        borelAction S.borel P .plus (J.borelPart g) (φ.val (J.compactPart g))) =
    Complex.exp (s * (Real.log (forwardAbs F ζ hζ q S J' g) : ℂ)) •
      ((inducingScalar S.borel 0 (J.borelPart g)) •
        borelAction S.borel P .plus (J.borelPart g) (φ.val (J.compactPart g)))
  simp only [inducingScalar, normPower, zero_mul, Complex.exp_zero, mul_one, smul_smul]
  congr 1
  unfold logCorrection forwardAbs
  push_cast
  rw [mul_sub, Complex.exp_sub]
  have hn : Complex.exp (s * (Real.log (localAbs (LocalField F q)
      (S.borel.coordinate (S.borel.retract (J.borelPart g)))) : ℂ)) ≠ 0 :=
    Complex.exp_ne_zero _
  field_simp

def correctionComponent (J J' : IwasawaData S.borel)
    (P : Polarization S.heisenberg) (r : ℝ) :
    compactPicture S.borel P J .plus →ₗ[ℂ] compactPicture S.borel P J .plus where
  toFun φ := ⟨fun k => if logCorrection F ζ hζ q S J J' k.val = r then φ.val k else 0, by
    constructor
    · intro b k k' hk
      change (if logCorrection F ζ hζ q S J J' k'.val = r then φ.val k' else 0) =
        inducingAction S.borel P .plus 0 b
          (if logCorrection F ζ hζ q S J J' k.val = r then φ.val k else 0)
      have he : logCorrection F ζ hζ q S J J' k'.val =
          logCorrection F ζ hζ q S J J' k.val := by
        rw [hk]
        exact logCorrection_borel_mul F ζ hζ q S J J' b k.val
      rw [he]
      split_ifs <;> simp [φ.property.1 b k k' hk]
    · obtain ⟨U,hU⟩ := φ.property.2
      let V := J'.compact.toOpenSubgroup.comap J.compact.toOpenSubgroup.subtype continuous_subtype_val
      refine ⟨U ⊓ V, ?_⟩
      intro k hk
      funext x
      have hφ := congrFun (hU k hk.1) x
      change φ.val (x * k) = φ.val x at hφ
      change (if logCorrection F ζ hζ q S J J' (x.val * k.val) = r then φ.val (x * k) else 0) =
        (if logCorrection F ζ hζ q S J J' x.val = r then φ.val x else 0)
      rw [hφ, logCorrection_mul_common_compact F ζ hζ q S J J' x.val k hk.2]⟩
  map_add' φ ψ := by
    apply Subtype.ext
    funext k
    change (if _ then φ.val k + ψ.val k else 0) = _
    split_ifs with h <;> simp [h]
  map_smul' c φ := by
    apply Subtype.ext
    funext k
    change (if _ then c • φ.val k else 0) = _
    split_ifs with h <;> simp [h]

def correctionSpectrum (J J' : IwasawaData S.borel) : Finset ℝ :=
  (logCorrection_compact_range_finite F ζ hζ q S J J').toFinset

theorem correctedCompact_expansion (J J' : IwasawaData S.borel)
    (P : Polarization S.heisenberg) (φ : compactPicture S.borel P J .plus) (s : ℂ) :
    correctedCompact F ζ hζ q S J J' P s φ =
      ∑ r ∈ correctionSpectrum F ζ hζ q S J J', Complex.exp (s * (r : ℂ)) •
        correctionComponent F ζ hζ q S J J' P r φ := by
  apply Subtype.ext
  funext k
  change Complex.exp (s * (logCorrection F ζ hζ q S J J' k.val : ℂ)) • φ.val k = _
  simp only [Submodule.coe_sum, Finset.sum_apply, Submodule.coe_smul, Pi.smul_apply,
    correctionComponent, LinearMap.coe_mk, AddHom.coe_mk]
  rw [Finset.sum_eq_single (logCorrection F ζ hζ q S J J' k.val)]
  · simp
  · intro r hr hne
    rw [if_neg (Ne.symm hne), smul_zero]
  · intro h
    exact False.elim (h ((Set.Finite.mem_toFinset _).mpr ⟨k,rfl⟩))

end DedekindZetaZeroFree.KPGlobalResidualConstruction.StandardIntertwinerProducers.NonzeroResidue.LocalCompactChange

end
