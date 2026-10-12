module

public import DedekindZetaZeroFree.HarmonicAnalysis.Poisson.PrincipalProbes.CosetTermsAndNormalization
public import DedekindZetaZeroFree.Adeles.Characters.PrincipalFiniteTrace
public import DedekindZetaZeroFree.HarmonicAnalysis.Poisson.SIntegers.TraceAnnihilator

@[expose] public section

namespace DedekindZetaZeroFree.ProbeCoset
noncomputable section
open scoped Classical NumberField
open NumberField IsDedekindDomain MeasureTheory
variable {F : Type} [Field F] [NumberField F]

local instance bridgeCompletionMeasurable (v : HeightOneSpectrum (RingOfIntegers F)) :
    MeasurableSpace (v.adicCompletion F) := borel _
local instance bridgeLocalProductMeasurable
    (S : Finset (HeightOneSpectrum (RingOfIntegers F))) :
    MeasurableSpace (SLocalProduct F S) := borel _

local instance bridgeCompletionBorel (v : HeightOneSpectrum (RingOfIntegers F)) :
    BorelSpace (v.adicCompletion F) := ⟨rfl⟩
local instance bridgeLocalProductBorel
    (S : Finset (HeightOneSpectrum (RingOfIntegers F))) :
    BorelSpace (SLocalProduct F S) := ⟨rfl⟩

theorem raw_tracePhase_eq (A : SArithmeticData F)
    (e : (v : ↥A.Sf) → AddChar (v.val.adicCompletion F) Circle)
    (u v : SLocalProduct F A.Sf) :
    PoissonS.tracePhase F A.Sf e (PoissonS.localProductToSpace F A.Sf u)
      (PoissonS.localProductToSpace F A.Sf v) =
      ProbeAdditive.phase F A.Sf e (u * v) := by
  have ht : PoissonArch.tracePairing F (PoissonArch.infiniteAdeleToSpace F u.1)
      (PoissonArch.infiniteAdeleToSpace F v.1) =
      ∑ w : InfinitePlace F, 2 * (InfinitePlace.Completion.extensionEmbedding w
        (u.1 w * v.1 w)).re := by
    rw [← Fintype.sum_subtype_add_sum_subtype (fun w : InfinitePlace F => w.IsReal)]
    unfold PoissonArch.tracePairing
    rw [PoissonArch.infiniteAdeleToSpace_coordinates,
      PoissonArch.infiniteAdeleToSpace_coordinates]
    dsimp only
    congr 1
    · apply Finset.sum_congr rfl
      intro w hw
      exact (InfinitePlace.not_isReal_iff_isComplex.mpr (A.complex_place w.val)
        w.property).elim
    · rw [Finset.mul_sum]
      apply Fintype.sum_equiv
        (Equiv.subtypeEquivRight fun w : InfinitePlace F =>
          InfinitePlace.not_isReal_iff_isComplex).symm
      intro w
      simp only [InfinitePlace.Completion.ringEquivComplexOfIsComplex_apply,
        map_mul]
      rfl
  unfold PoissonS.tracePhase ProbeAdditive.phase ProbeAdditive.archPhase
  change Complex.exp (2 * (Real.pi : ℂ) * Complex.I *
      (PoissonArch.tracePairing F (PoissonArch.infiniteAdeleToSpace F u.1)
        (PoissonArch.infiniteAdeleToSpace F v.1) : ℂ)) * _ = _
  rw [ht]
  simp only [Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_ofNat]
  rfl

theorem raw_diagonal_tracePhase_eq (A : SArithmeticData F) (σ : F →+* ℂ)
    (η : RayClassCharacter F A.modulus) (hS : A.ContainsTraceBadPlaces)
    (P : NormalizedProbe.PrincipalData A σ η hS) (x y : F) :
    PoissonS.tracePhase F A.Sf P.finiteTrace (PoissonS.diagonalHom F A.Sf x)
      (PoissonS.diagonalHom F A.Sf y) = P.coefficients.additiveCharacter (x * y) := by
  rw [P.sameTrace]
  have hd (z : F) : PoissonS.diagonalHom F A.Sf z =
      PoissonS.localProductToSpace F A.Sf (sLocalDiagonal F A.Sf z) := by
    apply Prod.ext
    · apply (mixedEmbedding.euclidean.toMixed F).injective
      change (mixedEmbedding.euclidean.toMixed F)
          ((mixedEmbedding.euclidean.toMixed F).symm (mixedEmbedding F z)) =
        (mixedEmbedding.euclidean.toMixed F) (PoissonArch.infiniteAdeleToSpace F
          ((sLocalDiagonal F A.Sf z).1))
      rw [ContinuousLinearEquiv.apply_symm_apply,
        PoissonArch.infiniteAdeleToSpace_coordinates]
      have hfst : (sLocalDiagonal F A.Sf z).1 = algebraMap F (InfiniteAdeleRing F) z := by
        funext w
        rw [sLocalDiagonal_infinite]
        exact (InfiniteAdeleRing.algebraMap_apply F z w).symm
      rw [hfst, ← InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp]
    · rfl
  rw [hd, hd, raw_tracePhase_eq]
  congr 1
  exact (sLocalDiagonal F A.Sf).map_mul x y |>.symm

theorem raw_fourier_coordinate_eq (A : SArithmeticData F) (σ : F →+* ℂ)
    (η : RayClassCharacter F A.modulus) (hS : A.ContainsTraceBadPlaces)
    (P : NormalizedProbe.PrincipalData A σ η hS)
    (N : Normalization A σ η hS P) (y : SLocalProduct F A.Sf) :
    ProbeWeight.fourier F A.Sf P.finiteTrace P.additiveMeasure P.W0 y =
      PoissonS.fourierIntegral F A.Sf P.finiteTrace N.localMeasure
        (fun x => P.W0 ((PoissonS.localProductToSpace F A.Sf).symm x))
        (PoissonS.localProductToSpace F A.Sf y) := by
  let E : SLocalProduct F A.Sf ≃ₜ PoissonS.Space F A.Sf :=
    (PoissonArch.infiniteAdeleToSpace F).toHomeomorph.prodCongr (Homeomorph.refl _)
  have hE : E.toEquiv = (PoissonS.localProductToSpace F A.Sf).toEquiv := rfl
  rw [ProbeWeight.fourier, N.sameMeasure]
  change (∫ x, P.W0 x * ProbeAdditive.phase F A.Sf P.finiteTrace (-x * y)
      ∂Measure.map E.symm (PoissonS.productMeasure F A.Sf N.localMeasure)) = _
  rw [E.symm.measurableEmbedding.integral_map]
  unfold PoissonS.fourierIntegral
  apply integral_congr_ae
  filter_upwards [] with x
  rw [show ProbeAdditive.phase F A.Sf P.finiteTrace
      (-E.symm x * y) = PoissonS.tracePhase F A.Sf P.finiteTrace
        (-x) (PoissonS.localProductToSpace F A.Sf y) by
    rw [← raw_tracePhase_eq A P.finiteTrace]
    change PoissonS.tracePhase F A.Sf P.finiteTrace
      (PoissonS.localProductToSpace F A.Sf (-((PoissonS.localProductToSpace F A.Sf).symm x)))
      (PoissonS.localProductToSpace F A.Sf y) = _
    rw [map_neg, AddEquiv.apply_symm_apply]]
  simp only [PoissonS.tracePhase, Prod.fst_neg, Prod.snd_neg, Pi.neg_apply,
    PoissonArch.tracePairing_eq_inner, inner_neg_left, Complex.ofReal_neg]
  rw [← mul_assoc]
  change P.W0 ((PoissonS.localProductToSpace F A.Sf).symm x) *
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I * -_) * _ = _
  congr 2
  congr 1
  ring

theorem raw_annular_tensor_coordinates (A : SArithmeticData F) (W : SLocalProduct F A.Sf → ℂ)
    (hW : ProbeWeight.IsAnnularTensor F A.Sf W) :
    ∃ (f : SchwartzMap (PoissonArch.Space F) ℂ)
      (φ : (v : ↥A.Sf) → v.val.adicCompletion F → ℂ),
      (∀ v, IsLocallyConstant (φ v)) ∧ (∀ v, HasCompactSupport (φ v)) ∧
      ∀ x, W ((PoissonS.localProductToSpace F A.Sf).symm x) =
        PoissonS.tensorFunction F A.Sf f φ x := by
  letI : NumberField.IsTotallyComplex F := ⟨A.complex_place⟩
  letI : IsEmpty {v : InfinitePlace F // v.IsReal} :=
    ⟨fun v => (InfinitePlace.not_isReal_iff_isComplex.mpr (A.complex_place v.val)) v.property⟩
  obtain ⟨fr, fc, ff, hr, hc, hf, hw⟩ := hW
  have hsm : ContDiff ℝ (⊤ : ℕ∞) (TateTensorProfile.archTensor F fc) := by
    apply contDiff_prod
    intro v _
    exact (hc v).1.comp ((contDiff_apply ℝ ℂ v).comp
      (contDiff_snd.comp (mixedEmbedding.euclidean.toMixed F).contDiff))
  let Kc := Set.pi Set.univ (fun v => tsupport (fc v))
  let K := (mixedEmbedding.euclidean.toMixed F) ⁻¹'
    ((Set.univ : Set ((v : {v : InfinitePlace F // v.IsReal}) → ℝ)) ×ˢ Kc)
  have hK : IsCompact K :=
    (mixedEmbedding.euclidean.toMixed F).toHomeomorph.isCompact_preimage.mpr
      (isCompact_univ.prod (isCompact_univ_pi (fun v => (hc v).2.1)))
  have hco : HasCompactSupport (TateTensorProfile.archTensor F fc) := by
    refine HasCompactSupport.intro hK ?_
    intro x hx
    by_contra hn
    apply hx
    refine ⟨Set.mem_univ _, ?_⟩
    intro v _
    exact subset_tsupport _ ((Finset.prod_ne_zero_iff.mp hn) v (Finset.mem_univ v))
  refine ⟨hco.toSchwartzMap hsm, ff, fun v => (hf v).1, fun v => (hf v).2.1, ?_⟩
  intro x
  rw [hw]
  simp only [Finset.univ_eq_empty, Finset.prod_empty, one_mul]
  change (∏ v, fc v ((InfiniteAdeleRing.ringEquiv_mixedSpace F
    ((PoissonArch.infiniteAdeleToSpace F).symm x.1)).2 v)) * (∏ v, ff v (x.2 v)) =
    TateTensorProfile.archTensor F fc x.1 * (∏ v, ff v (x.2 v))
  rw [TateTensorProfile.archTensor]
  have hh := PoissonArch.infiniteAdeleToSpace_coordinates F
    ((PoissonArch.infiniteAdeleToSpace F).symm x.1)
  rw [ContinuousLinearEquiv.apply_symm_apply] at hh
  rw [hh]

theorem raw_productModule_eq_modulus (A : SArithmeticData F) (a : A.R) (ha : a ≠ 0) :
    PoissonS.productModule F A.Sf (a : F) = ProbeCoset.modulus A a := by
  exact (sProductModulus_eq_principalIdeal_index F A.Sf a ha).2

def raw_localUnits (A : SArithmeticData F) : A.G ≃* (SLocalProduct F A.Sf)ˣ :=
  ((MulEquiv.piUnits).symm.prodCongr (MulEquiv.piUnits).symm).trans
    (MulEquiv.prodUnits).symm

theorem raw_localDilationModule_eq_norm (A : SArithmeticData F) (g : A.G) :
    PoissonS.localDilationModule F A.Sf (raw_localUnits A g) = A.norm g := by
  unfold PoissonS.localDilationModule SArithmeticData.norm
  congr 1
  change ‖((raw_localUnits A g).val).1‖ = _
  rw [InfiniteAdeleRing.norm_def]
  apply Finset.prod_congr rfl
  intro v _
  rw [(A.complex_place v).mult_eq_two]
  rfl

 theorem raw_diagonal_coordinates (A : SArithmeticData F) (z : F) : PoissonS.diagonalHom F A.Sf z =
      PoissonS.localProductToSpace F A.Sf (sLocalDiagonal F A.Sf z) := by
    apply Prod.ext
    · apply (mixedEmbedding.euclidean.toMixed F).injective
      change (mixedEmbedding.euclidean.toMixed F)
          ((mixedEmbedding.euclidean.toMixed F).symm (mixedEmbedding F z)) =
        (mixedEmbedding.euclidean.toMixed F) (PoissonArch.infiniteAdeleToSpace F
          ((sLocalDiagonal F A.Sf z).1))
      rw [ContinuousLinearEquiv.apply_symm_apply,
        PoissonArch.infiniteAdeleToSpace_coordinates]
      have hfst : (sLocalDiagonal F A.Sf z).1 = algebraMap F (InfiniteAdeleRing F) z := by
        funext w
        rw [sLocalDiagonal_infinite]
        exact (InfiniteAdeleRing.algebraMap_apply F z w).symm
      rw [hfst, ← InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp]
    · rfl

 theorem raw_scalar_diagonal (A : SArithmeticData F) (c x : F) :
    PoissonS.ScaleShift.scalarAction F A.Sf c (PoissonS.diagonalHom F A.Sf x) =
      PoissonS.diagonalHom F A.Sf (c*x) := by
  rw [raw_diagonal_coordinates, raw_diagonal_coordinates]
  unfold PoissonS.ScaleShift.scalarAction
  change PoissonS.localProductToSpace F A.Sf
    (sLocalDiagonal F A.Sf c * (PoissonS.localProductToSpace F A.Sf).symm
      (PoissonS.localProductToSpace F A.Sf (sLocalDiagonal F A.Sf x))) = _
  rw [AddEquiv.symm_apply_apply, ← map_mul]

 theorem raw_tsum_scalar_lattice (A : SArithmeticData F) (c : Fˣ) (f : PoissonS.Space F A.Sf → ℂ) :
    (∑' m : PoissonS.lattice F A.Sf (c : F), f m) =
      ∑' n : A.R, f (PoissonS.diagonalHom F A.Sf ((c : F)*(n : F))) := by
  have hr := PoissonS.ScaleShift.tsum_scalar_lattice F A.Sf c 1 f
  rw [mul_one] at hr
  rw [← hr, ← (PoissonS.ScaleShift.diagonalLatticeEquiv F A.Sf).tsum_eq]
  apply tsum_congr
  intro n
  change f (PoissonS.ScaleShift.scalarAction F A.Sf (c : F)
    (PoissonS.diagonalHom F A.Sf (n : F))) = _
  rw [raw_scalar_diagonal]

set_option maxHeartbeats 800000 in
 theorem raw_translate_dilate_poisson (A : SArithmeticData F) (σ : F →+* ℂ)
    (η : RayClassCharacter F A.modulus) (hS : A.ContainsTraceBadPlaces)
    (P : NormalizedProbe.PrincipalData A σ η hS)
    (N : Normalization A σ η hS P)
    (c : Fˣ) (b : F) (d : (SLocalProduct F A.Sf)ˣ) :
    (∑' n : A.R, P.W0 (sLocalDiagonal F A.Sf ((c : F)*(n : F)+b) * d⁻¹.val)) =
      ((PoissonS.productModule F A.Sf (c : F))⁻¹ : ℂ) *
      (PoissonS.localDilationModule F A.Sf d : ℂ) *
      ∑' h : A.R, P.coefficients.additiveCharacter (((c⁻¹ : Fˣ) : F)*(h : F)*b) *
        ProbeWeight.fourier F A.Sf P.finiteTrace P.additiveMeasure P.W0
          (d.val * sLocalDiagonal F A.Sf (((c⁻¹ : Fˣ) : F)*(h : F))) := by
  letI := N.localHaar
  obtain ⟨f, φ, hl, hs, hw⟩ := raw_annular_tensor_coordinates A P.W0 P.annular
  obtain ⟨g, ψ, hga, hψ, hψl, hψs, hfun⟩ :=
    PoissonS.tensorFunction_local_dilation_bruhatSchwartz F A.Sf f φ hl hs d
  have hdiag (r : A.R) : PoissonS.tracePhase F A.Sf P.finiteTrace
      (PoissonS.diagonalHom F A.Sf (r : F)) (PoissonS.diagonalHom F A.Sf 1) = 1 := by
    rw [raw_diagonal_tracePhase_eq]
    rw [mul_one, P.sameTrace]
    exact P.traceCompatible r
  have hp := PoissonS.poisson_scale_shift F A.Sf N.containsDifferent P.finiteTrace
    N.localMeasure P.continuousTrace N.traceConductor N.localNormalization hdiag
    g ψ hψl hψs c (PoissonS.diagonalHom F A.Sf b) 0
  rw [raw_tsum_scalar_lattice A c (fun x => PoissonS.tensorFunction F A.Sf g ψ
    (x + PoissonS.diagonalHom F A.Sf b) * PoissonS.tracePhase F A.Sf P.finiteTrace 0 x),
    raw_tsum_scalar_lattice A c⁻¹ (fun x => PoissonS.tracePhase F A.Sf P.finiteTrace (x-0)
      (PoissonS.diagonalHom F A.Sf b) * PoissonS.fourierIntegral F A.Sf P.finiteTrace
      N.localMeasure (PoissonS.tensorFunction F A.Sf g ψ) (x-0))] at hp
  have hgf : PoissonS.tensorFunction F A.Sf g ψ =
      (fun x => PoissonS.tensorFunction F A.Sf f φ (PoissonS.localDilation F A.Sf d⁻¹ x)) :=
    funext fun x => (hfun x).symm
  simp only [sub_zero] at hp
  have hzero (x : PoissonS.Space F A.Sf) : PoissonS.tracePhase F A.Sf P.finiteTrace 0 x = 1 := by
    simp [PoissonS.tracePhase, PoissonArch.tracePairing, map_zero]
  simp only [hzero, mul_one, hgf] at hp
  simp_rw [PoissonS.fourierIntegral_local_dilation F A.Sf P.finiteTrace N.localMeasure
    P.continuousTrace f φ hl hs d] at hp
  have hleft : (∑' n : A.R, P.W0 (sLocalDiagonal F A.Sf ((c : F)*(n : F)+b) * d⁻¹.val)) =
      ∑' n : A.R, PoissonS.tensorFunction F A.Sf f φ
        (PoissonS.localDilation F A.Sf d⁻¹
          (PoissonS.diagonalHom F A.Sf ((c : F)*(n : F)) + PoissonS.diagonalHom F A.Sf b)) := by
    apply tsum_congr
    intro n
    rw [← map_add, raw_diagonal_coordinates, ← hw]
    simp only [PoissonS.localDilation, AddEquiv.symm_apply_apply]
    rw [mul_comm]
  rw [hleft, hp]
  rw [mul_assoc]
  congr 1
  rw [← tsum_mul_left]
  apply tsum_congr
  intro h
  rw [raw_diagonal_tracePhase_eq]
  rw [mul_assoc, mul_left_comm _ (PoissonS.localDilationModule F A.Sf d : ℂ)]
  congr 1
  have hW : PoissonS.tensorFunction F A.Sf f φ =
      (fun x => P.W0 ((PoissonS.localProductToSpace F A.Sf).symm x)) := funext fun x => (hw x).symm
  rw [hW, raw_fourier_coordinate_eq A σ η hS P N, raw_diagonal_coordinates]
  simp only [PoissonS.localDilation, AddEquiv.symm_apply_apply]

def raw_residueCosetEquiv (A : SArithmeticData F) (s a : A.R)
    (hs : s ≠ 0) (ha : a ≠ 0) (r : FiniteTransform.Residue A.R.toSubring (s*a)) :
    A.R ≃ {m : A.R // FiniteTransform.residueMap A.R.toSubring (s*a) m = r} := by
  let l := (FiniteTransform.canonicalLifts A.R.toSubring (s*a)).val r
  have hl : FiniteTransform.residueMap A.R.toSubring (s*a) l = r :=
    (FiniteTransform.canonicalLifts A.R.toSubring (s*a)).property r
  let f (n : A.R) : {m : A.R // FiniteTransform.residueMap A.R.toSubring (s*a) m = r} :=
    ⟨l + (s*a)*n, by
      rw [← hl]
      apply Ideal.Quotient.eq.mpr
      apply Ideal.mem_span_singleton.mpr
      exact ⟨n, by ring⟩⟩
  apply Equiv.ofBijective f
  constructor
  · intro x y h
    have hh : l + (s*a)*x = l + (s*a)*y := congrArg Subtype.val h
    exact mul_left_cancel₀ (mul_ne_zero hs ha) (add_left_cancel hh)
  · intro m
    have hh : FiniteTransform.residueMap A.R.toSubring (s*a) m.val =
        FiniteTransform.residueMap A.R.toSubring (s*a) l := m.property.trans hl.symm
    obtain ⟨n, hn⟩ := Ideal.mem_span_singleton.mp (Ideal.Quotient.eq.mp hh)
    refine ⟨n, Subtype.ext ?_⟩
    change l + (s*a)*n = m.val
    rw [← hn]
    ring

theorem raw_tsum_residueCoset (A : SArithmeticData F) (s a : A.R)
    (hs : s ≠ 0) (ha : a ≠ 0) (r : FiniteTransform.Residue A.R.toSubring (s*a))
    (w : A.R → ℂ) :
    (∑' m : {m : A.R // FiniteTransform.residueMap A.R.toSubring (s*a) m = r}, w m.val) =
    ∑' n : A.R, w ((FiniteTransform.canonicalLifts A.R.toSubring (s*a)).val r + (s*a)*n) :=
  ((raw_residueCosetEquiv A s a hs ha r).tsum_eq (fun m => w m.val)).symm

theorem raw_productModule_mul (A : SArithmeticData F) (x y : F) :
    PoissonS.productModule F A.Sf (x*y) =
      PoissonS.productModule F A.Sf x * PoissonS.productModule F A.Sf y := by
  simp only [PoissonS.productModule, map_mul, mul_pow, Finset.prod_mul_distrib]
  ring

theorem raw_localUnits_point (A : SArithmeticData F) (g : A.G) :
    (raw_localUnits A g).val = NormalizedProbe.asLocalPoint A g := rfl

theorem raw_norm_mul (A : SArithmeticData F) (g h : A.G) : A.norm (g*h) = A.norm g * A.norm h := by
  simp only [SArithmeticData.norm, Prod.fst_mul, Prod.snd_mul, Pi.mul_apply,
    Units.val_mul, _root_.norm_mul, mul_pow, Finset.prod_mul_distrib]
  ring

theorem raw_residue_poisson
    (A : SArithmeticData F) (σ : F →+* ℂ)
    (η : RayClassCharacter F A.modulus) (hS : A.ContainsTraceBadPlaces)
    (P : NormalizedProbe.PrincipalData A σ η hS)
    (N : Normalization A σ η hS P)
    (s a : A.R) (hs : s ≠ 0) (ha : a ≠ 0)
    (X : ℝ) (hX : 0 < X) (t : A.G1)
    (r : FiniteTransform.Residue A.R.toSubring (s*a)) :
    (∑' m : {m : A.R // FiniteTransform.residueMap A.R.toSubring (s*a) m = r},
      P.W0 (sLocalDiagonal F A.Sf (m.val : F) * NormalizedProbe.asLocalPoint A
        (((t : A.G) * NormalizedProbe.radialSection A (modulus A s * X))⁻¹))) =
    ((X / modulus A a : ℝ) : ℂ) *
      ∑' h : A.R, P.coefficients.additiveCharacter ((h : F) *
        (((FiniteTransform.canonicalLifts A.R.toSubring (s*a)).val r) : F) /
          ((s : F)*(a : F))) *
        ProbeWeight.fourier F A.Sf P.finiteTrace P.additiveMeasure P.W0
          (frequencyPoint A s a X t h) := by
  let c : Fˣ := Units.mk0 ((s : F)*(a : F)) (mul_ne_zero (by exact_mod_cast hs) (by exact_mod_cast ha))
  let b : A.R := (FiniteTransform.canonicalLifts A.R.toSubring (s*a)).val r
  let d : (SLocalProduct F A.Sf)ˣ := raw_localUnits A
    ((t : A.G) * NormalizedProbe.radialSection A (modulus A s * X))
  have hd : PoissonS.localDilationModule F A.Sf d = modulus A s * X := by
    rw [raw_localDilationModule_eq_norm, raw_norm_mul]
    rw [show A.norm (t : A.G) = 1 from t.property, one_mul]
    rw [NormalizedProbe.radialSection, dif_pos (mul_pos (modulus_pos A P.coefficients hs) hX)]
    exact A.norm_radialSection _ _
  have hc : PoissonS.productModule F A.Sf (c : F) = modulus A s * modulus A a := by
    rw [show (c : F) = (s : F)*(a : F) from rfl, raw_productModule_mul,
      raw_productModule_eq_modulus A s hs, raw_productModule_eq_modulus A a ha]
  have hscalar : ((PoissonS.productModule F A.Sf (c : F))⁻¹ : ℂ) *
      (PoissonS.localDilationModule F A.Sf d : ℂ) = ((X / modulus A a : ℝ) : ℂ) := by
    rw [hd, hc, ← Complex.ofReal_inv, ← Complex.ofReal_mul]
    congr 1
    field_simp [(modulus_pos A P.coefficients hs).ne', (modulus_pos A P.coefficients ha).ne']
  have hp := raw_translate_dilate_poisson A σ η hS P N c (b : F) d
  rw [hscalar] at hp
  rw [raw_tsum_residueCoset A s a hs ha r (fun m => P.W0
    (sLocalDiagonal F A.Sf (m : F) * NormalizedProbe.asLocalPoint A
      (((t : A.G) * NormalizedProbe.radialSection A (modulus A s * X))⁻¹)))]
  calc
    _ = ∑' n : A.R, P.W0 (sLocalDiagonal F A.Sf ((c : F)*(n : F)+(b : F)) * d⁻¹.val) := by
      apply tsum_congr
      intro n
      have hinv : d⁻¹.val = NormalizedProbe.asLocalPoint A
        (((t : A.G) * NormalizedProbe.radialSection A (modulus A s * X))⁻¹) := rfl
      rw [hinv]
      have heq : (((FiniteTransform.canonicalLifts A.R.toSubring (s*a)).val r +
          (s*a)*n : A.R) : F) = (c : F)*(n : F)+(b : F) := by
        change (b : F) + ((s : F)*(a : F))*(n : F) = (c : F)*(n : F)+(b : F)
        dsimp [c]
        ring
      rw [heq]
    _ = _ := hp
    _ = _ := by
      congr 1
      apply tsum_congr
      intro h
      have hfreq : d.val * sLocalDiagonal F A.Sf (((c⁻¹ : Fˣ) : F)*(h : F)) =
          frequencyPoint A s a X t h := by
        rw [frequencyPoint, ← raw_localUnits_point]
        congr 2
        simp only [c, Units.val_inv_eq_inv_val, Units.val_mk0]
        rw [div_eq_mul_inv, mul_comm]
      rw [hfreq]
      congr 2
      simp only [c, Units.val_inv_eq_inv_val, Units.val_mk0]
      rw [div_eq_mul_inv]
      ring

theorem raw_principal_additiveCharacter_primitive
    (A : SArithmeticData F) (σ : F →+* ℂ)
    (η : RayClassCharacter F A.modulus) (hS : A.ContainsTraceBadPlaces)
    (P : NormalizedProbe.PrincipalData A σ η hS)
    (N : Normalization A σ η hS P)
    (s : A.R) (hs : s ≠ 0) :
    FiniteTransform.IsPrimitiveAt A.R.toSubring s P.coefficients.additiveCharacter := by
  classical
  have hfield (x : F) : P.coefficients.additiveCharacter x =
      (sLocalTraceCharacter F A.Sf (sLocalDiagonal F A.Sf x) : ℂ) := by
    rw [P.sameTrace]
    exact TateSLocalComparison.compatible_phase_eq_trace F A P.finiteTrace
      P.continuousTrace P.traceCompatible _
  intro k hk
  by_contra h
  push Not at h
  have hall : ∀ j : A.R,
      sLocalTraceCharacter F A.Sf
        (sLocalDiagonal F A.Sf ((k : F) * (j : F) / (s : F))) = 1 := by
    intro j
    apply Subtype.ext
    simpa only [hfield, Circle.coe_one] using h j
  have htest : ∀ m : sIntegerRing F A.Sf,
      sLocalTraceCharacter F A.Sf
        (sLocalDiagonal F A.Sf ((k : F) / (s : F)) * sIntegerDiagonal F A.Sf m) = 1 := by
    intro m
    rw [sIntegerDiagonal_apply, ← map_mul]
    simpa only [div_mul_eq_mul_div] using hall m
  obtain ⟨n, hn⟩ := (sInteger_trace_annihilator F A.Sf
    (fun v hv => N.containsDifferent v (Ideal.dvd_iff_le.mpr hv)) _).mp htest
  have hkn : (k : F) / (s : F) = (n : F) := by
    apply (sLocalDiagonal F A.Sf).injective
    exact hn
  apply hk
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  apply Ideal.mem_span_singleton.mpr
  refine ⟨n, ?_⟩
  apply Subtype.ext
  have hsF : (s : F) ≠ 0 := by exact_mod_cast hs
  change (k : F) = (s : F) * (n : F)
  rw [div_eq_iff hsF] at hkn
  simpa [mul_comm] using hkn

end
end DedekindZetaZeroFree.ProbeCoset
