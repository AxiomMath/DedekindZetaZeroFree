module

public import DedekindZetaZeroFree.HarmonicAnalysis.Poisson.PrincipalProbes.CosetTermsAndNormalization

@[expose] public section

namespace DedekindZetaZeroFree.ProbeCoset
noncomputable section
open scoped Classical NumberField SchwartzMap
open NumberField IsDedekindDomain MeasureTheory
variable {F : Type} [Field F] [NumberField F]

local instance (v : HeightOneSpectrum (RingOfIntegers F)) : MeasurableSpace (v.adicCompletion F) := borel _
local instance (S : Finset (HeightOneSpectrum (RingOfIntegers F))) : MeasurableSpace (SLocalProduct F S) := borel _
local instance (S : Finset (HeightOneSpectrum (RingOfIntegers F))) : BorelSpace (SLocalProduct F S) := ⟨rfl⟩
local instance (v : HeightOneSpectrum (RingOfIntegers F)) : BorelSpace (v.adicCompletion F) := ⟨rfl⟩

private theorem annular_tensor (A : SArithmeticData F) (W : SLocalProduct F A.Sf → ℂ)
    (hw : ProbeWeight.IsAnnularTensor F A.Sf W) :
    ∃ (f : 𝓢(PoissonArch.Space F, ℂ)) (φ : (v : A.Sf) → v.val.adicCompletion F → ℂ),
      (∀ v, IsLocallyConstant (φ v)) ∧ (∀ v, HasCompactSupport (φ v)) ∧
      ∀ x, W ((PoissonS.localProductToSpace F A.Sf).symm x) = PoissonS.tensorFunction F A.Sf f φ x := by
  obtain ⟨r, c, φ, hr, hc, hφ, hW⟩ := hw
  let E := mixedEmbedding.euclidean.toMixed F
  let f : PoissonArch.Space F → ℂ := fun x => (∏ v, r v ((E x).1 v)) * ∏ v, c v ((E x).2 v)
  have hs : ContDiff ℝ (⊤ : ℕ∞) f := by
    apply ContDiff.mul
    · apply contDiff_prod
      intro v hv
      exact (hr v).1.comp ((contDiff_apply ℝ ℝ v).comp (contDiff_fst.comp E.contDiff))
    · apply contDiff_prod
      intro v hv
      exact (hc v).1.comp ((contDiff_apply ℝ ℂ v).comp (contDiff_snd.comp E.contDiff))
  let K := E ⁻¹' ((Set.pi Set.univ fun v => tsupport (r v)) ×ˢ (Set.pi Set.univ fun v => tsupport (c v)))
  have hK : IsCompact K := E.toHomeomorph.isCompact_preimage.mpr
    ((isCompact_univ_pi fun v => (hr v).2.1).prod (isCompact_univ_pi fun v => (hc v).2.1))
  have ht : HasCompactSupport f := by
    apply HasCompactSupport.intro hK
    intro x hx
    by_contra hne
    have hp := mul_ne_zero_iff.mp hne
    apply hx
    constructor <;> intro v hv
    · exact subset_tsupport _ ((Finset.prod_ne_zero_iff.mp hp.1) v (Finset.mem_univ _))
    · exact subset_tsupport _ ((Finset.prod_ne_zero_iff.mp hp.2) v (Finset.mem_univ _))
  refine ⟨ht.toSchwartzMap hs, φ, fun v => (hφ v).1, fun v => (hφ v).2.1, ?_⟩
  intro x
  rw [hW]
  change _ = f x.1 * ∏ v, φ v (x.2 v)
  have he : InfiniteAdeleRing.ringEquiv_mixedSpace F ((PoissonS.localProductToSpace F A.Sf).symm x).1 = E x.1 := by
    rw [← PoissonArch.infiniteAdeleToSpace_coordinates]
    congr 1
    exact congrArg Prod.fst ((PoissonS.localProductToSpace F A.Sf).apply_symm_apply x)
  rw [he]
  rfl

private theorem trace_pair (A : SArithmeticData F) (u v : InfiniteAdeleRing F) :
    PoissonArch.tracePairing F (PoissonArch.infiniteAdeleToSpace F u) (PoissonArch.infiniteAdeleToSpace F v) =
      ∑ w : InfinitePlace F, 2 * (InfinitePlace.Completion.extensionEmbedding w (u w * v w)).re := by
  letI : IsEmpty {w : InfinitePlace F // w.IsReal} := ⟨fun w => (InfinitePlace.not_isReal_iff_isComplex.mpr (A.complex_place w)) w.property⟩
  simp only [PoissonArch.tracePairing, PoissonArch.infiniteAdeleToSpace_coordinates,
    InfiniteAdeleRing.ringEquiv_mixedSpace_apply, Finset.univ_eq_empty, Finset.sum_empty, zero_add, map_mul]
  rw [Finset.mul_sum]
  apply Fintype.sum_equiv (Equiv.subtypeUnivEquiv (fun w => A.complex_place w))
  intro w
  rfl

private theorem fourier_transport (A : SArithmeticData F)
    (e : (v : A.Sf) → AddChar (v.val.adicCompletion F) Circle)
    (μ : (v : A.Sf) → Measure (v.val.adicCompletion F))
    (W : SLocalProduct F A.Sf → ℂ) (y : SLocalProduct F A.Sf) :
    ProbeWeight.fourier F A.Sf e
      (Measure.map (PoissonS.localProductToSpace F A.Sf).symm (PoissonS.productMeasure F A.Sf μ)) W y =
    PoissonS.fourierIntegral F A.Sf e μ (fun x => W ((PoissonS.localProductToSpace F A.Sf).symm x))
      (PoissonS.localProductToSpace F A.Sf y) := by
  let E : SLocalProduct F A.Sf ≃ₜ PoissonS.Space F A.Sf := (PoissonArch.infiniteAdeleToSpace F).toHomeomorph.prodCongr (Homeomorph.refl _)
  rw [ProbeWeight.fourier]
  change (∫ x, W x * ProbeAdditive.phase F A.Sf e (-x * y) ∂Measure.map E.symm _) = _
  rw [show (E.symm : PoissonS.Space F A.Sf → SLocalProduct F A.Sf) = E.symm.toMeasurableEquiv from rfl,
    integral_map_equiv E.symm.toMeasurableEquiv]
  unfold PoissonS.fourierIntegral
  apply integral_congr_ae
  filter_upwards [] with x
  unfold ProbeAdditive.phase ProbeAdditive.archPhase
  have ht := trace_pair A (- (E.symm x).1) y.1
  have hx : PoissonArch.infiniteAdeleToSpace F (E.symm x).1 = x.1 := by
    exact congrArg Prod.fst (E.apply_symm_apply x)
  have hy : (PoissonS.localProductToSpace F A.Sf y).1 = PoissonArch.infiniteAdeleToSpace F y.1 := rfl
  rw [map_neg, hx, PoissonArch.tracePairing_eq_inner, inner_neg_left, ← PoissonArch.tracePairing_eq_inner] at ht
  simp only [show (2 : ℂ) = ((2 : ℝ) : ℂ) from rfl, ← Complex.ofReal_mul, ← Complex.ofReal_sum]
  change W (E.symm x) * (Complex.exp (((2 * Real.pi : ℝ) : ℂ) * Complex.I *
    ((∑ w : InfinitePlace F, 2 * (InfinitePlace.Completion.extensionEmbedding w
      ((-(E.symm x).1) w * y.1 w)).re : ℝ) : ℂ)) * ∏ v, (e v (-x.2 v * y.2 v) : ℂ)) = _
  rw [← ht]
  simp only [hy, Complex.ofReal_neg]
  rw [← mul_assoc]
  congr 1
  congr 1
  congr 1
  push_cast
  ring

theorem raw_fourier_norm_summable
    (A : SArithmeticData F) (σ : F →+* ℂ)
    (η : RayClassCharacter F A.modulus) (hS : A.ContainsTraceBadPlaces)
    (P : NormalizedProbe.PrincipalData A σ η hS)
    (N : Normalization A σ η hS P)
    (s a : A.R) (hs : s ≠ 0) (ha : a ≠ 0)
    (X : ℝ) (hX : 0 < X) (t : A.G1) :
    Summable (fun h : A.R =>
      ‖ProbeWeight.fourier F A.Sf P.finiteTrace P.additiveMeasure P.W0
        (frequencyPoint A s a X t h)‖) := by
  letI : ∀ v, (N.localMeasure v).IsAddHaarMeasure := N.localHaar
  obtain ⟨f, φ, hl, hc, hW⟩ := annular_tensor A P.W0 P.annular
  let d0 : A.G := (t : A.G) * NormalizedProbe.radialSection A (modulus A s * X)
  let d : (SLocalProduct F A.Sf)ˣ :=
    ((MulEquiv.piUnits).symm.prodCongr (MulEquiv.piUnits).symm).trans
      (MulEquiv.prodUnits).symm d0
  have hd : d.val = NormalizedProbe.asLocalPoint A d0 := rfl
  obtain ⟨g, ψ, hg, hψ, hψl, hψc, hfun⟩ :=
    PoissonS.tensorFunction_local_dilation_bruhatSchwartz F A.Sf f φ hl hc d
  have hp : (s : F) * (a : F) ≠ 0 := mul_ne_zero (by exact_mod_cast hs) (by exact_mod_cast ha)
  have hsum := PoissonS.summable_norm_fourierIntegral_tensorFunction_lattice F A.Sf
    P.finiteTrace N.localMeasure P.continuousTrace
    (PoissonS.ScaleShift.traceConductor_nontrivial F A.Sf P.finiteTrace N.traceConductor)
    g ψ hψl hψc ((s : F) * (a : F)) hp
  let i : A.R → PoissonS.lattice F A.Sf ((s : F) * (a : F))⁻¹ := fun h =>
    ⟨PoissonS.diagonalHom F A.Sf (((s : F) * (a : F))⁻¹ * (h : F)), by
      exact AddSubgroup.mem_map.mpr ⟨(h : F), h.property, rfl⟩⟩
  have hi : Function.Injective i := by
    intro x y hxy
    have he := congrArg (fun z : PoissonS.lattice F A.Sf ((s : F) * (a : F))⁻¹ =>
      mixedEmbedding.euclidean.toMixed F z.val.1) hxy
    change mixedEmbedding F (((s : F) * (a : F))⁻¹ * (x : F)) =
      mixedEmbedding F (((s : F) * (a : F))⁻¹ * (y : F)) at he
    rw [InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp, InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp] at he
    have he' := (algebraMap F (InfiniteAdeleRing F)).injective
      ((InfiniteAdeleRing.ringEquiv_mixedSpace F).injective he)
    apply Subtype.ext
    exact mul_left_cancel₀ (inv_ne_zero hp) he'
  have hsum' := hsum.comp_injective hi
  have hscale (h : A.R) :
      PoissonS.fourierIntegral F A.Sf P.finiteTrace N.localMeasure (PoissonS.tensorFunction F A.Sf g ψ) (i h) =
        (PoissonS.localDilationModule F A.Sf d : ℂ) *
        ProbeWeight.fourier F A.Sf P.finiteTrace P.additiveMeasure P.W0 (frequencyPoint A s a X t h) := by
    rw [← show (fun x => PoissonS.tensorFunction F A.Sf f φ (PoissonS.localDilation F A.Sf d⁻¹ x)) =
      PoissonS.tensorFunction F A.Sf g ψ from funext hfun]
    rw [PoissonS.fourierIntegral_local_dilation F A.Sf P.finiteTrace N.localMeasure P.continuousTrace f φ hl hc d]
    congr 1
    rw [N.sameMeasure, fourier_transport]
    simp_rw [hW]
    congr 1
    apply (PoissonS.localProductToSpace F A.Sf).symm.injective
    simp only [PoissonS.localDilation, AddEquiv.symm_apply_apply]
    rw [hd]
    congr 1
    change (PoissonS.localProductToSpace F A.Sf).symm
      (PoissonS.diagonalHom F A.Sf (((s : F) * (a : F))⁻¹ * (h : F))) =
      sLocalDiagonal F A.Sf ((h : F) / ((s : F) * (a : F)))
    have he : PoissonS.localProductToSpace F A.Sf (sLocalDiagonal F A.Sf ((h : F) / ((s : F) * (a : F)))) =
      PoissonS.diagonalHom F A.Sf (((s : F) * (a : F))⁻¹ * (h : F)) := by
      rw [div_eq_mul_inv, mul_comm (h : F)]
      apply Prod.ext
      · apply (mixedEmbedding.euclidean.toMixed F).injective
        change (mixedEmbedding.euclidean.toMixed F)
          (PoissonArch.infiniteAdeleToSpace F (algebraMap F (InfiniteAdeleRing F) _)) =
            (mixedEmbedding.euclidean.toMixed F) ((mixedEmbedding.euclidean.toMixed F).symm _)
        rw [PoissonArch.infiniteAdeleToSpace_coordinates, ContinuousLinearEquiv.apply_symm_apply]
        exact (InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp (K := F)).symm
      · rfl
    exact (PoissonS.localProductToSpace F A.Sf).symm_apply_eq.mpr he.symm
  have hpos : 0 < PoissonS.localDilationModule F A.Sf d := by
    unfold PoissonS.localDilationModule
    apply mul_pos
    · rw [InfiniteAdeleRing.norm_def]
      apply Finset.prod_pos
      intro v hv
      exact pow_pos (norm_pos_iff.mpr (Units.ne_zero ((Units.map (Pi.evalRingHom _ v).toMonoidHom)
        ((Units.map (RingHom.fst _ _).toMonoidHom) d)))) _
    · apply Finset.prod_pos
      intro v hv
      let dv : (v.val.adicCompletion F)ˣ := Units.map
        ((Pi.evalRingHom _ v).comp (RingHom.snd _ _)).toMonoidHom d
      exact norm_pos_iff.mpr (show (d.val.2 v) ≠ 0 from Units.ne_zero dv)
  simp only [Function.comp_def, hscale, norm_mul] at hsum'
  exact (summable_mul_left_iff (norm_ne_zero_iff.mpr (Complex.ofReal_ne_zero.mpr hpos.ne'))).mp hsum'

end
end DedekindZetaZeroFree.ProbeCoset
