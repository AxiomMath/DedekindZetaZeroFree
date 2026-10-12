module

public import DedekindZetaZeroFree.Metaplectic.Kubota.LocalCoverChartTopology
public import DedekindZetaZeroFree.Metaplectic.Kubota.TameCompact.CorrectionAndDeterminantTwist

@[expose] public section

open scoped NumberField
open NumberField IsDedekindDomain

namespace DedekindZetaZeroFree.KPScalarSplitCentral

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000

variable (F : Type) [Field F] [NumberField F]
variable (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (v : KPHilbert.Place F)

abbrev scalarMatrix : (KPHilbert.Completion F v)ˣ →* KPLocalCover.LocalGL2 F v :=
  Matrix.GeneralLinearGroup.scalar (Fin 2)

def scalarLift (z : (KPHilbert.Completion F v)ˣ) :
    KPLocalCover.CubicGL2Raw F ζ hζ v :=
  KPLocalCover.sectionMap F ζ hζ v (scalarMatrix F v z)

private theorem X_scalar (z : (KPHilbert.Completion F v)ˣ) :
    KubotaRankTwo.X (KPHilbert.Completion F v) (scalarMatrix F v z) = z := by
  apply Units.ext
  simp [KubotaRankTwo.X, KubotaRankTwo.x, scalarMatrix, Matrix.scalar]

private theorem X_scalar_mul (z : (KPHilbert.Completion F v)ˣ)
    (g : KPLocalCover.LocalGL2 F v) :
    KubotaRankTwo.X (KPHilbert.Completion F v) (scalarMatrix F v z * g) =
      z * KubotaRankTwo.X (KPHilbert.Completion F v) g := by
  classical
  apply Units.ext
  simp only [KubotaRankTwo.X, Units.val_mk0, Units.val_mul]
  unfold KubotaRankTwo.x
  have he (i j : Fin 2) : (scalarMatrix F v z * g) i j = (z : KPHilbert.Completion F v) * g i j := by
    fin_cases i <;> fin_cases j <;> simp [scalarMatrix, Matrix.mul_apply, Matrix.scalar]
  rw [he 1 0, he 1 1]
  simp only [mul_eq_zero, z.ne_zero, false_or]
  split_ifs <;> rfl

private theorem X_mul_scalar (z : (KPHilbert.Completion F v)ˣ)
    (g : KPLocalCover.LocalGL2 F v) :
    KubotaRankTwo.X (KPHilbert.Completion F v) (g * scalarMatrix F v z) =
      z * KubotaRankTwo.X (KPHilbert.Completion F v) g := by
  rw [← Matrix.GeneralLinearGroup.scalar_commute, X_scalar_mul]

private theorem B3_ninth (a b : (KPHilbert.Completion F v)ˣ) :
    KPHilbert.B3 F ζ hζ v a b ^ 9 = 1 := by
  apply Subtype.ext
  change (KPHilbert.B3 F ζ hζ v a b : Fˣ) ^ 9 = 1
  rw [show (9 : ℕ) = 3 * 3 from rfl, pow_mul,
    (KPHilbert.B3 F ζ hζ v a b).property, one_pow]

theorem sigmaTwo_scalar_scalar (z z' : (KPHilbert.Completion F v)ˣ) :
    KPLocalCover.sigmaTwo F ζ hζ v (scalarMatrix F v z) (scalarMatrix F v z') =
      KPHilbert.B3 F ζ hζ v z z' ^ 9 := by
  let B := KPHilbert.B3 F ζ hζ v
  obtain ⟨hL, hR, hsk, _, _, ha⟩ := KPHilbert.B3_laws F ζ hζ v
  let BL (b : (KPHilbert.Completion F v)ˣ) : (KPHilbert.Completion F v)ˣ →* rootsOfUnity 3 F :=
    { toFun := fun a => B a b
      map_one' := KubotaDefectSymbolAlgebra.one_left _ _ B hL b
      map_mul' := fun a a' => hL a a' b }
  let BR (a : (KPHilbert.Completion F v)ˣ) : (KPHilbert.Completion F v)ˣ →* rootsOfUnity 3 F :=
    { toFun := B a
      map_one' := KubotaDefectSymbolAlgebra.one_right _ _ B hR a
      map_mul' := hR a }
  have hp (a b : (KPHilbert.Completion F v)ˣ) : B (a ^ 2) (b ^ 2) = B a b ^ 4 := by
    change BL (b ^ 2) (a ^ 2) = _
    rw [map_pow]
    change (BR a (b ^ 2)) ^ 2 = _
    rw [map_pow, ← pow_mul]
    norm_num
    rfl
  have hi : B z' z⁻¹ = B z z' := by
    change BR z' z⁻¹ = _
    rw [map_inv]
    exact (hsk z z').symm
  simp only [KPLocalCover.sigmaTwo, KubotaElementaryLastArgument.tau,
    ← map_mul, X_scalar, KubotaRankTwo.det, Matrix.GeneralLinearGroup.det_scalar,
    Fintype.card_fin]
  rw [show z * z' / z = z' from by simp [mul_comm],
    show z * z' / (z' * z ^ 2) = z⁻¹ from by
      apply Units.ext
      simp only [Units.val_div_eq_div_val, Units.val_mul, Units.val_pow_eq_pow_val,
        Units.val_inv_eq_inv_val]
      field_simp]
  change B z' z⁻¹ * B (z ^ 2) (z' ^ 2) ^ 2 = _
  rw [hi, hp, ← pow_mul]
  simpa only [pow_one] using (pow_add (B z z') 1 8).symm

theorem sigmaTwo_scalar_scalar_eq_one (z z' : (KPHilbert.Completion F v)ˣ) :
    KPLocalCover.sigmaTwo F ζ hζ v (scalarMatrix F v z) (scalarMatrix F v z') = 1 := by
  rw [sigmaTwo_scalar_scalar F ζ hζ v z z']
  exact B3_ninth F ζ hζ v z z'

theorem sigmaTwo_scalar_commutator (z : (KPHilbert.Completion F v)ˣ)
    (g : KPLocalCover.LocalGL2 F v) :
    KPLocalCover.sigmaTwo F ζ hζ v (scalarMatrix F v z) g /
        KPLocalCover.sigmaTwo F ζ hζ v g (scalarMatrix F v z) =
      KPHilbert.B3 F ζ hζ v z (Matrix.GeneralLinearGroup.det g) ^ 9 := by
  let K := KPHilbert.Completion F v
  let B := KPHilbert.B3 F ζ hζ v
  obtain ⟨hL, hR, hsk, _, _, ha⟩ := KPHilbert.B3_laws F ζ hζ v
  have hi := KubotaDefectSymbolAlgebra.inv_right K (rootsOfUnity 3 F) B hR
  have hd := KubotaDefectSymbolAlgebra.div_right K (rootsOfUnity 3 F) B hR
  have hpL (a b : Kˣ) : B (a ^ 2) b = B a b ^ 2 := by
    simpa only [pow_two] using hL a a b
  have hpR (a b : Kˣ) : B a (b ^ 2) = B a b ^ 2 := by
    simpa only [pow_two] using hR a b b
  simp only [KPLocalCover.sigmaTwo, KubotaElementaryLastArgument.tau,
    X_scalar_mul, X_mul_scalar, X_scalar, KubotaRankTwo.det,
    Matrix.GeneralLinearGroup.det_scalar, Fintype.card_fin]
  rw [show z * KubotaRankTwo.X K g / z = KubotaRankTwo.X K g from by simp [mul_comm],
    show z * KubotaRankTwo.X K g / (KubotaRankTwo.X K g * z ^ 2) = z⁻¹ from by
      apply Units.ext
      simp only [Units.val_div_eq_div_val, Units.val_mul, Units.val_pow_eq_pow_val,
        Units.val_inv_eq_inv_val]
      field_simp,
    show z * KubotaRankTwo.X K g / KubotaRankTwo.X K g = z from by simp,
    show z * KubotaRankTwo.X K g / (z * Matrix.GeneralLinearGroup.det g) =
      KubotaRankTwo.X K g / Matrix.GeneralLinearGroup.det g from by
        apply Units.ext
        simp only [Units.val_div_eq_div_val, Units.val_mul]
        field_simp]
  change B (KubotaRankTwo.X K g) z⁻¹ * B (z ^ 2) (Matrix.GeneralLinearGroup.det g) ^ 2 /
    (B z (KubotaRankTwo.X K g / Matrix.GeneralLinearGroup.det g) *
      B (Matrix.GeneralLinearGroup.det g) (z ^ 2) ^ 2) = _
  rw [hi, hd, hpL, hpR]
  have hs (a b : Kˣ) : B a b = (B b a)⁻¹ := hsk a b
  rw [hs (KubotaRankTwo.X K g) z, hs (Matrix.GeneralLinearGroup.det g) z]
  simp only [inv_inv, ← pow_mul, show 2 * 2 = (4 : ℕ) by norm_num]
  apply Subtype.ext
  apply Units.ext
  simp only [Subgroup.coe_div, Subgroup.coe_mul, Subgroup.coe_pow, Subgroup.coe_inv,
    Units.val_div_eq_div_val, Units.val_mul,
    Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val]
  field_simp
  rfl

theorem sigmaTwo_scalar_commutator_eq_one (z : (KPHilbert.Completion F v)ˣ)
    (g : KPLocalCover.LocalGL2 F v) :
    KPLocalCover.sigmaTwo F ζ hζ v (scalarMatrix F v z) g /
        KPLocalCover.sigmaTwo F ζ hζ v g (scalarMatrix F v z) = 1 := by
  rw [sigmaTwo_scalar_commutator F ζ hζ v z g]
  exact B3_ninth F ζ hζ v z _

theorem scalarLift_one : scalarLift F ζ hζ v 1 = 1 := by
  change KPLocalCover.CubicGL2Raw.mk (scalarMatrix F v 1) 1 = _
  rw [map_one]
  rfl

theorem scalarLift_mul (z z' : (KPHilbert.Completion F v)ˣ) :
    scalarLift F ζ hζ v (z * z') = scalarLift F ζ hζ v z * scalarLift F ζ hζ v z' := by
  change KPLocalCover.CubicGL2Raw.mk (scalarMatrix F v (z * z')) 1 =
    KPLocalCover.CubicGL2Raw.mk (scalarMatrix F v z * scalarMatrix F v z')
      (1 * 1 * KPLocalCover.sigmaTwo F ζ hζ v (scalarMatrix F v z) (scalarMatrix F v z'))
  rw [map_mul, sigmaTwo_scalar_scalar_eq_one F ζ hζ v z z']
  simp

def scalarHom : (KPHilbert.Completion F v)ˣ →* KPLocalCover.CubicGL2Raw F ζ hζ v where
  toFun := scalarLift F ζ hζ v
  map_one' := scalarLift_one F ζ hζ v
  map_mul' := scalarLift_mul F ζ hζ v

theorem projection_scalarHom (z : (KPHilbert.Completion F v)ˣ) :
    KPLocalCover.projection F ζ hζ v (scalarHom F ζ hζ v z) = scalarMatrix F v z := by
  rfl

theorem scalarHom_range_le_center :
    (scalarHom F ζ hζ v).range ≤ Subgroup.center (KPLocalCover.CubicGL2Raw F ζ hζ v) := by
  rintro x ⟨z, rfl⟩
  rw [Subgroup.mem_center_iff]
  intro y
  have hs := div_eq_one.mp (sigmaTwo_scalar_commutator_eq_one F ζ hζ v z y.g)
  change KPLocalCover.CubicGL2Raw.mk (y.g * scalarMatrix F v z)
    (y.epsilon * 1 * KPLocalCover.sigmaTwo F ζ hζ v y.g (scalarMatrix F v z)) =
      KPLocalCover.CubicGL2Raw.mk (scalarMatrix F v z * y.g)
        (1 * y.epsilon * KPLocalCover.sigmaTwo F ζ hζ v (scalarMatrix F v z) y.g)
  rw [Matrix.GeneralLinearGroup.scalar_commute, hs]
  simp

private theorem scalar_continuous (K : Type*) [Field K] [TopologicalSpace K]
    [IsTopologicalRing K] : Continuous (Matrix.GeneralLinearGroup.scalar (Fin 2) (R := K)) := by
  apply Units.continuous_iff.mpr
  constructor
  · apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    by_cases h : i = j
    · simpa [Matrix.scalar, Matrix.diagonal_apply, h] using (Units.continuous_val : Continuous (fun z : Kˣ => (z : K)))
    · simpa [Matrix.scalar, Matrix.diagonal_apply, h] using (continuous_const : Continuous (fun _ : Kˣ => (0 : K)))
  · change Continuous (fun z : Kˣ => ((Matrix.GeneralLinearGroup.scalar (Fin 2) z)⁻¹).val)
    have hinv (z : Kˣ) : (Matrix.GeneralLinearGroup.scalar (Fin 2) z)⁻¹ =
        Matrix.GeneralLinearGroup.scalar (Fin 2) z⁻¹ := (Matrix.GeneralLinearGroup.scalar (Fin 2)).map_inv z |>.symm
    simp_rw [hinv]
    change Continuous (fun z : Kˣ => Matrix.scalar (Fin 2) ((z⁻¹ : Kˣ) : K))
    apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    by_cases h : i = j
    · simpa [Matrix.scalar, Matrix.diagonal_apply, h] using (Units.continuous_coe_inv : Continuous (fun z : Kˣ => (z⁻¹ : Kˣ).val))
    · simpa [Matrix.scalar, Matrix.diagonal_apply, h] using (continuous_const : Continuous (fun _ : Kˣ => (0 : K)))

private theorem scalar_range_closed (K : Type*) [Field K] [TopologicalSpace K]
    [IsTopologicalRing K] [T2Space K] :
    IsClosed (Set.range (Matrix.GeneralLinearGroup.scalar (Fin 2) (R := K))) := by
  have he : Set.range (Matrix.GeneralLinearGroup.scalar (Fin 2) (R := K)) =
      {g | g 0 1 = 0 ∧ g 1 0 = 0 ∧ g 0 0 = g 1 1} := by
    ext g
    constructor
    · rintro ⟨z, rfl⟩
      simp [Matrix.scalar]
    · rintro ⟨h01, h10, hdiag⟩
      have hn : g 0 0 ≠ 0 := by
        intro h
        have hd := Matrix.GeneralLinearGroup.det_ne_zero g
        simp [Matrix.det_fin_two, h, h01, h10] at hd
      refine ⟨Units.mk0 (g 0 0) hn, ?_⟩
      apply Matrix.GeneralLinearGroup.ext
      intro i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.scalar, h01, h10, hdiag]
  rw [he]
  have hc (i j : Fin 2) : Continuous (fun g : Matrix.GeneralLinearGroup (Fin 2) K => g i j) := by
    have hv : Continuous (fun g : Matrix.GeneralLinearGroup (Fin 2) K => (g : Matrix (Fin 2) (Fin 2) K)) := Units.continuous_val
    exact (continuous_apply j).comp ((continuous_apply i).comp hv)
  exact (isClosed_eq (hc 0 1) continuous_const).inter
    ((isClosed_eq (hc 1 0) continuous_const).inter (isClosed_eq (hc 0 0) (hc 1 1)))

theorem finite_continuous_closed (w : HeightOneSpectrum (𝓞 F)) (m : ℕ)
    (hm : KPLocalChartTopology.MatrixChartDepth F w m) :
    letI := KPLocalChartTopology.translatedTopology F ζ hζ w m
    Continuous (scalarHom F ζ hζ (Sum.inr w)) ∧
      IsClosed (Set.range (scalarHom F ζ hζ (Sum.inr w))) := by
  letI := KPLocalChartTopology.translatedTopology F ζ hζ w m
  have ht := KPLocalChartTopology.finite_topological_group F ζ hζ w m hm
  letI := ht.1
  letI := ht.2.2
  have hs : Continuous (scalarMatrix F (Sum.inr w)) :=
    scalar_continuous (KPHilbert.Completion F (Sum.inr w))
  have hopen := (KPLocalCube.Gamma_compact_open F w m hm.1).2
  let U := scalarMatrix F (Sum.inr w) ⁻¹' (KPLocalCube.Gamma F w m : Set (KPLocalCover.LocalGL2 F (Sum.inr w)))
  have hU : IsOpen U := hopen.preimage hs
  have h1 : (1 : (KPHilbert.Completion F (Sum.inr w))ˣ) ∈ U := by
    change scalarMatrix F (Sum.inr w) 1 ∈ KPLocalCube.Gamma F w m
    rw [map_one]
    exact (KPLocalCube.Gamma F w m).one_mem
  have hchart := KPLocalChartTopology.translatedChart_isOpenEmbedding F ζ hζ w m hm 1
  have hres : Continuous (U.domRestrict (scalarHom F ζ hζ (Sum.inr w))) := by
    have hk : Continuous (fun z : U => (⟨scalarMatrix F (Sum.inr w) z.val, z.property⟩ : KPLocalCube.Gamma F w m)) :=
      (hs.comp continuous_subtype_val).subtype_mk _
    convert hchart.continuous.comp hk using 1
    ext z
    simp [KPLocalChartTopology.translatedChart, scalarHom, scalarLift]
  have hcont : Continuous (scalarHom F ζ hζ (Sum.inr w)) := by
    apply continuous_of_continuousAt_one
    apply ContinuousWithinAt.continuousAt _ (hU.mem_nhds h1)
    exact (continuousWithinAt_iff_continuousAt_domRestrict _ h1).mpr (hres.continuousAt)
  refine ⟨hcont, ?_⟩
  have hh := KPLocalChartTopology.translatedChart_homeomorphism F ζ hζ w m hm 1
  obtain ⟨e, he⟩ := hh.2
  let R := (scalarHom F ζ hζ (Sum.inr w)).range
  apply R.isClosed_of_isLocallyClosedAt (x := 1) R.one_mem
  apply isLocallyClosedAt_iff_exists_isClosed_preimage_val.mpr
  refine ⟨Set.range (KPLocalChartTopology.translatedChart F ζ hζ w m 1), hh.1.mem_nhds ?_, ?_⟩
  · refine ⟨1, ?_⟩
    simp [KPLocalChartTopology.translatedChart, KPLocalCover.sectionMap]
    rfl
  · have hp : (fun k : KPLocalCube.Gamma F w m => (e k).val) ⁻¹' (R : Set _) =
        Subtype.val ⁻¹' Set.range (scalarMatrix F (Sum.inr w)) := by
      ext k
      change (e k).val ∈ R ↔ k.val ∈ Set.range (scalarMatrix F (Sum.inr w))
      rw [he]
      simp only [KPLocalChartTopology.translatedChart, one_mul]
      constructor
      · rintro ⟨z, hz⟩
        exact ⟨z, congrArg (KPLocalCover.projection F ζ hζ (Sum.inr w)) hz⟩
      · rintro ⟨z, hz⟩
        refine ⟨z, ?_⟩
        change KPLocalCover.sectionMap F ζ hζ (Sum.inr w) (scalarMatrix F (Sum.inr w) z) = _
        rw [hz]
    have hc := (scalar_range_closed (KPHilbert.Completion F (Sum.inr w))).preimage
      (continuous_subtype_val : Continuous (Subtype.val : KPLocalCube.Gamma F w m → _))
    rw [← hp] at hc
    have himage : e '' ((fun k : KPLocalCube.Gamma F w m => (e k).val) ⁻¹' (R : Set _)) =
        Subtype.val ⁻¹' (R : Set _) := by
      ext x
      constructor
      · rintro ⟨k, hk, rfl⟩
        exact hk
      · intro hx
        refine ⟨e.symm x, ?_, e.apply_symm_apply x⟩
        simpa using hx
    rw [← himage]
    exact e.isClosedMap _ hc

theorem complex_continuous_closed (w : InfinitePlace F) :
    letI := KPLocalChartTopology.complexTopology F ζ hζ w
    Continuous (scalarHom F ζ hζ (Sum.inl w)) ∧
      IsClosed (Set.range (scalarHom F ζ hζ (Sum.inl w))) := by
  letI := KPLocalChartTopology.complexTopology F ζ hζ w
  letI : TopologicalSpace (rootsOfUnity 3 F) := ⊥
  letI : DiscreteTopology (rootsOfUnity 3 F) := ⟨rfl⟩
  have hs : Continuous (scalarMatrix F (Sum.inl w)) :=
    scalar_continuous (KPHilbert.Completion F (Sum.inl w))
  have hc : Continuous (KPLocalChartTopology.complexCoordinates F ζ hζ w) :=
    continuous_induced_dom
  constructor
  · apply continuous_induced_rng.mpr
    change Continuous (fun z : (KPHilbert.Completion F (Sum.inl w))ˣ =>
      (scalarMatrix F (Sum.inl w) z, (1 : rootsOfUnity 3 F)))
    exact hs.prodMk continuous_const
  · have hset : Set.range (scalarHom F ζ hζ (Sum.inl w)) =
        (KPLocalChartTopology.complexCoordinates F ζ hζ w) ⁻¹'
          (Set.range (scalarMatrix F (Sum.inl w)) ×ˢ {(1 : rootsOfUnity 3 F)}) := by
      ext x
      constructor
      · rintro ⟨z, rfl⟩
        exact ⟨⟨z, rfl⟩, rfl⟩
      · rintro ⟨⟨z, hg⟩, he⟩
        refine ⟨z, ?_⟩
        cases x with
        | mk g ε =>
          dsimp [KPLocalChartTopology.complexCoordinates] at hg he
          subst g
          subst ε
          rfl
    rw [hset]
    exact ((scalar_range_closed (KPHilbert.Completion F (Sum.inl w))).prod
      (isClosed_discrete {1})).preimage hc

theorem good_compact_unit_scalar (w : HeightOneSpectrum (𝓞 F))
    (hw : ringChar (KPTameCompact.O F w ⧸ KPTameCompact.p F w) ≠ 3)
    (u : (KPTameCompact.O F w)ˣ) :
    scalarHom F ζ hζ (Sum.inr w) (KPTameCompact.unitInclusion F w u) =
      KPLocalCover.CubicGL2Raw.mk
        (KPTameCompact.inclusion F w (Matrix.GeneralLinearGroup.scalar (Fin 2) u))
        (KPTameCompact.kappa F w ζ hζ (Matrix.GeneralLinearGroup.scalar (Fin 2) u)) := by
  have hk := KPTameCompact.kappa_zero F w ζ hζ (Matrix.GeneralLinearGroup.scalar (Fin 2) u) (by simp [KPTameCompact.c, Matrix.scalar])
  rw [hk]
  change KPLocalCover.CubicGL2Raw.mk _ 1 = KPLocalCover.CubicGL2Raw.mk _ 1
  congr 1
  exact (Matrix.GeneralLinearGroup.map_scalar (KPTameCompact.O F w).subtype u).symm

end
end DedekindZetaZeroFree.KPScalarSplitCentral
