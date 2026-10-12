module

public import DedekindZetaZeroFree.Adeles.Quotients.PGL2CuspParabolicStabilizers
public import DedekindZetaZeroFree.Adeles.Quotients.NormalizedCuspHeightsAndHoroballSeparation

@[expose] public section

noncomputable section

open scoped Classical nonZeroDivisors

open Module

namespace DedekindZetaZeroFree

namespace KPCuspLogShape

abbrev dimension (F : Type*) [Field F] [NumberField F] :=
  NumberField.InfinitePlace.nrComplexPlaces F

end KPCuspLogShape

end DedekindZetaZeroFree

end

section

noncomputable section
open scoped Classical nonZeroDivisors
open Module

namespace DedekindZetaZeroFree
namespace KPCuspLogShape

def sumCoordinates (d : ℕ) : (Fin d → ℝ) →ₗ[ℝ] ℝ where
  toFun b := ∑ i, b i
  map_add' b c := by simp [Finset.sum_add_distrib]
  map_smul' a b := by simp [Finset.mul_sum]

def hyperplane (d : ℕ) : Submodule ℝ (Fin d → ℝ) :=
  (sumCoordinates d).ker

def logRatio (F : Type*) [Field F] [NumberField F] (E : Subgroup Fˣ) :
    Additive E →+ (Fin (dimension F) → ℝ) where
  toFun u := fun i => Real.log ((KPCusp.complexPlace F i) ((u.toMul : Fˣ) : F))
  map_zero' := by ext i; simp
  map_add' u v := by
    ext i
    simp only [toMul_add, Subgroup.coe_mul, Units.val_mul, map_mul, Pi.add_apply]
    exact Real.log_mul ((map_ne_zero _).mpr (Units.ne_zero _))
      ((map_ne_zero _).mpr (Units.ne_zero _))

def meanHeight (d : ℕ) (z : KPArch.Space d) : ℝ :=
  (∑ i, (z i).2) / (d : ℝ)

def shapeCoordinates (d : ℕ) (z : KPArch.Space d) : Fin d → ℝ :=
  fun i => (z i).2 - meanHeight d z

def ratioAction (F : Type*) [Field F] [NumberField F] (E : Subgroup Fˣ)
    (u : E) (z : KPArch.Space (dimension F)) : KPArch.Space (dimension F) :=
  fun i => ((KPCusp.complexPlace F i).embedding ((u : Fˣ) : F) * (z i).1,
    (z i).2 + logRatio F E (Additive.ofMul u) i)

theorem logRatio_mem_hyperplane
    (F : Type*) [Field F] [NumberField F]
    (hF : NumberField.InfinitePlace.nrRealPlaces F = 0)
    (E : Subgroup Fˣ) (hE : E ≤ KPCuspArithmetic.rationalUnits F)
    (u : Additive E) :
    logRatio F E u ∈ hyperplane (dimension F) := by
  rw [hyperplane, LinearMap.mem_ker]
  show ∑ i : Fin (dimension F),
    Real.log ((KPCusp.complexPlace F i) ((u.toMul : Fˣ) : F)) = 0
  obtain ⟨x, hx⟩ := hE (u.toMul).property
  have hxu : ((x : NumberField.RingOfIntegers F) : F) = ((u.toMul : Fˣ) : F) := by
    have h := congrArg (fun w : Fˣ => (w : F)) hx
    rw [Units.coe_map] at h
    simpa using h
  have hprod := NumberField.Units.sum_mult_mul_log x
  rw [NumberField.InfinitePlace.sum_eq_sum_add_sum] at hprod
  haveI : IsEmpty {w : NumberField.InfinitePlace F // NumberField.InfinitePlace.IsReal w} :=
    Fintype.card_eq_zero_iff.mp hF
  have hreal : (∑ w : {w : NumberField.InfinitePlace F //
        NumberField.InfinitePlace.IsReal w},
      w.1.mult * Real.log (w.1 (algebraMap (NumberField.RingOfIntegers F) F
        (x : NumberField.RingOfIntegers F)))) = 0 := by
    rw [Finset.univ_eq_empty, Finset.sum_empty]
  rw [hreal, zero_add] at hprod
  have h1 : 2 * (∑ w : {w : NumberField.InfinitePlace F //
        NumberField.InfinitePlace.IsComplex w},
        Real.log (w.1 (algebraMap (NumberField.RingOfIntegers F) F
          (x : NumberField.RingOfIntegers F))))
      = ∑ w : {w : NumberField.InfinitePlace F //
          NumberField.InfinitePlace.IsComplex w},
          w.1.mult * Real.log (w.1 (algebraMap (NumberField.RingOfIntegers F) F
            (x : NumberField.RingOfIntegers F))) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun w _ => ?_)
    rw [NumberField.InfinitePlace.IsComplex.mult_eq_two w.property]
    norm_num
  have h2 : (∑ w : {w : NumberField.InfinitePlace F //
        NumberField.InfinitePlace.IsComplex w},
        Real.log (w.1 (algebraMap (NumberField.RingOfIntegers F) F
          (x : NumberField.RingOfIntegers F))))
      = ∑ i : Fin (dimension F),
          Real.log ((KPCusp.complexPlace F i) ((u.toMul : Fˣ) : F)) := by
    rw [← Equiv.sum_comp (Fintype.equivFin {w : NumberField.InfinitePlace F //
        NumberField.InfinitePlace.IsComplex w}).symm
        (fun w => Real.log (w.1 (algebraMap (NumberField.RingOfIntegers F) F
          (x : NumberField.RingOfIntegers F))))]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [← NumberField.RingOfIntegers.coe_eq_algebraMap, hxu]
    rfl
  have h2' : 2 * (∑ i : Fin (dimension F),
      Real.log ((KPCusp.complexPlace F i) ((u.toMul : Fˣ) : F))) = 0 := by
    rw [← h2, h1]
    exact hprod
  rcases mul_eq_zero.mp h2' with h | h
  · exact absurd h (by norm_num)
  · exact h

def logarithm (F : Type*) [Field F] [NumberField F]
    (hF : NumberField.InfinitePlace.nrRealPlaces F = 0)
    (E : Subgroup Fˣ) (hE : E ≤ KPCuspArithmetic.rationalUnits F) :
    Additive E →+ hyperplane (dimension F) :=
  (logRatio F E).codRestrict (hyperplane (dimension F)).toAddSubgroup
    (logRatio_mem_hyperplane F hF E hE)

def logLattice (F : Type*) [Field F] [NumberField F]
    (hF : NumberField.InfinitePlace.nrRealPlaces F = 0)
    (E : Subgroup Fˣ) (hE : E ≤ KPCuspArithmetic.rationalUnits F) :
    Submodule ℤ (hyperplane (dimension F)) :=
  (logarithm F hF E hE).range.toIntSubmodule

def horizontalLattice (F : Type*) [Field F] [NumberField F] (L : AddSubgroup F) :
    AddSubgroup (NumberField.mixedEmbedding.mixedSpace F) :=
  L.map (NumberField.mixedEmbedding F).toAddMonoidHom

theorem sum_logRatio_eq_zero (F : Type*) [Field F] [NumberField F]
    (hF : NumberField.InfinitePlace.nrRealPlaces F = 0)
    (E : Subgroup Fˣ) (hE : E ≤ KPCuspArithmetic.rationalUnits F) (u : E) :
    ∑ i : Fin (dimension F), logRatio F E (Additive.ofMul u) i = 0 := by
  have h := logRatio_mem_hyperplane F hF E hE (Additive.ofMul u)
  rw [hyperplane, LinearMap.mem_ker] at h
  simpa [sumCoordinates] using h

theorem meanHeight_ratioAction (F : Type*) [Field F] [NumberField F]
    (hF : NumberField.InfinitePlace.nrRealPlaces F = 0)
    (E : Subgroup Fˣ) (hE : E ≤ KPCuspArithmetic.rationalUnits F)
    (u : E) (z : KPArch.Space (dimension F)) :
    meanHeight (dimension F) (ratioAction F E u z) = meanHeight (dimension F) z := by
  unfold meanHeight ratioAction
  simp only [Finset.sum_add_distrib]
  rw [sum_logRatio_eq_zero F hF E hE u, add_zero]

theorem shapeCoordinates_ratioAction (F : Type*) [Field F] [NumberField F]
    (hF : NumberField.InfinitePlace.nrRealPlaces F = 0)
    (E : Subgroup Fˣ) (hE : E ≤ KPCuspArithmetic.rationalUnits F)
    (u : E) (hu : logarithm F hF E hE (Additive.ofMul u) = 0)
    (z : KPArch.Space (dimension F)) :
    shapeCoordinates (dimension F) (ratioAction F E u z) =
      shapeCoordinates (dimension F) z := by
  have hlog : logRatio F E (Additive.ofMul u) = 0 := by
    have := congrArg (fun w : hyperplane (dimension F) => (w : Fin (dimension F) → ℝ)) hu
    simpa [logarithm, LinearMap.codRestrict_apply] using this
  funext i
  unfold shapeCoordinates
  rw [meanHeight_ratioAction F hF E hE u z]
  simp [ratioAction, hlog]

theorem finite_logarithm_ker (F : Type*) [Field F] [NumberField F]
    (hF : NumberField.InfinitePlace.nrRealPlaces F = 0)
    (E : Subgroup Fˣ) (hE : E ≤ KPCuspArithmetic.rationalUnits F) :
    Finite (logarithm F hF E hE).ker := by
  let f := Units.map (algebraMap (NumberField.RingOfIntegers F) F).toMonoidHom
  let T := (NumberField.Units.torsion F).map f
  letI : Finite T := Finite.of_equiv (NumberField.Units.torsion F)
    ((NumberField.Units.torsion F).equivMapOfInjective f
      (Units.map_injective NumberField.RingOfIntegers.coe_injective)).toEquiv
  have hmem (u : (logarithm F hF E hE).ker) :
      ((u.val.toMul : E) : Fˣ) ∈ T := by
    obtain ⟨x, hx⟩ := hE u.val.toMul.property
    refine Subgroup.mem_map.mpr ⟨x, ?_, hx⟩
    apply (NumberField.Units.mem_torsion F).mpr
    intro w
    haveI : IsEmpty {v : NumberField.InfinitePlace F // v.IsReal} :=
      Fintype.card_eq_zero_iff.mp hF
    have hw : w.IsComplex := NumberField.InfinitePlace.not_isReal_iff_isComplex.mp
      (fun h => isEmptyElim (⟨w, h⟩ : {v : NumberField.InfinitePlace F // v.IsReal}))
    let i := Fintype.equivFin {v : NumberField.InfinitePlace F // v.IsComplex} ⟨w, hw⟩
    have hplace : KPCusp.complexPlace F i = w := by
      exact congrArg Subtype.val ((Fintype.equivFin
        {v : NumberField.InfinitePlace F // v.IsComplex}).symm_apply_apply ⟨w, hw⟩)
    have hlog : Real.log (w (((u.val.toMul : E) : Fˣ) : F)) = 0 := by
      have h := congrArg (fun b : hyperplane (dimension F) => (b : Fin (dimension F) → ℝ) i)
        u.property
      simpa [logarithm, logRatio, hplace] using h
    have hx' : algebraMap (NumberField.RingOfIntegers F) F
        (x : NumberField.RingOfIntegers F) = (((u.val.toMul : E) : Fˣ) : F) := by
      exact congrArg (fun v : Fˣ => (v : F)) hx
    rw [hx']
    exact Real.eq_one_of_pos_of_log_eq_zero
      (NumberField.InfinitePlace.pos_iff.mpr (Units.ne_zero _)) hlog
  exact Finite.of_injective (fun u : (logarithm F hF E hE).ker =>
    (⟨((u.val.toMul : E) : Fˣ), hmem u⟩ : T)) (by
      intro u v huv
      have hb : ((u.val.toMul : E) : Fˣ) = ((v.val.toMul : E) : Fˣ) :=
        congrArg (fun t : T => (t : Fˣ)) huv
      have he : u.val.toMul = v.val.toMul := Subtype.ext hb
      exact Subtype.ext (congrArg Additive.ofMul he))

theorem finrank_hyperplane (d : ℕ) (hd : 0 < d) :
    finrank ℝ (hyperplane d) = d - 1 := by
  have hn : sumCoordinates d ≠ 0 := by
    intro h
    have he := LinearMap.congr_fun h (fun _ => (1 : ℝ))
    have he' : (d : ℝ) = 0 := by simpa [sumCoordinates] using he
    exact (Nat.cast_ne_zero.mpr hd.ne') he'
  have h := Module.Dual.finrank_ker_add_one_of_ne_zero hn
  simp only [finrank_fintype_fun_eq_card, Fintype.card_fin] at h
  change finrank ℝ (sumCoordinates d).ker = d - 1
  omega

theorem dimension_pos (F : Type*) [Field F] [NumberField F]
    (hF : NumberField.InfinitePlace.nrRealPlaces F = 0) : 0 < dimension F := by
  have hc := NumberField.InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces (K := F)
  have hp := Fintype.card_pos (α := NumberField.InfinitePlace F)
  rw [hc, hF, zero_add] at hp
  exact hp

theorem shapeCoordinates_mem_hyperplane (d : ℕ) (hd : d ≠ 0)
    (z : KPArch.Space d) : shapeCoordinates d z ∈ hyperplane d := by
  rw [hyperplane, LinearMap.mem_ker]
  change ∑ i, ((z i).2 - meanHeight d z) = 0
  simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, meanHeight]
  rw [mul_div_cancel₀ _ (Nat.cast_ne_zero.mpr hd), sub_self]

theorem shapeCoordinates_ratioAction_add (F : Type*) [Field F] [NumberField F]
    (hF : NumberField.InfinitePlace.nrRealPlaces F = 0)
    (E : Subgroup Fˣ) (hE : E ≤ KPCuspArithmetic.rationalUnits F)
    (u : E) (z : KPArch.Space (dimension F)) :
    shapeCoordinates (dimension F) (ratioAction F E u z) =
      shapeCoordinates (dimension F) z + logRatio F E (Additive.ofMul u) := by
  funext i
  simp only [shapeCoordinates, meanHeight_ratioAction F hF E hE u z, ratioAction,
    Pi.add_apply]
  ring

theorem compact_quotient_of_isZLattice {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [FiniteDimensional ℝ V] (L : Submodule ℤ V)
    [DiscreteTopology L] [IsZLattice ℝ L] : CompactSpace (V ⧸ L.toAddSubgroup) := by
  apply isCompact_univ_iff.mp
  have h := IsZLattice.isCompact_range_of_periodic L
    (QuotientAddGroup.mk : V → V ⧸ L.toAddSubgroup) QuotientAddGroup.continuous_mk ?_
  · simpa only [Set.range_eq_univ.mpr QuotientAddGroup.mk_surjective] using h
  · intro z w hw
    rw [QuotientAddGroup.mk_add, (QuotientAddGroup.eq_zero_iff w).mpr hw, add_zero]

theorem parallelotope_cover_of_isZLattice (F : Type*) [Field F] [NumberField F]
    (hF : NumberField.InfinitePlace.nrRealPlaces F = 0)
    (E : Subgroup Fˣ) (hE : E ≤ KPCuspArithmetic.rationalUnits F)
    [DiscreteTopology (logLattice F hF E hE)] [IsZLattice ℝ (logLattice F hF E hE)] :
    ∃ B : Basis (Fin (dimension F - 1)) ℝ (hyperplane (dimension F)),
      Submodule.span ℤ (Set.range B) = logLattice F hF E hE ∧
      IsCompact (parallelepiped B) ∧
      (∀ b : hyperplane (dimension F), ∃ u : E,
        b - logarithm F hF E hE (Additive.ofMul u) ∈ parallelepiped B) ∧
      ∃ C : ℝ, 0 ≤ C ∧
        (∀ b ∈ parallelepiped B, ∀ i : Fin (dimension F),
          |(b : Fin (dimension F) → ℝ) i| ≤ C) ∧
        (∀ z : KPArch.Space (dimension F), ∃ u : E,
          ∃ b : hyperplane (dimension F), b ∈ parallelepiped B ∧
            (b : Fin (dimension F) → ℝ) = shapeCoordinates (dimension F)
              (ratioAction F E u z)) := by
  let L := logLattice F hF E hE
  haveI := ZLattice.module_finite ℝ L
  haveI := ZLattice.module_free ℝ L
  have hr : finrank ℤ L = dimension F - 1 := by
    rw [ZLattice.rank ℝ L, finrank_hyperplane _ (dimension_pos F hF)]
  let b := Module.finBasisOfFinrankEq ℤ L hr
  let B := b.ofZLatticeBasis ℝ L
  have hspan : Submodule.span ℤ (Set.range B) = L := b.ofZLatticeBasis_span ℝ
  have hcompact : IsCompact (parallelepiped B) := by
    exact B.coe_parallelepiped ▸ B.parallelepiped.isCompact
  have hcover (v : hyperplane (dimension F)) :
      ∃ u : E, v - logarithm F hF E hE (Additive.ofMul u) ∈ parallelepiped B := by
    have hm : (ZSpan.floor B v : hyperplane (dimension F)) ∈ L := by
      rw [← hspan]
      exact (ZSpan.floor B v).property
    obtain ⟨u, hu⟩ := hm
    refine ⟨u.toMul, ?_⟩
    change v - logarithm F hF E hE u ∈ parallelepiped B
    rw [hu]
    exact ZSpan.fundamentalDomain_subset_parallelepiped B
      (ZSpan.fract_mem_fundamentalDomain B v)
  refine ⟨B, hspan, hcompact, hcover, ?_⟩
  obtain ⟨r, hr⟩ := hcompact.isBounded.subset_closedBall 0
  refine ⟨max r 0, le_max_right _ _, ?_, ?_⟩
  · intro v hv i
    have hn : ‖v‖ ≤ r := by simpa using hr hv
    have hcoord : |(v : Fin (dimension F) → ℝ) i| ≤ ‖v‖ := by
      simpa using norm_le_pi_norm (v : Fin (dimension F) → ℝ) i
    exact hcoord.trans (hn.trans (le_max_left _ _))
  · intro z
    let v : hyperplane (dimension F) := ⟨shapeCoordinates (dimension F) z,
      shapeCoordinates_mem_hyperplane _ (dimension_pos F hF).ne' z⟩
    obtain ⟨u, hu⟩ := hcover v
    refine ⟨u⁻¹, v - logarithm F hF E hE (Additive.ofMul u), hu, ?_⟩
    rw [shapeCoordinates_ratioAction_add F hF E hE]
    change shapeCoordinates (dimension F) z - logRatio F E (Additive.ofMul u) =
      shapeCoordinates (dimension F) z + logRatio F E (Additive.ofMul u⁻¹)
    have hi : Additive.ofMul u⁻¹ = -Additive.ofMul u := rfl
    rw [hi, map_neg, sub_eq_add_neg]

open NumberField.Units.dirichletUnitTheorem

variable (F : Type*) [Field F] [NumberField F]
    (hF : NumberField.InfinitePlace.nrRealPlaces F = 0)

private def placeIndex (w : NumberField.InfinitePlace F) : Fin (dimension F) :=
  Fintype.equivFin {v : NumberField.InfinitePlace F // v.IsComplex} ⟨w, by
    haveI : IsEmpty {v : NumberField.InfinitePlace F // v.IsReal} :=
      Fintype.card_eq_zero_iff.mp hF
    exact NumberField.InfinitePlace.not_isReal_iff_isComplex.mp
      (fun h => isEmptyElim (⟨w,h⟩ : {v : NumberField.InfinitePlace F // v.IsReal}))⟩

private lemma placeIndex_complexPlace (i : Fin (dimension F)) :
    placeIndex F hF (KPCusp.complexPlace F i) = i := by
  unfold placeIndex KPCusp.complexPlace
  simp

private lemma complexPlace_placeIndex (w : NumberField.InfinitePlace F) :
    KPCusp.complexPlace F (placeIndex F hF w) = w := by
  unfold placeIndex KPCusp.complexPlace
  simp

private def toDirichlet : hyperplane (dimension F) →ₗ[ℝ] logSpace F where
  toFun b w := 2 * (b : Fin (dimension F) → ℝ) (placeIndex F hF w)
  map_add' b c := by ext w; simp [mul_add]
  map_smul' a b := by ext w; simp; ring

private lemma toDirichlet_injective : Function.Injective (toDirichlet F hF) := by
  apply (LinearMap.ker_eq_bot).mp
  rw [Submodule.eq_bot_iff]
  intro b hb
  apply Subtype.ext
  funext i
  have hz : ∑ j, (b : Fin (dimension F) → ℝ) j = 0 := b.property
  by_cases hw : KPCusp.complexPlace F i = w₀
  · have ho : ∀ j, j ≠ i → (b : Fin (dimension F) → ℝ) j = 0 := by
      intro j hj
      have hwj : KPCusp.complexPlace F j ≠ w₀ := by
        intro he
        have he' : j = i := by
          simpa only [placeIndex_complexPlace] using congrArg (placeIndex F hF) (he.trans hw.symm)
        exact hj he'
      have h := congrFun hb ⟨KPCusp.complexPlace F j, hwj⟩
      change 2 * (b : Fin (dimension F) → ℝ) (placeIndex F hF (KPCusp.complexPlace F j)) = 0 at h
      rw [placeIndex_complexPlace] at h
      linarith
    rw [Finset.sum_eq_single i] at hz
    · exact hz
    · intro j _ hj
      exact ho j hj
    · simp
  · have h := congrFun hb ⟨KPCusp.complexPlace F i, hw⟩
    change 2 * (b : Fin (dimension F) → ℝ) (placeIndex F hF (KPCusp.complexPlace F i)) = 0 at h
    rw [placeIndex_complexPlace] at h
    change (b : Fin (dimension F) → ℝ) i = 0
    linarith

private lemma toDirichlet_bijective : Function.Bijective (toDirichlet F hF) := by
  have hr : finrank ℝ (hyperplane (dimension F)) = finrank ℝ (logSpace F) := by
    rw [finrank_hyperplane _ (dimension_pos F hF), NumberField.Units.finrank_eq_rank]
    simp [NumberField.Units.rank,
      NumberField.InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces, hF, dimension]
  exact ⟨toDirichlet_injective F hF,
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hr).mp
      (toDirichlet_injective F hF)⟩

private lemma toDirichlet_logarithm (E : Subgroup Fˣ)
    (hE : E ≤ KPCuspArithmetic.rationalUnits F) (u : Additive E)
    (x : (NumberField.RingOfIntegers F)ˣ)
    (hx : Units.map (algebraMap (NumberField.RingOfIntegers F) F).toMonoidHom x =
      (u.toMul : Fˣ)) :
    toDirichlet F hF (logarithm F hF E hE u) =
      NumberField.Units.logEmbedding F (Additive.ofMul x) := by
  ext w
  have hw : w.val.IsComplex := by
    haveI : IsEmpty {v : NumberField.InfinitePlace F // v.IsReal} :=
      Fintype.card_eq_zero_iff.mp hF
    exact NumberField.InfinitePlace.not_isReal_iff_isComplex.mp
      (fun h => isEmptyElim (⟨w.val,h⟩ : {v : NumberField.InfinitePlace F // v.IsReal}))
  have hx' := congrArg (fun v : Fˣ => (v : F)) hx
  simp only [Units.coe_map] at hx'
  simp [toDirichlet, logarithm, logRatio, complexPlace_placeIndex,
    NumberField.Units.dirichletUnitTheorem.logEmbedding_component,
    NumberField.InfinitePlace.IsComplex.mult_eq_two hw]
  have hx'' : ((x : NumberField.RingOfIntegers F) : F) = ((u.toMul : Fˣ) : F) := by
    simpa using hx'
  rw [← NumberField.RingOfIntegers.coe_eq_algebraMap, hx'']

private lemma toDirichlet_mem_unitLattice (E : Subgroup Fˣ)
    (hE : E ≤ KPCuspArithmetic.rationalUnits F)
    (b : logLattice F hF E hE) : toDirichlet F hF b ∈ NumberField.Units.unitLattice F := by
  obtain ⟨u, hu⟩ := b.property
  obtain ⟨x, hx⟩ := hE u.toMul.property
  rw [← hu, toDirichlet_logarithm F hF E hE u x hx]
  exact ⟨Additive.ofMul x, Submodule.mem_top, rfl⟩

theorem logarithm_discrete (E : Subgroup Fˣ)
    (hE : E ≤ KPCuspArithmetic.rationalUnits F) :
    DiscreteTopology (logLattice F hF E hE) := by
  let f : logLattice F hF E hE → NumberField.Units.unitLattice F :=
    fun b => ⟨toDirichlet F hF b, toDirichlet_mem_unitLattice F hF E hE b⟩
  apply DiscreteTopology.of_continuous_injective (f := f)
    ((toDirichlet F hF).continuous_of_finiteDimensional.comp continuous_subtype_val |>.subtype_mk _)
    (by intro a b h; apply Subtype.ext; exact toDirichlet_injective F hF (congrArg Subtype.val h))

theorem logarithm_span_top (E : Subgroup Fˣ)
    (hE : E ≤ KPCuspArithmetic.rationalUnits F)
    (hindex : (E.subgroupOf (KPCuspArithmetic.rationalUnits F)).FiniteIndex) :
    Submodule.span ℝ (logLattice F hF E hE : Set (hyperplane (dimension F))) = ⊤ := by
  let L := logLattice F hF E hE
  let P := Submodule.span ℝ (toDirichlet F hF '' (L : Set (hyperplane (dimension F))))
  have hle : NumberField.Units.unitLattice F ≤ P.restrictScalars ℤ := by
    intro b hb
    obtain ⟨x, _, rfl⟩ := hb
    let f := Units.map (algebraMap (NumberField.RingOfIntegers F) F).toMonoidHom
    let xu : KPCuspArithmetic.rationalUnits F := ⟨f x.toMul, ⟨x.toMul, rfl⟩⟩
    letI := hindex
    obtain ⟨n, hn, _, hpow⟩ :=
      Subgroup.exists_pow_mem_of_index_ne_zero
        (H := E.subgroupOf (KPCuspArithmetic.rationalUnits F))
        Subgroup.FiniteIndex.index_ne_zero xu
    let u : E := ⟨(xu : Fˣ) ^ n, hpow⟩
    have hu : f (x.toMul ^ n) = (u : Fˣ) := by simp [u, xu, map_pow]
    have hlog : toDirichlet F hF (logarithm F hF E hE (Additive.ofMul u)) =
        n • NumberField.Units.logEmbedding F x := by
      rw [toDirichlet_logarithm F hF E hE (Additive.ofMul u) (x.toMul ^ n) hu]
      change NumberField.Units.logEmbedding F (n • x) = _
      exact map_nsmul _ _ _
    have hm : n • NumberField.Units.logEmbedding F x ∈ P := by
      rw [← hlog]
      apply Submodule.subset_span
      exact ⟨logarithm F hF E hE (Additive.ofMul u), ⟨Additive.ofMul u, rfl⟩, rfl⟩
    have hm' : (n : ℝ) • NumberField.Units.logEmbedding F x ∈ P := by
      simpa only [Nat.cast_smul_eq_nsmul] using hm
    have hs := P.smul_mem (n : ℝ)⁻¹ hm'
    rw [smul_smul, inv_mul_cancel₀ (Nat.cast_ne_zero.mpr hn.ne'), one_smul] at hs
    exact hs
  have ht : P = ⊤ := by
    apply top_unique
    rw [← NumberField.Units.dirichletUnitTheorem.unitLattice_span_eq_top F]
    exact Submodule.span_le.mpr hle
  let e := LinearEquiv.ofBijective (toDirichlet F hF) (toDirichlet_bijective F hF)
  apply (Submodule.map_injective_of_injective e.injective)
  rw [Submodule.map_top, LinearEquiv.range]
  change Submodule.map (toDirichlet F hF) (Submodule.span ℝ (L : Set _)) = ⊤
  rw [Submodule.map_span]
  exact ht

 theorem upper_action_snd (A : Matrix.GeneralLinearGroup (Fin 2) ℂ)
    (hA : A 1 0 = 0) (u : ℂ) (hu : u ≠ 0) (hr : A 0 0 = u * A 1 1)
    (z : KPArch.H3) : (KPArch.action A z).2 = z.2 + Real.log ‖u‖ := by
  have hd : A 1 1 ≠ 0 := by
    intro hz
    exact A.det_ne_zero (by simp [Matrix.det_fin_two, hA, hz])
  have he : ‖(A : Matrix (Fin 2) (Fin 2) ℂ).det‖ * KPArch.height z /
      KPArch.actionDenominator A z = ‖u‖ * KPArch.height z := by
    simp only [Matrix.det_fin_two, hA, zero_mul, sub_zero, hr, norm_mul,
      KPArch.actionDenominator, norm_zero, mul_zero, zero_add, zero_pow, add_zero]
    field_simp
    <;> ring
  change Real.log _ = _
  rw [he]
  simp [KPArch.height, Real.log_mul (norm_ne_zero_iff.mpr hu) (Real.exp_ne_zero _), add_comm]
theorem actual_upper_height_shape (F : Type*) [Field F] [NumberField F]
    (hF : NumberField.InfinitePlace.nrRealPlaces F = 0)
    (E : Subgroup Fˣ) (hE : E ≤ KPCuspArithmetic.rationalUnits F)
    (u : E) (A : Matrix.GeneralLinearGroup (Fin 2) F)
    (hA : (A : Matrix (Fin 2) (Fin 2) F) 1 0 = 0)
    (hr : (A : Matrix (Fin 2) (Fin 2) F) 0 0 = ((u : Fˣ) : F) *
      (A : Matrix (Fin 2) (Fin 2) F) 1 1)
    (z : KPArch.Space (dimension F)) :
    let Az := KPArch.productAction (dimension F)
      (fun i => Matrix.GeneralLinearGroup.map (KPCusp.complexPlace F i).embedding A) z
    meanHeight (dimension F) Az = meanHeight (dimension F) z ∧
    shapeCoordinates (dimension F) Az = shapeCoordinates (dimension F) z +
      logRatio F E (Additive.ofMul u) := by
  dsimp only
  have hs (i : Fin (dimension F)) :
      (KPArch.productAction (dimension F)
        (fun j => Matrix.GeneralLinearGroup.map (KPCusp.complexPlace F j).embedding A) z i).2 =
      (z i).2 + logRatio F E (Additive.ofMul u) i := by
    let v := KPCusp.complexPlace F i
    have hzero : (Matrix.GeneralLinearGroup.map v.embedding A) 1 0 = 0 := by
      change v.embedding ((A : Matrix (Fin 2) (Fin 2) F) 1 0) = 0
      rw [hA, map_zero]
    have hratio : (Matrix.GeneralLinearGroup.map v.embedding A) 0 0 =
        v.embedding ((u : Fˣ) : F) * (Matrix.GeneralLinearGroup.map v.embedding A) 1 1 := by
      change v.embedding ((A : Matrix (Fin 2) (Fin 2) F) 0 0) = _
      rw [hr, map_mul]
      rfl
    have hh := upper_action_snd (Matrix.GeneralLinearGroup.map v.embedding A) hzero
      (v.embedding ((u : Fˣ) : F)) ((map_ne_zero _).mpr (Units.ne_zero _)) hratio (z i)
    change (KPArch.action (Matrix.GeneralLinearGroup.map v.embedding A) (z i)).2 =
      (z i).2 + Real.log (v ((u : Fˣ) : F))
    simpa only [NumberField.InfinitePlace.norm_embedding_eq] using hh
  have hm : meanHeight (dimension F) (KPArch.productAction (dimension F)
        (fun i => Matrix.GeneralLinearGroup.map (KPCusp.complexPlace F i).embedding A) z) =
      meanHeight (dimension F) z := by
    unfold meanHeight
    simp_rw [hs]
    rw [Finset.sum_add_distrib, sum_logRatio_eq_zero F hF E hE, add_zero]
  refine ⟨hm, ?_⟩
  funext i
  simp only [shapeCoordinates, hm, Pi.add_apply, hs]
  ring

section TorusAction
variable (F : Type*) [Field F] [NumberField F] (L : AddSubgroup F) (E : Subgroup Fˣ)
variable (hinv : ∀ (u : E) (x : F), x ∈ L → ((u : Fˣ) : F) * x ∈ L)
private def torusMul (u : E) :
    (NumberField.mixedEmbedding.mixedSpace F ⧸ horizontalLattice F L) →+
      (NumberField.mixedEmbedding.mixedSpace F ⧸ horizontalLattice F L) :=
  QuotientAddGroup.map (horizontalLattice F L) (horizontalLattice F L)
    (AddMonoidHom.mulLeft (NumberField.mixedEmbedding F ((u : Fˣ) : F))) (by
      intro x hx
      obtain ⟨a, ha, rfl⟩ := hx
      exact ⟨((u : Fˣ) : F) * a, hinv u a ha,
        (NumberField.mixedEmbedding F).map_mul _ _⟩)
private theorem torusMul_mk (u : E) (x : NumberField.mixedEmbedding.mixedSpace F) :
    torusMul F L E hinv u (QuotientAddGroup.mk x) =
      QuotientAddGroup.mk (NumberField.mixedEmbedding F ((u : Fˣ) : F) * x) := rfl
private theorem torusMul_one : torusMul F L E hinv 1 = AddMonoidHom.id _ := by
  ext x
  simp [torusMul_mk]
private theorem torusMul_mul (u v : E) : torusMul F L E hinv (u * v) =
    (torusMul F L E hinv u).comp (torusMul F L E hinv v) := by
  ext x
  simp [torusMul_mk, mul_assoc]
private def torusAut (u : E) :
    AddAut (NumberField.mixedEmbedding.mixedSpace F ⧸ horizontalLattice F L) where
  toFun := torusMul F L E hinv u
  invFun := torusMul F L E hinv u⁻¹
  left_inv x := by
    change ((torusMul F L E hinv u⁻¹).comp (torusMul F L E hinv u)) x = x
    rw [← torusMul_mul, inv_mul_cancel, torusMul_one]
    rfl
  right_inv x := by
    change ((torusMul F L E hinv u).comp (torusMul F L E hinv u⁻¹)) x = x
    rw [← torusMul_mul, mul_inv_cancel, torusMul_one]
    rfl
  map_add' := (torusMul F L E hinv u).map_add
 theorem torus_unit_action (hinv : ∀ (u : E) (x : F), x ∈ L → ((u : Fˣ) : F) * x ∈ L) :
    ∃ α : E →* Multiplicative (AddAut
        (NumberField.mixedEmbedding.mixedSpace F ⧸ horizontalLattice F L)),
      (∀ u : E, Continuous ((α u).toAdd)) ∧
      (∀ (u : E) (x : NumberField.mixedEmbedding.mixedSpace F),
        (α u).toAdd (QuotientAddGroup.mk x) = QuotientAddGroup.mk
          (NumberField.mixedEmbedding F ((u : Fˣ) : F) * x)) := by
  let α : E →* Multiplicative (AddAut
      (NumberField.mixedEmbedding.mixedSpace F ⧸ horizontalLattice F L)) := {
    toFun := fun u => Multiplicative.ofAdd (torusAut F L E hinv u)
    map_one' := by
      apply congrArg Multiplicative.ofAdd
      ext x
      exact DFunLike.congr_fun (torusMul_one F L E hinv) x
    map_mul' := by
      intro u v
      apply congrArg Multiplicative.ofAdd
      ext x
      exact DFunLike.congr_fun (torusMul_mul F L E hinv u v) x }
  refine ⟨α, ?_, ?_⟩
  · intro u
    change Continuous (torusMul F L E hinv u)
    rw [← QuotientAddGroup.isOpenQuotientMap_mk.continuous_comp_iff]
    exact QuotientAddGroup.continuous_mk.comp (continuous_const.mul continuous_id)
  · intro u x
    exact torusMul_mk F L E hinv u x
end TorusAction

section AffineAction
variable (F : Type*) [Field F]
private lemma upper_right_ne_zero (A : Matrix.GeneralLinearGroup (Fin 2) F)
    (hA : A 1 0 = 0) : A 1 1 ≠ 0 := by
  intro hz
  exact A.det_ne_zero (by simp [Matrix.det_fin_two, hA, hz])
private lemma upper_translation_eq (A B : Matrix.GeneralLinearGroup (Fin 2) F)
    (hAB : Matrix.ProjGenLinGroup.mk A = Matrix.ProjGenLinGroup.mk B)
    (hA : A 1 0 = 0) : A 0 1 / A 1 1 = B 0 1 / B 1 1 := by
  obtain ⟨u, rfl⟩ := Matrix.ProjGenLinGroup.mk_eq_mk_iff.mp hAB
  simp only [Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar, Matrix.mul_apply,
    Fin.sum_univ_two, Matrix.scalar, Matrix.diagonal_apply]
  simp
  rw [mul_div_mul_right _ _ (Units.ne_zero u)]
private def upperRepresentative (S : Subgroup (KPCuspArithmetic.PGL2 F))
    (hS : ∀ g ∈ S, KPCuspArithmetic.IsUpperTriangular F g) (g : S) :=
  Classical.choose (hS g g.property)
private lemma upperRepresentative_upper (S : Subgroup (KPCuspArithmetic.PGL2 F))
    (hS : ∀ g ∈ S, KPCuspArithmetic.IsUpperTriangular F g) (g : S) :
    upperRepresentative F S hS g 1 0 = 0 :=
  (Classical.choose_spec (hS g g.property)).2
private lemma upperRepresentative_mk (S : Subgroup (KPCuspArithmetic.PGL2 F))
    (hS : ∀ g ∈ S, KPCuspArithmetic.IsUpperTriangular F g) (g : S) :
    Matrix.ProjGenLinGroup.mk (upperRepresentative F S hS g) = g :=
  (Classical.choose_spec (hS g g.property)).1
private def upperTranslation (S : Subgroup (KPCuspArithmetic.PGL2 F))
    (hS : ∀ g ∈ S, KPCuspArithmetic.IsUpperTriangular F g) (g : S) : F :=
  upperRepresentative F S hS g 0 1 / upperRepresentative F S hS g 1 1
private theorem upperTranslation_formula (S : Subgroup (KPCuspArithmetic.PGL2 F))
    (hS : ∀ g ∈ S, KPCuspArithmetic.IsUpperTriangular F g) (g : S)
    (A : Matrix.GeneralLinearGroup (Fin 2) F)
    (hA : Matrix.ProjGenLinGroup.mk A = g) :
    upperTranslation F S hS g = A 0 1 / A 1 1 := by
  exact upper_translation_eq F _ _ ((upperRepresentative_mk F S hS g).trans hA.symm)
    (upperRepresentative_upper F S hS g)
 theorem upper_translation_cocycle (S : Subgroup (KPCuspArithmetic.PGL2 F))
    (hS : ∀ g ∈ S, KPCuspArithmetic.IsUpperTriangular F g)
    (E : Subgroup Fˣ) (ρ : S →* E)
    (hr : ∀ (g : S) (A : Matrix.GeneralLinearGroup (Fin 2) F),
      Matrix.ProjGenLinGroup.mk A = (g : KPCuspArithmetic.PGL2 F) → A 1 0 = 0 →
      A 0 0 = ((ρ g : Fˣ) : F) * A 1 1) :
    ∃ τ : S → F, τ 1 = 0 ∧
      (∀ g h : S, τ (g * h) = ((ρ g : Fˣ) : F) * τ h + τ g) ∧
      (∀ (g : S) (A : Matrix.GeneralLinearGroup (Fin 2) F),
        Matrix.ProjGenLinGroup.mk A = (g : KPCuspArithmetic.PGL2 F) →
        τ g = A 0 1 / A 1 1) := by
  refine ⟨upperTranslation F S hS, ?_, ?_, upperTranslation_formula F S hS⟩
  · rw [upperTranslation_formula F S hS 1 1 (by simp)]
    simp
  · intro g h
    let A := upperRepresentative F S hS g
    let B := upperRepresentative F S hS h
    have hA : A 1 0 = 0 := upperRepresentative_upper F S hS g
    have hB : B 1 0 = 0 := upperRepresentative_upper F S hS h
    have hAr := hr g A (upperRepresentative_mk F S hS g) hA
    have hnA := upper_right_ne_zero F A hA
    have hnB := upper_right_ne_zero F B hB
    rw [upperTranslation_formula F S hS (g * h) (A * B) (by
      rw [map_mul, upperRepresentative_mk, upperRepresentative_mk]; rfl)]
    change (A * B) 0 1 / (A * B) 1 1 =
      ((ρ g : Fˣ) : F) * (B 0 1 / B 1 1) + A 0 1 / A 1 1
    simp only [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, hA, hAr, zero_mul, zero_add]
    field_simp
    <;> ring

 theorem upper_affine_torus_action (S : Subgroup (KPCuspArithmetic.PGL2 F))
    [NumberField F] (hS : ∀ g ∈ S, KPCuspArithmetic.IsUpperTriangular F g)
    (L : AddSubgroup F) (E : Subgroup Fˣ) (ρ : S →* E)
    (hr : ∀ (g : S) (A : Matrix.GeneralLinearGroup (Fin 2) F),
      Matrix.ProjGenLinGroup.mk A = (g : KPCuspArithmetic.PGL2 F) → A 1 0 = 0 →
      A 0 0 = ((ρ g : Fˣ) : F) * A 1 1)
    (hinv : ∀ (u : E) (x : F), x ∈ L → ((u : Fˣ) : F) * x ∈ L) :
    ∃ β : S → (NumberField.mixedEmbedding.mixedSpace F ⧸ horizontalLattice F L) →
        (NumberField.mixedEmbedding.mixedSpace F ⧸ horizontalLattice F L),
      (∀ x, β 1 x = x) ∧
      (∀ g h x, β (g * h) x = β g (β h x)) ∧
      (∀ g, Continuous (β g)) ∧
      (∀ (g : S) (A : Matrix.GeneralLinearGroup (Fin 2) F)
        (x : NumberField.mixedEmbedding.mixedSpace F),
        Matrix.ProjGenLinGroup.mk A = (g : KPCuspArithmetic.PGL2 F) →
        A 1 0 = 0 →
        β g (QuotientAddGroup.mk x) = QuotientAddGroup.mk
          (NumberField.mixedEmbedding F ((ρ g : Fˣ) : F) * x +
            NumberField.mixedEmbedding F (A 0 1 / A 1 1))) := by
    obtain ⟨τ, hτ1, hτmul, hτformula⟩ := upper_translation_cocycle F S hS E ρ hr
    obtain ⟨α, hαcont, hαformula⟩ := torus_unit_action F L E hinv
    let β : S → (NumberField.mixedEmbedding.mixedSpace F ⧸ horizontalLattice F L) →
        (NumberField.mixedEmbedding.mixedSpace F ⧸ horizontalLattice F L) :=
      fun g x => (α (ρ g)).toAdd x + QuotientAddGroup.mk (NumberField.mixedEmbedding F (τ g))
    refine ⟨β, ?_, ?_, ?_, ?_⟩
    · intro x
      simp only [β, map_one, hτ1, map_zero,
        QuotientAddGroup.mk_zero, add_zero]
      rfl
    · intro g h x
      simp only [β, map_mul]
      change (α (ρ g)).toAdd ((α (ρ h)).toAdd x) + QuotientAddGroup.mk
        (NumberField.mixedEmbedding F (τ (g * h))) =
        (α (ρ g)).toAdd ((α (ρ h)).toAdd x + QuotientAddGroup.mk
          (NumberField.mixedEmbedding F (τ h))) +
          QuotientAddGroup.mk (NumberField.mixedEmbedding F (τ g))
      rw [hτmul, map_add, QuotientAddGroup.mk_add, map_mul,
        ← hαformula (ρ g) (NumberField.mixedEmbedding F (τ h)), map_add]
      abel
    · intro g
      exact ((hαcont (ρ g)).add continuous_const)
    · intro g A x hA _
      simp only [β, hαformula, hτformula g A hA, QuotientAddGroup.mk_add]
end AffineAction

 theorem actual_translation_lattice_stable (F : Type*) [Field F]
    (S : Subgroup (KPCuspArithmetic.PGL2 F))
    (hS : ∀ g ∈ S, KPCuspArithmetic.IsUpperTriangular F g)
    (L : AddSubgroup F) (E : Subgroup Fˣ)
    (ι : Multiplicative L →* S) (ρ : S →* E)
    (hsurj : Function.Surjective ρ) (hexact : ι.range = ρ.ker)
    (htrans : ∀ (x : L) (A : Matrix.GeneralLinearGroup (Fin 2) F),
      Matrix.ProjGenLinGroup.mk A = (ι (Multiplicative.ofAdd x) : KPCuspArithmetic.PGL2 F) →
      A 1 0 = 0 ∧ A 0 0 = A 1 1 ∧ A 0 1 = (x : F) * A 0 0)
    (hr : ∀ (g : S) (A : Matrix.GeneralLinearGroup (Fin 2) F),
      Matrix.ProjGenLinGroup.mk A = (g : KPCuspArithmetic.PGL2 F) → A 1 0 = 0 →
      A 0 0 = ((ρ g : Fˣ) : F) * A 1 1) :
    ∀ (u : E) (x : F), x ∈ L → ((u : Fˣ) : F) * x ∈ L := by
  obtain ⟨τ, hτ1, hτmul, hτformula⟩ := upper_translation_cocycle F S hS E ρ hr
  have hτi (x : L) : τ (ι (Multiplicative.ofAdd x)) = x := by
    obtain ⟨A, hA⟩ := Matrix.ProjGenLinGroup.mk_surjective
      (ι (Multiplicative.ofAdd x) : KPCuspArithmetic.PGL2 F)
    obtain ⟨hzero, hdiag, ht⟩ := htrans x A hA
    have hd : A 1 1 ≠ 0 := by
      intro hz
      exact A.det_ne_zero (by simp [Matrix.det_fin_two, hzero, hz])
    rw [hτformula _ _ hA, ht, hdiag, mul_div_cancel_right₀ _ hd]
  have hρi (x : L) : ρ (ι (Multiplicative.ofAdd x)) = 1 := by
    apply MonoidHom.mem_ker.mp
    rw [← hexact]
    exact ⟨Multiplicative.ofAdd x, rfl⟩
  intro u x hx
  obtain ⟨g, rfl⟩ := hsurj u
  let xi : L := ⟨x, hx⟩
  have hker : g * ι (Multiplicative.ofAdd xi) * g⁻¹ ∈ ρ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_mul, hρi, mul_one, map_inv, mul_inv_cancel]
  rw [← hexact] at hker
  obtain ⟨y, hy⟩ := hker
  have hτinv : ((ρ g : Fˣ) : F) * τ g⁻¹ + τ g = 0 := by
    rw [← hτmul, mul_inv_cancel, hτ1]
  have hτconj : τ (g * ι (Multiplicative.ofAdd xi) * g⁻¹) =
      ((ρ g : Fˣ) : F) * x := by
    rw [hτmul, map_mul, hρi, mul_one, hτmul, hτi]
    change ((ρ g : Fˣ) : F) * τ g⁻¹ +
      (((ρ g : Fˣ) : F) * x + τ g) = ((ρ g : Fˣ) : F) * x
    linear_combination hτinv
  have hxy : (y.toAdd : F) = ((ρ g : Fˣ) : F) * x := by
    rw [← hτi y.toAdd]
    change τ (ι y) = _
    rw [hy, hτconj]
  rw [← hxy]
  exact y.toAdd.property

end KPCuspLogShape

theorem kp_cusp_log_unit_shape
    (F : Type*) [Field F] [NumberField F]
    (hF : NumberField.InfinitePlace.nrRealPlaces F = 0)
    (E : Subgroup Fˣ) (hE : E ≤ KPCuspArithmetic.rationalUnits F)
    (hindex : (E.subgroupOf (KPCuspArithmetic.rationalUnits F)).FiniteIndex) :
    let d := KPCuspLogShape.dimension F
    let H := KPCuspLogShape.hyperplane d
    let ell := KPCuspLogShape.logarithm F hF E hE
    let Λ := KPCuspLogShape.logLattice F hF E hE
    (∃ hdisc : DiscreteTopology Λ, letI := hdisc; IsZLattice ℝ Λ) ∧
    CompactSpace (H ⧸ Λ.toAddSubgroup) ∧
    Finite ell.ker ∧
    (∀ (u : E) (z : KPArch.Space d),
      KPCuspLogShape.meanHeight d (KPCuspLogShape.ratioAction F E u z) =
        KPCuspLogShape.meanHeight d z) ∧
    (∀ (u : E), ell (Additive.ofMul u) = 0 →
      ∀ z : KPArch.Space d,
        KPCuspLogShape.shapeCoordinates d (KPCuspLogShape.ratioAction F E u z) =
          KPCuspLogShape.shapeCoordinates d z) ∧
    ∃ B : Basis (Fin (d - 1)) ℝ H,
      Submodule.span ℤ (Set.range B) = Λ ∧
      IsCompact (parallelepiped B) ∧
      (∀ b : H, ∃ u : E, b - ell (Additive.ofMul u) ∈ parallelepiped B) ∧
      ∃ C : ℝ, 0 ≤ C ∧
        (∀ b ∈ parallelepiped B, ∀ i : Fin d, |(b : Fin d → ℝ) i| ≤ C) ∧
        (∀ z : KPArch.Space d, ∃ u : E,
          ∃ b : H, b ∈ parallelepiped B ∧
            (b : Fin d → ℝ) = KPCuspLogShape.shapeCoordinates d
              (KPCuspLogShape.ratioAction F E u z)) := by
  dsimp only
  have hlat : ∃ hdisc : DiscreteTopology (KPCuspLogShape.logLattice F hF E hE),
      letI := hdisc; IsZLattice ℝ (KPCuspLogShape.logLattice F hF E hE) := by
    letI := KPCuspLogShape.logarithm_discrete F hF E hE
    exact ⟨inferInstance, ⟨KPCuspLogShape.logarithm_span_top F hF E hE hindex⟩⟩
  obtain ⟨hdisc, hfull⟩ := hlat
  letI := hdisc
  letI := hfull
  refine ⟨⟨hdisc, hfull⟩, ?_, ?_, ?_, ?_, ?_⟩
  · exact KPCuspLogShape.compact_quotient_of_isZLattice _
  · exact KPCuspLogShape.finite_logarithm_ker F hF E hE
  · exact fun u z => KPCuspLogShape.meanHeight_ratioAction F hF E hE u z
  · exact fun u hu z => KPCuspLogShape.shapeCoordinates_ratioAction F hF E hE u hu z
  · exact KPCuspLogShape.parallelotope_cover_of_isZLattice F hF E hE

namespace KPCuspLogShape.UnitTorus

variable (F : Type*) [Field F] [NumberField F]
variable (L : AddSubgroup F) (E : Subgroup Fˣ)
variable (hstable : ∀ (u : E) (x : F), x ∈ L → ((u : Fˣ) : F) * x ∈ L)
private def mulHom (u : E) : NumberField.mixedEmbedding.mixedSpace F →+ NumberField.mixedEmbedding.mixedSpace F where
  toFun x := NumberField.mixedEmbedding F ((u : Fˣ) : F) * x
  map_zero' := mul_zero _
  map_add' := mul_add _
include hstable
private lemma mulHom_stable (u : E) : horizontalLattice F L ≤ AddSubgroup.comap (mulHom F E u) (horizontalLattice F L) := by
  rintro x ⟨y, hy, rfl⟩
  exact ⟨((u : Fˣ) : F) * y, hstable u y hy, by simp [mulHom]⟩
private def torusMul (u : E) : (NumberField.mixedEmbedding.mixedSpace F ⧸ horizontalLattice F L) →+
    (NumberField.mixedEmbedding.mixedSpace F ⧸ horizontalLattice F L) :=
  QuotientAddGroup.map _ _ (mulHom F E u) (mulHom_stable F L E hstable u)
private lemma torusMul_mk (u : E) (x : NumberField.mixedEmbedding.mixedSpace F) :
    torusMul F L E hstable u (QuotientAddGroup.mk x) = QuotientAddGroup.mk (NumberField.mixedEmbedding F ((u : Fˣ) : F) * x) := rfl
private lemma torusMul_one (x : NumberField.mixedEmbedding.mixedSpace F ⧸ horizontalLattice F L) :
    torusMul F L E hstable 1 x = x := by
  induction x using QuotientAddGroup.induction_on with | H x => simp [torusMul_mk]
private lemma torusMul_mul (u v : E) (x : NumberField.mixedEmbedding.mixedSpace F ⧸ horizontalLattice F L) :
    torusMul F L E hstable (u * v) x = torusMul F L E hstable u (torusMul F L E hstable v x) := by
  induction x using QuotientAddGroup.induction_on with
  | H x => simp [torusMul_mk, map_mul, mul_assoc]
private def torusAut (u : E) : AddAut (NumberField.mixedEmbedding.mixedSpace F ⧸ horizontalLattice F L) where
  toFun := torusMul F L E hstable u
  invFun := torusMul F L E hstable u⁻¹
  left_inv x := by rw [← torusMul_mul, inv_mul_cancel, torusMul_one]
  right_inv x := by rw [← torusMul_mul, mul_inv_cancel, torusMul_one]
  map_add' := map_add _

theorem exists_unit_torus_action : ∃ α : E →* Multiplicative (AddAut (NumberField.mixedEmbedding.mixedSpace F ⧸ horizontalLattice F L)),
    (∀ u : E, Continuous ((α u).toAdd)) ∧
    (∀ (u : E) (x : NumberField.mixedEmbedding.mixedSpace F),
      (α u).toAdd (QuotientAddGroup.mk x) = QuotientAddGroup.mk
        (NumberField.mixedEmbedding F ((u : Fˣ) : F) * x)) := by
  let α : E →* Multiplicative (AddAut (NumberField.mixedEmbedding.mixedSpace F ⧸ horizontalLattice F L)) := {
    toFun := fun u => Multiplicative.ofAdd (torusAut F L E hstable u)
    map_one' := by apply Multiplicative.toAdd.injective; ext x; exact torusMul_one F L E hstable x
    map_mul' := by intro u v; apply Multiplicative.toAdd.injective; ext x; exact torusMul_mul F L E hstable u v x }
  refine ⟨α, ?_, fun u x => torusMul_mk F L E hstable u x⟩
  intro u
  apply continuous_quot_lift
  exact QuotientAddGroup.continuous_mk.comp (continuous_const.mul continuous_id)

end KPCuspLogShape.UnitTorus

namespace KPCuspLogShape.AffineTorus

variable {F : Type*} [Field F] [NumberField F]
private lemma upper_diagonal_ne_zero (A : Matrix.GeneralLinearGroup (Fin 2) F) (hA : A 1 0 = 0) : A 1 1 ≠ 0 := by
  intro hz
  exact A.det_ne_zero (by simp [Matrix.det_fin_two, hA, hz])

private lemma translation_same (A B : Matrix.GeneralLinearGroup (Fin 2) F)
    (h : Matrix.ProjGenLinGroup.mk A = Matrix.ProjGenLinGroup.mk B) :
    A 0 1 / A 1 1 = B 0 1 / B 1 1 := by
  obtain ⟨u, rfl⟩ := Matrix.ProjGenLinGroup.mk_eq_mk_iff.mp h
  simp only [Matrix.GeneralLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
  simp
  field_simp
  <;> ring
private lemma translation_mul (A B : Matrix.GeneralLinearGroup (Fin 2) F)
    (hA : A 1 0 = 0) (hB : B 1 0 = 0) (u : F) (hu : A 0 0 = u * A 1 1) :
    (A * B) 0 1 / (A * B) 1 1 = u * (B 0 1 / B 1 1) + A 0 1 / A 1 1 := by
  have ha := upper_diagonal_ne_zero A hA
  have hb := upper_diagonal_ne_zero B hB
  simp only [Matrix.GeneralLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two,
    hA, hu, zero_mul, zero_add]
  field_simp
  <;> ring
variable (F : Type*) [Field F] [NumberField F]
variable (S : Subgroup (KPCuspArithmetic.PGL2 F)) (E : Subgroup Fˣ) (ρ : S →* E)
variable (hupper : ∀ g ∈ S, KPCuspArithmetic.IsUpperTriangular F g)
variable (hratio : ∀ (g : S) (A : Matrix.GeneralLinearGroup (Fin 2) F),
  Matrix.ProjGenLinGroup.mk A = (g : KPCuspArithmetic.PGL2 F) → A 1 0 = 0 →
  A 0 0 = ((ρ g : Fˣ) : F) * A 1 1)
private def representative (g : S) : Matrix.GeneralLinearGroup (Fin 2) F := (hupper g g.property).choose
private lemma representative_spec (g : S) :
    Matrix.ProjGenLinGroup.mk (representative F S hupper g) = (g : KPCuspArithmetic.PGL2 F) ∧
    representative F S hupper g 1 0 = 0 := (hupper g g.property).choose_spec
private def translation (g : S) : F := representative F S hupper g 0 1 / representative F S hupper g 1 1
private lemma translation_formula (g : S) (A : Matrix.GeneralLinearGroup (Fin 2) F)
    (h : Matrix.ProjGenLinGroup.mk A = (g : KPCuspArithmetic.PGL2 F)) :
    translation F S hupper g = A 0 1 / A 1 1 :=
  translation_same _ A ((representative_spec F S hupper g).1.trans h.symm)
private lemma translation_one : translation F S hupper 1 = 0 := by
  rw [translation_formula F S hupper 1 1 (by simp)]
  simp
include hratio
private lemma translation_product (g h : S) : translation F S hupper (g * h) =
    ((ρ g : Fˣ) : F) * translation F S hupper h + translation F S hupper g := by
  let A := representative F S hupper g
  let B := representative F S hupper h
  have ha := representative_spec F S hupper g
  have hb := representative_spec F S hupper h
  rw [translation_formula F S hupper (g * h) (A * B) (by rw [map_mul, ha.1, hb.1]; rfl)]
  exact translation_mul A B ha.2 hb.2 ((ρ g : Fˣ) : F) (hratio g A ha.1 ha.2)
variable (L : AddSubgroup F)
variable (hstable : ∀ (u : E) (x : F), x ∈ L → ((u : Fˣ) : F) * x ∈ L)
include hupper hratio hstable

theorem exists_affine_torus_action :
    ∃ β : S → (NumberField.mixedEmbedding.mixedSpace F ⧸ horizontalLattice F L) →
        (NumberField.mixedEmbedding.mixedSpace F ⧸ horizontalLattice F L),
      (∀ x, β 1 x = x) ∧
      (∀ g h x, β (g * h) x = β g (β h x)) ∧
      (∀ g, Continuous (β g)) ∧
      (∀ (g : S) (A : Matrix.GeneralLinearGroup (Fin 2) F)
          (x : NumberField.mixedEmbedding.mixedSpace F),
        Matrix.ProjGenLinGroup.mk A = (g : KPCuspArithmetic.PGL2 F) →
        A 1 0 = 0 → β g (QuotientAddGroup.mk x) = QuotientAddGroup.mk
          (NumberField.mixedEmbedding F ((ρ g : Fˣ) : F) * x +
            NumberField.mixedEmbedding F (A 0 1 / A 1 1))) := by
  obtain ⟨α, hcont, hformula⟩ := torus_unit_action F L E hstable
  let τ : S → NumberField.mixedEmbedding.mixedSpace F ⧸ horizontalLattice F L :=
    fun g => QuotientAddGroup.mk (NumberField.mixedEmbedding F (translation F S hupper g))
  let β := fun (g : S) x => (α (ρ g)).toAdd x + τ g
  have hτ1 : τ 1 = 0 := by simp [τ, translation_one]
  have hτmul (g h : S) : τ (g * h) = (α (ρ g)).toAdd (τ h) + τ g := by
    simp only [τ, translation_product F S E ρ hupper hratio, map_add, map_mul,
      QuotientAddGroup.mk_add, hformula]
  refine ⟨β, ?_, ?_, ?_, ?_⟩
  · intro x
    simp [β, hτ1]
  · intro g h x
    change (α (ρ (g * h))).toAdd x + τ (g * h) =
      (α (ρ g)).toAdd ((α (ρ h)).toAdd x + τ h) + τ g
    rw [map_mul, map_mul, hτmul, map_add]
    change (α (ρ g)).toAdd ((α (ρ h)).toAdd x) +
      ((α (ρ g)).toAdd (τ h) + τ g) = _
    abel
  · intro g
    exact (hcont (ρ g)).add continuous_const
  · intro g A x hA _
    simp only [β, hformula, τ, translation_formula F S hupper g A hA,
      QuotientAddGroup.mk_add]

end KPCuspLogShape.AffineTorus

namespace KPCuspLogShape.ExactSequence

variable (F : Type*) [Field F] [NumberField F]
variable (S : Subgroup (KPCuspArithmetic.PGL2 F))
variable (hS : ∀ g ∈ S, KPCuspArithmetic.IsUpperTriangular F g)
variable (L : AddSubgroup F) (E : Subgroup Fˣ) (ι : Multiplicative L →* S) (ρ : S →* E)
variable (hsurj : Function.Surjective ρ) (hexact : ι.range = ρ.ker)
variable (hi : ∀ (x : L) (A : Matrix.GeneralLinearGroup (Fin 2) F),
    Matrix.ProjGenLinGroup.mk A = (ι (Multiplicative.ofAdd x) : KPCuspArithmetic.PGL2 F) →
    A 1 0 = 0 ∧ A 0 0 = A 1 1 ∧ A 0 1 = (x : F) * A 0 0)
variable (hr : ∀ (g : S) (A : Matrix.GeneralLinearGroup (Fin 2) F),
  Matrix.ProjGenLinGroup.mk A = (g : KPCuspArithmetic.PGL2 F) → A 1 0 = 0 →
  A 0 0 = ((ρ g : Fˣ) : F) * A 1 1)
include hS hsurj hexact hi hr

theorem actual_translation_lattice_stable : ∀ (u : E) (x : F), x ∈ L → ((u : Fˣ) : F) * x ∈ L := by
  obtain ⟨τ, hτone, hτmul, hτformula⟩ := KPCuspLogShape.upper_translation_cocycle F S hS E ρ hr
  have hker (x : Multiplicative L) : ρ (ι x) = 1 := by
    apply MonoidHom.mem_ker.mp
    rw [← hexact]
    exact ⟨x, rfl⟩
  have hτi (x : L) : τ (ι (Multiplicative.ofAdd x)) = (x : F) := by
    obtain ⟨A, hA, ha⟩ := hS (ι (Multiplicative.ofAdd x)) (ι (Multiplicative.ofAdd x)).property
    obtain ⟨h0, hd, ht⟩ := hi x A hA
    have hn : A 1 1 ≠ 0 := by
      intro hz
      exact A.det_ne_zero (by simp [Matrix.det_fin_two, h0, hz])
    rw [hτformula _ A hA, ht, hd, mul_div_cancel_right₀ _ hn]
  intro u x hx
  obtain ⟨g, rfl⟩ := hsurj u
  let k := ι (Multiplicative.ofAdd (⟨x, hx⟩ : L))
  have hconj : g * k * g⁻¹ ∈ ι.range := by
    rw [hexact, MonoidHom.mem_ker]
    simp [k, hker]
  obtain ⟨y, hy⟩ := hconj
  have ht : τ (g * k * g⁻¹) = ((ρ g : Fˣ) : F) * x := by
    have hiinv := hτmul g g⁻¹
    simp only [mul_inv_cancel, hτone] at hiinv
    rw [hτmul, hτmul]
    have hrk : ρ k = 1 := hker _
    simp only [map_mul, hrk, mul_one, Units.val_mul, Subgroup.coe_mul]
    have hk : τ k = x := hτi ⟨x, hx⟩
    rw [hk]
    linear_combination -hiinv
  have hty : τ (g * k * g⁻¹) = ((y.toAdd : L) : F) := by
    rw [← hy]
    exact hτi y.toAdd
  rw [← ht, hty]
  exact y.toAdd.property

end KPCuspLogShape.ExactSequence

theorem kp_cusp_log_unit_shape_actual_stabilizer
    (F : Type*) [Field F] [NumberField F]
    (hF : NumberField.InfinitePlace.nrRealPlaces F = 0)
    (M : Submodule (KPCuspArithmetic.Order F) (KPCuspArithmetic.Vec F))
    (hM : KPCuspArithmetic.IsRankTwoLattice F M)
    (Γ : Subgroup (KPCuspArithmetic.PGL2 F))
    (hΓ : ∀ g ∈ Γ, KPCuspArithmetic.PreservesUpToHomothety F M g)
    (hcomm : Γ.Commensurable (KPCuspArithmetic.projectiveAutomorphisms F M))
    (q : KPCuspArithmetic.Cusp F)
    (σ : KPCuspArithmetic.PGL2 F) (hσ : σ • KPCuspArithmetic.infinity F = q) :
    let S := KPCuspArithmetic.conjugatedStabilizer F Γ q σ
    (∀ g ∈ S, KPCuspArithmetic.IsUpperTriangular F g) ∧
    ∃ (L : AddSubgroup F) (E : Subgroup Fˣ)
      (ι : Multiplicative L →* S) (ρ : S →* E)
      (hE : E ≤ KPCuspArithmetic.rationalUnits F),
      (E.subgroupOf (KPCuspArithmetic.rationalUnits F)).FiniteIndex ∧
      Function.Injective ι ∧ Function.Surjective ρ ∧ ι.range = ρ.ker ∧
      (∀ (x : L) (A : Matrix.GeneralLinearGroup (Fin 2) F),
        Matrix.ProjGenLinGroup.mk A =
          (ι (Multiplicative.ofAdd x) : KPCuspArithmetic.PGL2 F) →
        (A : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 ∧
        (A : Matrix (Fin 2) (Fin 2) F) 0 0 = (A : Matrix (Fin 2) (Fin 2) F) 1 1 ∧
        (A : Matrix (Fin 2) (Fin 2) F) 0 1 =
          (x : F) * (A : Matrix (Fin 2) (Fin 2) F) 0 0) ∧
      (∀ (g : S) (A : Matrix.GeneralLinearGroup (Fin 2) F),
        Matrix.ProjGenLinGroup.mk A = (g : KPCuspArithmetic.PGL2 F) →
        (A : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 →
        (A : Matrix (Fin 2) (Fin 2) F) 0 0 = ((ρ g : Fˣ) : F) *
          (A : Matrix (Fin 2) (Fin 2) F) 1 1) ∧
      (∀ (u : E) (x : F), x ∈ L → ((u : Fˣ) : F) * x ∈ L) ∧
      (∃ hdisc : DiscreteTopology (KPCuspLogShape.horizontalLattice F L).toIntSubmodule,
        letI := hdisc
        IsZLattice ℝ (KPCuspLogShape.horizontalLattice F L).toIntSubmodule) ∧
      let ell := KPCuspLogShape.logarithm F hF E hE
      let Λ := KPCuspLogShape.logLattice F hF E hE
      let T := NumberField.mixedEmbedding.mixedSpace F ⧸
        KPCuspLogShape.horizontalLattice F L
      CompactSpace T ∧
      (∀ (g : S) (A : Matrix.GeneralLinearGroup (Fin 2) F)
        (z : KPArch.Space (KPCuspLogShape.dimension F)),
        Matrix.ProjGenLinGroup.mk A = (g : KPCuspArithmetic.PGL2 F) →
        (A : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 →
        let Az := KPArch.productAction (KPCuspLogShape.dimension F)
          (fun i => Matrix.GeneralLinearGroup.map (KPCusp.complexPlace F i).embedding A) z
        KPCuspLogShape.meanHeight (KPCuspLogShape.dimension F) Az =
          KPCuspLogShape.meanHeight (KPCuspLogShape.dimension F) z ∧
        KPCuspLogShape.shapeCoordinates (KPCuspLogShape.dimension F) Az =
          KPCuspLogShape.shapeCoordinates (KPCuspLogShape.dimension F) z +
            KPCuspLogShape.logRatio F E (Additive.ofMul (ρ g))) ∧
      (∃ β : S → T → T,
        (∀ x : T, β 1 x = x) ∧
        (∀ (g h : S) (x : T), β (g * h) x = β g (β h x)) ∧
        (∀ g : S, Continuous (β g)) ∧
        (∀ (g : S) (A : Matrix.GeneralLinearGroup (Fin 2) F)
          (x : NumberField.mixedEmbedding.mixedSpace F),
          Matrix.ProjGenLinGroup.mk A = (g : KPCuspArithmetic.PGL2 F) →
          (A : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 →
          β g (QuotientAddGroup.mk x) = QuotientAddGroup.mk
            (NumberField.mixedEmbedding F ((ρ g : Fˣ) : F) * x +
              NumberField.mixedEmbedding F
                ((A : Matrix (Fin 2) (Fin 2) F) 0 1 /
                  (A : Matrix (Fin 2) (Fin 2) F) 1 1)))) ∧
      (∃ hdisc : DiscreteTopology Λ, letI := hdisc; IsZLattice ℝ Λ) ∧
      CompactSpace (KPCuspLogShape.hyperplane (KPCuspLogShape.dimension F) ⧸
        Λ.toAddSubgroup) ∧
      (∃ B : Basis (Fin (KPCuspLogShape.dimension F - 1)) ℝ
          (KPCuspLogShape.hyperplane (KPCuspLogShape.dimension F)),
        Submodule.span ℤ (Set.range B) = Λ ∧ IsCompact (parallelepiped B) ∧
        (∀ b : KPCuspLogShape.hyperplane (KPCuspLogShape.dimension F),
          ∃ u : E, b - ell (Additive.ofMul u) ∈ parallelepiped B)) ∧
      Finite ell.ker ∧
      ∃ α : E →* Multiplicative (AddAut T),
        (∀ u : E, Continuous ((α u).toAdd)) ∧
        (∀ (u : E) (x : NumberField.mixedEmbedding.mixedSpace F),
          (α u).toAdd (QuotientAddGroup.mk x) = QuotientAddGroup.mk
            (NumberField.mixedEmbedding F ((u : Fˣ) : F) * x)) ∧
        (∀ u : E, ell (Additive.ofMul u) = 0 →
          ∀ z : KPArch.Space (KPCuspLogShape.dimension F),
            KPCuspLogShape.shapeCoordinates (KPCuspLogShape.dimension F)
              (KPCuspLogShape.ratioAction F E u z) =
            KPCuspLogShape.shapeCoordinates (KPCuspLogShape.dimension F) z) := by
  obtain ⟨hupper, J, L, E, ι, ρ, hJ, hL, hLindex, hhor, hE, hindex,
    hinj, hsurj, hexact, hiota, hratio⟩ :=
    kp_cusp_arithmetic_parabolic_stabilizers F M hM Γ hΓ hcomm q σ hσ
  have hstable := KPCuspLogShape.ExactSequence.actual_translation_lattice_stable F
    (KPCuspArithmetic.conjugatedStabilizer F Γ q σ) hupper L E ι ρ hsurj hexact hiota hratio
  obtain ⟨hlog, hcompact, hfinite, hmean, hshape, B, hspan, hBcompact, hBcover, hbound⟩ :=
    kp_cusp_log_unit_shape F hF E hE hindex
  obtain ⟨α, hαcont, hαformula⟩ := KPCuspLogShape.torus_unit_action F L E hstable
  obtain ⟨β, hβone, hβmul, hβcont, hβformula⟩ :=
    KPCuspLogShape.AffineTorus.exists_affine_torus_action F
      (KPCuspArithmetic.conjugatedStabilizer F Γ q σ) E ρ hupper hratio L hstable
  have hTcompact : CompactSpace (NumberField.mixedEmbedding.mixedSpace F ⧸
      KPCuspLogShape.horizontalLattice F L) := by
    change ∃ hdisc : DiscreteTopology (KPCuspLogShape.horizontalLattice F L).toIntSubmodule,
      letI := hdisc; IsZLattice ℝ (KPCuspLogShape.horizontalLattice F L).toIntSubmodule at hhor
    obtain ⟨hdisc, hfull⟩ := hhor
    letI := hdisc
    letI := hfull
    exact KPCuspLogShape.compact_quotient_of_isZLattice
      (KPCuspLogShape.horizontalLattice F L).toIntSubmodule
  refine ⟨hupper, L, E, ι, ρ, hE, hindex, hinj, hsurj, hexact,
    hiota, hratio, hstable, ?_, hTcompact, ?_, ⟨β, hβone, hβmul, hβcont, hβformula⟩,
    hlog, hcompact, ?_, hfinite, ⟨α, hαcont, hαformula, hshape⟩⟩
  · exact hhor
  · intro g A z hA hzero
    exact KPCuspLogShape.actual_upper_height_shape F hF E hE (ρ g) A hzero
      (hratio g A hA hzero) z
  · exact ⟨B, hspan, hBcompact, hBcover⟩

end DedekindZetaZeroFree

end
end
