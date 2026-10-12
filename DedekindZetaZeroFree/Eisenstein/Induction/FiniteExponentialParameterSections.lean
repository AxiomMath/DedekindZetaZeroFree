module

public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.LocalCompactHolomorphicModel

@[expose] public section

noncomputable section
open scoped Classical BigOperators
namespace DedekindZetaZeroFree.KPGlobalResidualConstruction.StandardIntertwinerProducers.NonzeroResidue.FiniteSourceTransport
open KPLocalPrincipalSeries KPLocalStoneVonNeumann
variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
variable {G H D : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [CommGroup D] [Finite D]
variable {T : LocalHeisenbergData H D}
variable (A : LocalBorelData (K := K) (G := G) T) (I J : IwasawaData A)
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

def localLogNorm (g : G) : ℝ :=
  Real.log (localAbs K (A.coordinate (A.retract (J.borelPart g))))

private theorem decomposition_norm_unique
    (b c : A.B) (k l : J.compact.toOpenSubgroup)
    (h : (b : G) * (k : G) = (c : G) * (l : G)) :
    localAbs K (A.coordinate (A.retract b)) =
      localAbs K (A.coordinate (A.retract c)) := by
  have he : ((c⁻¹ * b : A.B) : G) = (l : G) * (k : G)⁻¹ := by
    have h' := congrArg (fun g : G => (c : G)⁻¹ * g * (k : G)⁻¹) h
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv, mul_assoc,
      mul_inv_cancel, mul_one, inv_mul_cancel_left] using h'
  have hm : ((c⁻¹ * b : A.B) : G) ∈ J.compact.toOpenSubgroup := by
    rw [he]
    exact J.compact.toOpenSubgroup.mul_mem l.property
      (J.compact.toOpenSubgroup.inv_mem k.property)
  have hn := J.intersection_norm (c⁻¹ * b) hm
  have hmul : localAbs K (A.coordinate (A.retract c)) *
      localAbs K (A.coordinate (A.retract (c⁻¹ * b))) =
      localAbs K (A.coordinate (A.retract b)) := by
    rw [← localAbs_mul, ← map_mul, ← map_mul, mul_inv_cancel_left]
  rw [hn,mul_one] at hmul
  exact hmul.symm

theorem localLogNorm_borel_mul (b : A.B) (g : G) :
    localLogNorm A J ((b : G) * g) =
      Real.log (localAbs K (A.coordinate (A.retract b))) + localLogNorm A J g := by
  have hn := decomposition_norm_unique A J (J.borelPart ((b : G) * g))
    (b * J.borelPart g) (J.compactPart ((b : G) * g)) (J.compactPart g) (by
      rw [← J.decomposition, Subgroup.coe_mul, mul_assoc, ← J.decomposition])
  unfold localLogNorm
  rw [hn,map_mul,map_mul,localAbs_mul,Real.log_mul
    (localAbs_pos K _).ne' (localAbs_pos K _).ne']

theorem localLogNorm_mul_compact (g : G) (k : J.compact.toOpenSubgroup) :
    localLogNorm A J (g * (k : G)) = localLogNorm A J g := by
  have hn := decomposition_norm_unique A J (J.borelPart (g * (k : G)))
    (J.borelPart g) (J.compactPart (g * (k : G))) (J.compactPart g * k) (by
      rw [← J.decomposition, Subgroup.coe_mul, ← mul_assoc, ← J.decomposition])
  exact congrArg Real.log hn

theorem localLogNorm_locallyConstant : IsLocallyConstant (localLogNorm A J) := by
  apply (IsLocallyConstant.iff_exists_open _).mpr
  intro g
  let U : Set G := {h | g⁻¹ * h ∈ J.compact.toOpenSubgroup}
  refine ⟨U, ?_, ?_, ?_⟩
  · exact J.compact.toOpenSubgroup.isOpen.preimage (continuous_const.mul continuous_id)
  · change g⁻¹ * g ∈ J.compact.toOpenSubgroup
    simp
  · intro h hh
    let k : J.compact.toOpenSubgroup := ⟨g⁻¹ * h, hh⟩
    have he : h = g * (k : G) := by dsimp [k]; group
    rw [he]
    exact localLogNorm_mul_compact A J g k

def normValues : Finset ℝ := by
  letI : CompactSpace I.compact.toOpenSubgroup :=
    isCompact_iff_compactSpace.mp I.compact.isCompact
  have h : IsLocallyConstant (fun k : I.compact.toOpenSubgroup => localLogNorm A J (k : G)) :=
    (localLogNorm_locallyConstant A J).comp_continuous continuous_subtype_val
  exact h.range_finite.toFinset

private theorem mem_normValues (k : I.compact.toOpenSubgroup) :
    localLogNorm A J (k : G) ∈ normValues A I J := by
  unfold normValues
  simp only [Set.Finite.mem_toFinset]
  exact ⟨k,rfl⟩

 theorem norm_fiber_compact_covariance (b : A.B)
    (k k' : I.compact.toOpenSubgroup) (h : (k' : G) = (b : G) * (k : G)) :
    localLogNorm A J (k' : G) = localLogNorm A J (k : G) := by
  have hb : (b : G) ∈ I.compact.toOpenSubgroup := by
    have he : (b : G) = (k' : G) * (k : G)⁻¹ := by rw [h]; group
    rw [he]
    exact I.compact.toOpenSubgroup.mul_mem k'.property
      (I.compact.toOpenSubgroup.inv_mem k.property)
  rw [h,localLogNorm_borel_mul, I.intersection_norm b hb, Real.log_one, zero_add]

def normPiece (P : Polarization T) (ε : Sign)
    (φ : compactPicture A P I ε) (r : ℝ) : compactPicture A P I ε := by
  refine ⟨fun k => if localLogNorm A J (k : G) = r then φ.val k else 0, ?_, ?_⟩
  · intro b k k' h
    dsimp only
    rw [norm_fiber_compact_covariance A I J b k k' h]
    split_ifs
    · exact φ.property.1 b k k' h
    · exact (map_zero _).symm
  · obtain ⟨L,hL⟩ := φ.property.2
    let U : OpenSubgroup I.compact.toOpenSubgroup :=
      J.compact.toOpenSubgroup.comap I.compact.toOpenSubgroup.subtype continuous_subtype_val
    refine ⟨L ⊓ U, ?_⟩
    intro j hj
    funext k
    change (if localLogNorm A J (((k*j : I.compact.toOpenSubgroup) : G)) = r
      then φ.val (k*j) else 0) = _
    have hn := localLogNorm_mul_compact A J (k : G) ⟨(j : G),hj.2⟩
    have hp := congrFun (hL j hj.1) k
    change φ.val (k*j) = φ.val k at hp
    rw [show (((k*j : I.compact.toOpenSubgroup) : G)) = (k:G)*(j:G) from rfl,
      hn,hp]

def parameterSource (P : Polarization T) (ε : Sign)
    (φ : compactPicture A P I ε) (s : ℂ) : compactPicture A P I ε :=
  (compactTrivialization A P I ε s).symm
    (compactTrivialization A P J ε s
      ((compactTrivialization A P J ε 0).symm
        (compactTrivialization A P I ε 0 φ)))

theorem parameterSource_zero (P : Polarization T) (ε : Sign)
    (φ : compactPicture A P I ε) : parameterSource A I J P ε φ 0 = φ := by
  unfold parameterSource
  rw [LinearEquiv.apply_symm_apply,LinearEquiv.symm_apply_apply]

theorem parameterSource_extension (P : Polarization T) (ε : Sign)
    (φ : compactPicture A P I ε) (s : ℂ) (g : G) :
    (compactTrivialization A P I ε s (parameterSource A I J P ε φ s)).val g =
      Complex.exp (s * (localLogNorm A J g : ℂ)) •
        (compactTrivialization A P I ε 0 φ).val g := by
  unfold parameterSource
  rw [LinearEquiv.apply_symm_apply]
  let σ := (compactTrivialization A P J ε 0).symm
    (compactTrivialization A P I ε 0 φ)
  have hz : compactTrivialization A P J ε 0 σ = compactTrivialization A P I ε 0 φ :=
    LinearEquiv.apply_symm_apply _ _
  rw [← hz, LinearEquiv.symm_apply_apply]
  change (inducingScalar A s (J.borelPart g)) •
    (borelAction A P ε (J.borelPart g)) (σ.val (J.compactPart g)) = _
  change _ = Complex.exp (s * (localLogNorm A J g : ℂ)) •
    ((inducingScalar A 0 (J.borelPart g)) •
      (borelAction A P ε (J.borelPart g)) (σ.val (J.compactPart g)))
  simp only [inducingScalar, normPower, zero_mul, Complex.exp_zero, mul_one, smul_smul]
  rw [mul_comm]
  rfl

theorem parameterSource_finite_expansion (P : Polarization T) (ε : Sign)
    (φ : compactPicture A P I ε) (s : ℂ) :
    parameterSource A I J P ε φ s =
      ∑ r ∈ normValues A I J, Complex.exp (s * (r : ℂ)) • normPiece A I J P ε φ r := by
  apply Subtype.ext
  funext k
  have he := parameterSource_extension A I J P ε φ s (k : G)
  have hv : ∀ (t : ℂ) (ψ : compactPicture A P I ε),
      (compactTrivialization A P I ε t ψ).val (k : G) = ψ.val k := by
    intro t ψ
    change inducingAction A P ε t (I.borelPart (k:G)) (ψ.val (I.compactPart (k:G))) = _
    rw [I.borelPart_compact, I.compactPart_compact,map_one]
    rfl
  rw [hv,hv] at he
  rw [he]
  simp only [Submodule.coe_sum, Finset.sum_apply, Submodule.coe_smul,
    Pi.smul_apply, normPiece]
  rw [Finset.sum_eq_single (localLogNorm A J (k:G))]
  · simp
  · intro r hr hne
    simp [Ne.symm hne]
  · exact fun h => (h (mem_normValues A I J k)).elim

end DedekindZetaZeroFree.KPGlobalResidualConstruction.StandardIntertwinerProducers.NonzeroResidue.FiniteSourceTransport

end
