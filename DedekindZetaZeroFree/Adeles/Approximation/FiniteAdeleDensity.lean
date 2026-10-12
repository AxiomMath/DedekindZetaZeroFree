module

public import DedekindZetaZeroFree.Adeles.Approximation.SIntegerFiniteStrongApproximation

@[expose] public section

noncomputable section

namespace DedekindZetaZeroFree.KPAdelicTopology

open NumberField IsDedekindDomain Topology

set_option backward.isDefEq.respectTransparency false in

theorem finiteAdeles_diagonal_denseRange (F : Type) [Field F] [NumberField F] :
    DenseRange (algebraMap F (FiniteAdeles F)) := by
  classical
  apply dense_iff_inter_open.mpr
  intro U hU hUne
  obtain ⟨a, ha⟩ := hUne
  let X := fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F
  let C := fun v : HeightOneSpectrum (𝓞 F) => (v.adicCompletionIntegers F : Set (X v))
  have hs : {v | a v ∉ v.adicCompletionIntegers F}.Finite := a.2
  let s := hs.toFinset
  have hsc : Filter.cofinite ≤ Filter.principal (↑s : Set (HeightOneSpectrum (𝓞 F)))ᶜ := by
    rw [Filter.le_principal_iff]
    exact s.finite_toSet.compl_mem_cofinite
  let inc := RestrictedProduct.inclusion X C hsc
  let a' : RestrictedProduct X C (Filter.principal (↑s : Set _)ᶜ) :=
    ⟨a.1, by
      intro v hv
      change a v ∈ v.adicCompletionIntegers F
      simpa only [Set.mem_compl_iff, Finset.mem_coe, s, hs.mem_toFinset,
        Set.mem_setOf_eq, not_not] using hv⟩
  have ha' : a' ∈ inc ⁻¹' U := ha
  have hopen : IsOpen (inc ⁻¹' U) := hU.preimage (RestrictedProduct.continuous_inclusion hsc)
  obtain ⟨V, hV, hVU⟩ :=
    RestrictedProduct.isEmbedding_coe_of_principal.toIsInducing.isOpen_iff.mp hopen
  have haV : a.1 ∈ V := by
    have h : a' ∈ DFunLike.coe ⁻¹' V := by rw [hVU]; exact ha'
    exact h
  obtain ⟨t, u, hu, huV⟩ := isOpen_pi_iff.mp hV a.1 haV
  let S := s ∪ t
  let W (v : S) : Set (X v.val) :=
    (if v.val ∈ t then u v.val else Set.univ) ∩
      (if v.val ∈ s then Set.univ else C v.val)
  have hW : IsOpen (Set.univ.pi W) := by
    apply isOpen_set_pi Set.finite_univ
    intro v _
    apply IsOpen.inter
    · by_cases hv : v.val ∈ t
      · simpa [W, hv] using (hu v.val hv).1
      · simp [hv]
    · by_cases hv : v.val ∈ s
      · simp [hv]
      · simpa [hv, C] using completionIntegers_isOpen F v.val
  have haW : (fun v : S => a v.val) ∈ Set.univ.pi W := by
    intro v _
    constructor
    · by_cases hv : v.val ∈ t
      · change a.1 v.val ∈ (if v.val ∈ t then u v.val else Set.univ)
        simpa only [if_pos hv] using (hu v.val hv).2
      · simp [hv]
    · by_cases hv : v.val ∈ s
      · simp [hv]
      · change a v.val ∈ (if v.val ∈ s then Set.univ else C v.val)
        rw [if_neg hv]
        change a v.val ∈ v.val.adicCompletionIntegers F
        simpa only [s, hs.mem_toFinset, Set.mem_setOf_eq, not_not] using hv
  obtain ⟨m, hm⟩ := (PoissonSFiniteDensity.diagonal_denseRange F S).exists_mem_open hW ⟨_, haW⟩
  have hmC : ∀ v : HeightOneSpectrum (𝓞 F), v ∉ s →
      algebraMap F (X v) (m : F) ∈ C v := by
    intro v hv
    by_cases hvS : v ∈ S
    · have h := (hm ⟨v, hvS⟩ (Set.mem_univ _)).2
      simpa [W, hv, PoissonSFiniteDensity.diagonal_apply] using h
    · exact (mem_sIntegerRing_iff F S (m : F)).mp m.property v hvS
  let d : RestrictedProduct X C (Filter.principal (↑s : Set _)ᶜ) :=
    ⟨fun v => algebraMap F (X v) (m : F), hmC⟩
  have hdV : d.1 ∈ V := by
    apply huV
    intro v hv
    have hvS : v ∈ S := Finset.mem_union.mpr (Or.inr hv)
    have h := (hm ⟨v, hvS⟩ (Set.mem_univ _)).1
    change algebraMap F (X v) (m : F) ∈ u v
    change algebraMap F (X v) (m : F) ∈ (if v ∈ t then u v else Set.univ) at h
    have hv' : v ∈ t := hv
    rw [if_pos hv'] at h
    exact h
  have hdU : inc d ∈ U := by
    change d ∈ inc ⁻¹' U
    rw [← hVU]
    exact hdV
  refine ⟨algebraMap F (FiniteAdeles F) (m : F), ?_, ⟨(m : F), rfl⟩⟩
  exact hdU

theorem exists_integral_remainder (F : Type) [Field F] [NumberField F]
    (a : FiniteAdeles F) :
    ∃ r : F, a - algebraMap F (FiniteAdeles F) r ∈ integralAdeles F := by
  let U := {b : FiniteAdeles F | a - b ∈ integralAdeles F}
  have hU : IsOpen U := (integralAdeles_isOpen F).preimage (continuous_const.sub continuous_id)
  have ha : a ∈ U := by
    change a - a ∈ integralAdeles F
    rw [sub_self]
    exact (integralAdeles F).zero_mem
  obtain ⟨r, hr⟩ := (finiteAdeles_diagonal_denseRange F).exists_mem_open hU ⟨a, ha⟩
  exact ⟨r, hr⟩

end DedekindZetaZeroFree.KPAdelicTopology

end
