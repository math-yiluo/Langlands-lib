/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.Algebra.Homology.Embedding.Extend
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
public import Mathlib.LinearAlgebra.ExteriorPower.Basic
public import WeilConjectures.AlgebraicGeometry.KoszulComplex
import Mathlib.Algebra.Homology.Embedding.ExtendHomology
import Mathlib.RingTheory.Finiteness.Ideal
import all WeilConjectures.RingTheory.KoszulProjectiveResolution

/-!
# Cohomology of the strict Koszul augmentation cones

Source: Stacks Project, Tag 0921.
(auxiliary; not a blueprint node).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits
open scoped Pointwise

namespace ExteriorAlgebra

private theorem cochain_homologyMap_zero_of_cycles_to_boundaries
    (A : Type u) [CommRing A] {K L : CochainComplex (ModuleCat.{u} A) ℤ}
    (f : K ⟶ L) (j : ℤ)
    (hf : ∀ z : K.cycles j, ∃ w : L.X (j - 1),
      L.d (j - 1) j w = f.f j (K.iCycles j z)) :
    HomologicalComplex.homologyMap f j = 0 := by
  apply (cancel_epi (K.homologyπ j)).mp
  apply (cancel_mono (L.homologyι j)).mp
  simp only [comp_zero, zero_comp, Category.assoc]
  change (K.sc j).homologyπ ≫ ShortComplex.homologyMap
    ((HomologicalComplex.shortComplexFunctor _ _ j).map f) ≫ (L.sc j).homologyι = 0
  rw [ShortComplex.π_homologyMap_ι]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  obtain ⟨w, hw⟩ := hf z
  change L.pOpcycles j (f.f j (K.iCycles j z)) = 0
  rw [← hw]
  exact congrArg (fun φ ↦ φ w) (L.d_pOpcycles (j - 1) j)

private theorem cochain_boundary_of_homologyMap_zero
    (A : Type u) [CommRing A] {K L : CochainComplex (ModuleCat.{u} A) ℤ}
    (f : K ⟶ L) (i j : ℤ) (hij : i + 1 = j)
    (hf : HomologicalComplex.homologyMap f j = 0)
    (x : K.X j) (hx : K.d j (j + 1) x = 0) :
    ∃ w : L.X i, L.d i j w = f.f j x := by
  have hn : (ComplexShape.up ℤ).next j = j + 1 :=
    (ComplexShape.up ℤ).next_eq' rfl
  have hp : (ComplexShape.up ℤ).prev j = i :=
    (ComplexShape.up ℤ).prev_eq' hij
  have hx' : (K.sc j).g x = 0 := by
    change K.d j ((ComplexShape.up ℤ).next j) x = 0
    rw [hn]
    exact hx
  let z := (K.sc j).moduleCatCyclesIso.inv ⟨x, hx'⟩
  have hiz : K.iCycles j z = x := by
    exact congrArg (fun φ ↦ φ ⟨x, hx'⟩) (K.sc j).moduleCatCyclesIso_inv_iCycles
  have hz : K.iCycles j ≫ f.f j ≫ L.pOpcycles j = 0 := by
    change (K.sc j).iCycles ≫
      ((HomologicalComplex.shortComplexFunctor _ _ j).map f).τ₂ ≫
        (L.sc j).pOpcycles = 0
    rw [← ShortComplex.π_homologyMap_ι
      ((HomologicalComplex.shortComplexFunctor _ _ j).map f)]
    change K.homologyπ j ≫ HomologicalComplex.homologyMap f j ≫ L.homologyι j = 0
    rw [hf, zero_comp, comp_zero]
  have hz' := congrArg (fun φ ↦ φ z) hz
  simp only [ModuleCat.comp_apply, hiz] at hz'
  let S := ShortComplex.mk (L.d i j) (L.pOpcycles j) (L.d_pOpcycles i j)
  have hS : S.Exact := S.exact_of_g_is_cokernel (L.opcyclesIsCokernel _ _ hp)
  exact (S.moduleCat_exact_iff.mp hS) _ hz'

private theorem cone_inl_map (A : Type u) [CommRing A]
    {F G F' G' : CochainComplex (ModuleCat.{u} A) ℤ}
    (φ : F ⟶ G) (φ' : F' ⟶ G') (α : Arrow.mk φ ⟶ Arrow.mk φ') (j : ℤ) :
    HomologicalComplex.homotopyCofiber.inlX φ (j + 1) j rfl ≫
        (HomologicalComplex.homotopyCofiber.mapArrowHom φ φ'
          (fun j : ℤ ↦ ⟨j - 1, sub_add_cancel j 1⟩) α).f j =
      α.left.f (j + 1) ≫ HomologicalComplex.homotopyCofiber.inlX φ' (j + 1) j rfl := by
  simp [HomologicalComplex.homotopyCofiber.mapArrowHom,
    HomologicalComplex.homotopyCofiber.inrCompHomotopy_hom]

private theorem cone_fst_inl (A : Type u) [CommRing A]
    {F G : CochainComplex (ModuleCat.{u} A) ℤ} (φ : F ⟶ G) (j : ℤ)
    (hG : IsZero (G.X j)) :
    HomologicalComplex.homotopyCofiber.fstX φ j (j + 1) rfl ≫
      HomologicalComplex.homotopyCofiber.inlX φ (j + 1) j rfl = 𝟙 _ := by
  apply HomologicalComplex.homotopyCofiber.ext_to_X φ j (j + 1) rfl
  · simp
  · exact hG.eq_of_tgt _ _

private theorem cone_homologyMap_zero_of_boundaries (A : Type u) [CommRing A]
    {F G F' G' : CochainComplex (ModuleCat.{u} A) ℤ}
    (φ : F ⟶ G) (φ' : F' ⟶ G') (α : Arrow.mk φ ⟶ Arrow.mk φ') (j : ℤ)
    (hG : IsZero (G.X j)) (hG' : IsZero (G'.X j))
    (hf : ∀ x : F.X (j + 1), F.d (j + 1) (j + 1 + 1) x = 0 →
      φ.f (j + 1) x = 0 → ∃ w : F'.X j,
        F'.d j (j + 1) w = α.left.f (j + 1) x) :
    HomologicalComplex.homologyMap
      (HomologicalComplex.homotopyCofiber.mapArrowHom φ φ'
        (fun j : ℤ ↦ ⟨j - 1, sub_add_cancel j 1⟩) α) j = 0 := by
  apply cochain_homologyMap_zero_of_cycles_to_boundaries A
  intro z
  let C := HomologicalComplex.homotopyCofiber φ
  let x : F.X (j + 1) := HomologicalComplex.homotopyCofiber.fstX φ j (j + 1) rfl
    (C.iCycles j z)
  have hx : F.d (j + 1) (j + 1 + 1) x = 0 := by
    have hh := congrArg (fun f ↦ f (C.iCycles j z))
      (HomologicalComplex.homotopyCofiber.d_fstX φ j (j + 1) (j + 1 + 1) rfl rfl)
    have hz := congrArg (fun f ↦ f z) (C.iCycles_d j (j + 1))
    simp only [ModuleCat.comp_apply] at hz hh
    change _ = -(F.d (j + 1) (j + 1 + 1) x) at hh
    change HomologicalComplex.homotopyCofiber.d φ j (j + 1) (C.iCycles j z) = 0 at hz
    rw [hz, map_zero] at hh
    exact neg_eq_zero.mp hh.symm
  have hφ : φ.f (j + 1) x = 0 := by
    have hs : HomologicalComplex.homotopyCofiber.sndX φ j = 0 := hG.eq_of_tgt _ _
    have hh := congrArg (fun f ↦ f (C.iCycles j z))
      (HomologicalComplex.homotopyCofiber.d_sndX φ j (j + 1) rfl)
    rw [hs, zero_comp, add_zero] at hh
    have hz := congrArg (fun f ↦ f z) (C.iCycles_d j (j + 1))
    simp only [ModuleCat.comp_apply] at hz hh
    change HomologicalComplex.homotopyCofiber.d φ j (j + 1) (C.iCycles j z) = 0 at hz
    rw [hz, map_zero] at hh
    exact hh.symm
  obtain ⟨w, hw'⟩ := hf x hx hφ
  refine ⟨-HomologicalComplex.homotopyCofiber.inlX φ' j (j - 1)
    (by change j - 1 + 1 = j; omega) w, ?_⟩
  have hd := congrArg (fun f ↦ f w)
    (HomologicalComplex.homotopyCofiber.inlX_d φ' (j - 1) j (j + 1)
      (by change j - 1 + 1 = j; omega) rfl)
  have hz : HomologicalComplex.homotopyCofiber.inlX φ (j + 1) j rfl x =
      C.iCycles j z := congrArg (fun f ↦ f (C.iCycles j z)) (cone_fst_inl A φ j hG)
  have hm := congrArg (fun f ↦ f x) (cone_inl_map A φ φ' α j)
  simp only [ModuleCat.comp_apply] at hd hm
  have he : φ'.f j = 0 := hG'.eq_of_tgt _ _
  change (HomologicalComplex.homotopyCofiber φ').d (j - 1) j
    (HomologicalComplex.homotopyCofiber.inlX φ' j (j - 1) _ w) =
      -HomologicalComplex.homotopyCofiber.inlX φ' (j + 1) j rfl
        (F'.d j (j + 1) w) +
      HomologicalComplex.homotopyCofiber.inrX φ' j (φ'.f j w) at hd
  have he' : φ'.f j w = 0 := by rw [he]; rfl
  rw [he', map_zero, add_zero] at hd
  rw [map_neg, hd, neg_neg, hw']
  exact hm.symm.trans (congrArg
    ((HomologicalComplex.homotopyCofiber.mapArrowHom φ φ'
      (fun j : ℤ ↦ ⟨j - 1, sub_add_cancel j 1⟩) α).f j) hz)

private theorem extend_positive_isZero (A : Type u) [CommRing A]
    (K : ChainComplex (ModuleCat.{u} A) ℕ) (j : ℤ) (hj : 0 < j) :
    IsZero ((K.extend ComplexShape.embeddingDownNat).X j) := by
  apply K.isZero_extend_X
  intro n hn
  change -(n : ℤ) = j at hn
  omega

private theorem single_extend_isZero (A : Type u) [CommRing A]
    (M : ModuleCat.{u} A) (j : ℤ) (hj : j ≠ 0) :
    IsZero ((((ChainComplex.single₀ (ModuleCat.{u} A)).obj M).extend
      ComplexShape.embeddingDownNat).X j) := by
  let S := (ChainComplex.single₀ (ModuleCat.{u} A)).obj M
  by_cases he : ∃ n : ℕ, -(n : ℤ) = j
  · obtain ⟨n, rfl⟩ := he
    exact (HomologicalComplex.isZero_single_obj_X (.down ℕ) 0 M n
      (by intro hn; subst n; exact hj rfl)).of_iso
        (S.extendXIso ComplexShape.embeddingDownNat rfl)
  · apply S.isZero_extend_X
    intro n hn
    exact he ⟨n, hn⟩

private theorem cone_boundary_of_epi (A : Type u) [CommRing A]
    {F G : CochainComplex (ModuleCat.{u} A) ℤ} (φ : F ⟶ G) (j : ℤ)
    (hF : IsZero (F.X (j + 1))) [Epi (φ.f j)]
    (z : (HomologicalComplex.homotopyCofiber φ).X j) :
    ∃ w : (HomologicalComplex.homotopyCofiber φ).X (j - 1),
      (HomologicalComplex.homotopyCofiber φ).d (j - 1) j w = z := by
  have hid : HomologicalComplex.homotopyCofiber.sndX φ j ≫
      HomologicalComplex.homotopyCofiber.inrX φ j = 𝟙 _ := by
    apply HomologicalComplex.homotopyCofiber.ext_to_X φ j (j + 1) rfl
    · exact hF.eq_of_tgt _ _
    · simp
  obtain ⟨x, hx⟩ := (ModuleCat.epi_iff_surjective (φ.f j)).mp inferInstance
    (HomologicalComplex.homotopyCofiber.sndX φ j z)
  refine ⟨HomologicalComplex.homotopyCofiber.inlX φ j (j - 1)
    (by change j - 1 + 1 = j; omega) x, ?_⟩
  have hd := HomologicalComplex.homotopyCofiber.inlX_d φ (j - 1) j (j + 1)
    (by change j - 1 + 1 = j; omega) rfl
  have hh := congrArg (fun f ↦ f x) hd
  change (HomologicalComplex.homotopyCofiber φ).d (j - 1) j
    (HomologicalComplex.homotopyCofiber.inlX φ j (j - 1) _ x) =
      -HomologicalComplex.homotopyCofiber.inlX φ (j + 1) j rfl
        (F.d j (j + 1) x) +
      HomologicalComplex.homotopyCofiber.inrX φ j (φ.f j x) at hh
  have hz : F.d j (j + 1) x = 0 := congrArg (fun f ↦ f x) (hF.eq_of_tgt (F.d j (j + 1)) 0)
  rw [hz, map_zero, neg_zero, zero_add, hx] at hh
  exact hh.trans (congrArg (fun f ↦ f z) hid)

private theorem koszulBoundary_zero_range (A : Type u) [CommRing A] (r : ℕ)
    (f : Fin r → A) (x : ⋀[A]^0 (Fin r →₀ A))
    (hx : exteriorPower.zeroEquiv A (Fin r →₀ A) x ∈ Ideal.span (Set.range f)) :
    ∃ y : ⋀[A]^1 (Fin r →₀ A), koszulBoundary A r f 0 y = x := by
  change exteriorPower.zeroEquiv A (Fin r →₀ A) x ∈ Submodule.span A (Set.range f) at hx
  rw [← Finsupp.range_linearCombination] at hx
  obtain ⟨y, hy⟩ := hx
  refine ⟨(exteriorPower.oneEquiv A (Fin r →₀ A)).symm y, ?_⟩
  apply (exteriorPower.zeroEquiv A (Fin r →₀ A)).injective
  rw [koszulBoundary_zero_quotient_formula, LinearEquiv.apply_symm_apply]
  exact hy

private theorem power_ideals_cofinal (A : Type u) [CommRing A] (r : ℕ)
    (a : Fin r → A) (m : ℕ) : ∃ s : ℕ,
    (Ideal.span (Set.range a)) ^ s ≤ Ideal.span (Set.range (fun i ↦ a i ^ (m + 1))) := by
  apply Ideal.exists_pow_le_of_le_radical_of_fg
  · apply Ideal.span_le.mpr
    rintro x ⟨i, rfl⟩
    exact ⟨m + 1, Ideal.subset_span (Set.mem_range_self i)⟩
  · exact Submodule.fg_span (Set.finite_range a)

/-- Cohomology transitions of the strict power Koszul augmentation cones are eventually zero.
Source: Stacks Project, Tags 0921 and 0922.
(auxiliary; not a blueprint node).

Proof: the cone has H^0=0 because the augmentation is surjective in degree zero.
For j <= -2 its cohomology is the positive Koszul homology in degree -j-1,
naturally in strict augmentation squares, and the supplied positive-homology
vanishing therefore kills its transitions. In degree -1 it is I^(m+1)/J_m,
where J_m is generated by the a_i^(m+1). The transition is induced by inclusion
of ideal powers. Each generator of I lies in the radical of J_m; finite generation
therefore gives an exponent s with I^s <= J_m. Choose k=m+s to kill this map.
Positive degrees vanish because all cone terms do.
These descriptions remain valid for an empty sequence, zero ring, and unit ideal. -/
theorem koszul_cone_homology_transition_pro_zero
    (A : Type u) [CommRing A] (r : ℕ) (a : Fin r → A)
    (ε : ∀ m : ℕ, koszulComplex A r (fun i ↦ a i ^ (m + 1)) ⟶
      (ChainComplex.single₀ (ModuleCat.{u} A)).obj
        (ModuleCat.of A (A ⧸ (Ideal.span (Set.range a)) ^ (m + 1))))
    (t : ∀ m k : ℕ, m ≤ k →
      (koszulComplex A r (fun i ↦ a i ^ (k + 1)) ⟶
        koszulComplex A r (fun i ↦ a i ^ (m + 1))))
    (q : ∀ m k : ℕ, m ≤ k →
      ((ChainComplex.single₀ (ModuleCat.{u} A)).obj
          (ModuleCat.of A (A ⧸ (Ideal.span (Set.range a)) ^ (k + 1))) ⟶
        (ChainComplex.single₀ (ModuleCat.{u} A)).obj
          (ModuleCat.of A (A ⧸ (Ideal.span (Set.range a)) ^ (m + 1)))))
    (hε : ∀ m, (ε m).f 0 = ModuleCat.ofHom
      (((Ideal.span (Set.range a)) ^ (m + 1)).mkQ.comp
        (exteriorPower.zeroEquiv A (Fin r →₀ A)).toLinearMap))
    (ht : ∀ m k h n, (t m k h).f n = ModuleCat.ofHom
      (exteriorPower.map n (Finsupp.linearCombination A
        (fun i ↦ Finsupp.single i (a i ^ (k - m))))))
    (hc : ∀ m k h,
      HomologicalComplex.extendMap (t m k h) ComplexShape.embeddingDownNat ≫
          HomologicalComplex.extendMap (ε m) ComplexShape.embeddingDownNat =
        HomologicalComplex.extendMap (ε k) ComplexShape.embeddingDownNat ≫
          HomologicalComplex.extendMap (q m k h) ComplexShape.embeddingDownNat)
    (hpos : ∀ (n : ℕ), 0 < n → ∀ m : ℕ, ∃ (k : ℕ) (h : m ≤ k),
      HomologicalComplex.homologyMap (t m k h) n = 0) :
    ∀ (j : ℤ) (m : ℕ), ∃ (k : ℕ) (h : m ≤ k),
      HomologicalComplex.homologyMap
        (HomologicalComplex.homotopyCofiber.mapArrowHom
          (HomologicalComplex.extendMap (ε k) ComplexShape.embeddingDownNat)
          (HomologicalComplex.extendMap (ε m) ComplexShape.embeddingDownNat)
          (fun j : ℤ ↦ ⟨j - 1, sub_add_cancel j 1⟩)
          (Arrow.homMk
            (HomologicalComplex.extendMap (t m k h) ComplexShape.embeddingDownNat)
            (HomologicalComplex.extendMap (q m k h) ComplexShape.embeddingDownNat)
            (hc m k h))) j = 0 := by
  let K (m : ℕ) := koszulComplex A r (fun i ↦ a i ^ (m + 1))
  let S (m : ℕ) := (ChainComplex.single₀ (ModuleCat.{u} A)).obj
    (ModuleCat.of A (A ⧸ (Ideal.span (Set.range a)) ^ (m + 1)))
  let F (m : ℕ) := (K m).extend ComplexShape.embeddingDownNat
  let G (m : ℕ) := (S m).extend ComplexShape.embeddingDownNat
  let φ (m : ℕ) := HomologicalComplex.extendMap (ε m) ComplexShape.embeddingDownNat
  let α (m k : ℕ) (h : m ≤ k) : Arrow.mk (φ k) ⟶ Arrow.mk (φ m) :=
    Arrow.homMk (HomologicalComplex.extendMap (t m k h) ComplexShape.embeddingDownNat)
      (HomologicalComplex.extendMap (q m k h) ComplexShape.embeddingDownNat) (hc m k h)
  have hG (m : ℕ) (j : ℤ) (hj : j ≠ 0) : IsZero ((G m).X j) :=
    single_extend_isZero A _ j hj
  intro j m
  by_cases hj : 0 < j
  · refine ⟨m, le_rfl, ?_⟩
    have hz : IsZero ((HomologicalComplex.homotopyCofiber (φ m)).X j) := by
      apply HomologicalComplex.homotopyCofiber.isZero_X (φ m)
      · exact hG m j (by omega)
      · intro l hl
        exact extend_positive_isZero A (K m) l (by change j + 1 = l at hl; omega)
    exact (HomologicalComplex.ExactAt.of_isZero hz).isZero_homology.eq_of_tgt _ _
  by_cases hj0 : j = 0
  · subst j
    refine ⟨m, le_rfl, ?_⟩
    have hepi : Epi ((ε m).f 0) := by
      apply (ModuleCat.epi_iff_surjective _).mpr
      rw [hε m]
      exact (Submodule.mkQ_surjective _).comp
        (exteriorPower.zeroEquiv A (Fin r →₀ A)).surjective
    have hepie : Epi ((φ m).f 0) := by
      dsimp only [φ]
      rw [HomologicalComplex.extendMap_f (ε m) ComplexShape.embeddingDownNat
        (i := 0) (i' := 0) rfl]
      infer_instance
    apply cochain_homologyMap_zero_of_cycles_to_boundaries A
    intro z
    exact cone_boundary_of_epi A (φ m) 0
      (extend_positive_isZero A (K m) 1 (by omega)) _
  by_cases hj1 : j = -1
  · subst j
    obtain ⟨s, hs⟩ := power_ideals_cofinal A r a m
    let k := m + s
    have hmk : m ≤ k := Nat.le_add_right _ _
    refine ⟨k, hmk, ?_⟩
    apply cone_homologyMap_zero_of_boundaries A (φ k) (φ m) (α m k hmk) (-1)
      (hG k (-1) (by omega)) (hG m (-1) (by omega))
    intro x hx hφ
    change (F k).X 0 at x
    change (φ k).f 0 x = 0 at hφ
    let eₖ := (K k).extendXIso ComplexShape.embeddingDownNat (i := 0) (i' := 0) rfl
    let eₘ := (K m).extendXIso ComplexShape.embeddingDownNat (i := 0) (i' := 0) rfl
    let e₁ := (K m).extendXIso ComplexShape.embeddingDownNat (i := 1) (i' := -1) rfl
    let eS := (S k).extendXIso ComplexShape.embeddingDownNat (i := 0) (i' := 0) rfl
    let ξ : ⋀[A]^0 (Fin r →₀ A) := eₖ.hom x
    have hxε : (ε k).f 0 ξ = 0 := by
      apply (ModuleCat.mono_iff_injective eS.inv).mp inferInstance
      have hh : eS.inv ((ε k).f 0 ξ) = 0 := by
        simpa only [φ, HomologicalComplex.extendMap_f (ε k)
          ComplexShape.embeddingDownNat (i := 0) (i' := 0) rfl, ModuleCat.comp_apply] using hφ
      simpa only [map_zero] using hh
    rw [hε k] at hxε
    change ((Ideal.span (Set.range a)) ^ (k + 1)).mkQ
      (exteriorPower.zeroEquiv A (Fin r →₀ A) ξ) = 0 at hxε
    have hxI : exteriorPower.zeroEquiv A (Fin r →₀ A) ξ ∈
        (Ideal.span (Set.range a)) ^ (k + 1) :=
      (Submodule.Quotient.mk_eq_zero _).mp hxε
    have hxJ : exteriorPower.zeroEquiv A (Fin r →₀ A) ξ ∈
        Ideal.span (Set.range (fun i ↦ a i ^ (m + 1))) :=
      hs (Ideal.pow_le_pow_right (by dsimp [k]; omega) hxI)
    obtain ⟨y, hy⟩ := koszulBoundary_zero_range A r (fun i ↦ a i ^ (m + 1)) ξ hxJ
    have ht0 : (t m k hmk).f 0 ξ = ξ := by
      rw [ht]
      apply (exteriorPower.zeroEquiv A (Fin r →₀ A)).injective
      exact LinearMap.congr_fun (exteriorPower.zeroEquiv_naturality _) ξ
    refine ⟨e₁.inv y, ?_⟩
    change (F m).d (-1) 0 (e₁.inv y) =
      (HomologicalComplex.extendMap (t m k hmk) ComplexShape.embeddingDownNat).f 0 x
    rw [HomologicalComplex.extend_d_eq (K m) ComplexShape.embeddingDownNat
      (i := 1) (j := 0) (i' := -1) (j' := 0) rfl rfl,
      HomologicalComplex.extendMap_f (t m k hmk) ComplexShape.embeddingDownNat
        (i := 0) (i' := 0) rfl]
    have hc₁ : e₁.hom (e₁.inv y) = y :=
      congrArg (fun f ↦ f y) e₁.inv_hom_id
    change eₘ.inv ((K m).d 1 0 (e₁.hom (e₁.inv y))) =
      eₘ.inv ((t m k hmk).f 0 (eₖ.hom x))
    rw [hc₁]
    have hd : (K m).d 1 0 = ModuleCat.ofHom
        (koszulBoundary A r (fun i ↦ a i ^ (m + 1)) 0) := by
      dsimp only [K, koszulComplex]
      exact ChainComplex.of_d _ _ 0
    rw [hd]
    change eₘ.inv (koszulBoundary A r (fun i ↦ a i ^ (m + 1)) 0 y) =
      eₘ.inv ((t m k hmk).f 0 ξ)
    rw [hy, ht0]
  · let n := (-(j + 1)).toNat
    have hnpos : 0 < n := by dsimp [n]; omega
    have hn : -(n : ℤ) = j + 1 := by dsimp [n]; omega
    obtain ⟨k, hmk, hk⟩ := hpos n hnpos m
    refine ⟨k, hmk, ?_⟩
    apply cone_homologyMap_zero_of_boundaries A (φ k) (φ m) (α m k hmk) j
      (hG k j hj0) (hG m j hj0)
    intro x hx hφ
    have hf : HomologicalComplex.homologyMap
        (HomologicalComplex.extendMap (t m k hmk) ComplexShape.embeddingDownNat)
          (j + 1) = 0 := by
      apply (cancel_mono ((K m).extendHomologyIso ComplexShape.embeddingDownNat hn).hom).mp
      rw [zero_comp, HomologicalComplex.extendHomologyIso_hom_naturality, hk, comp_zero]
    have hh := cochain_boundary_of_homologyMap_zero A
      (HomologicalComplex.extendMap (t m k hmk) ComplexShape.embeddingDownNat)
      j (j + 1) rfl hf x hx
    exact hh

end ExteriorAlgebra
