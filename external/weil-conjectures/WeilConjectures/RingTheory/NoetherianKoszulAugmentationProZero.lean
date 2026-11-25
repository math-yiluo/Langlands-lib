/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.Embedding.Extend
public import Mathlib.LinearAlgebra.ExteriorPower.Basic
public import WeilConjectures.AlgebraicGeometry.KoszulComplex
import Mathlib.LinearAlgebra.ExteriorPower.Basis
import WeilConjectures.Algebra.Homology.BoundedDerivedTowerProZero
import WeilConjectures.RingTheory.KoszulConeHomologyProZero
import WeilConjectures.RingTheory.KoszulGeneratorChainMap
import WeilConjectures.RingTheory.KoszulPowerHomologyProZero
import all WeilConjectures.RingTheory.KoszulProjectiveResolution

/-!
# Pro-zero cones of the Noetherian Koszul augmentation

Source: Stacks Project, Tags 0921, 0922 and 0G3B
(auxiliary; not a blueprint node).
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits Opposite

namespace ExteriorAlgebra

private theorem powerAugmentation_cycle (A : Type u) [CommRing A] (r : ℕ)
    (a : Fin r → A) (m : ℕ) :
    (koszulComplex A r (fun i ↦ a i ^ (m + 1))).d 1 0 ≫
      ModuleCat.ofHom (((Ideal.span (Set.range a)) ^ (m + 1)).mkQ.comp
        (exteriorPower.zeroEquiv A (Fin r →₀ A)).toLinearMap) = 0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change ((Ideal.span (Set.range a)) ^ (m + 1)).mkQ
    (exteriorPower.zeroEquiv A (Fin r →₀ A) (koszulBoundary A r _ 0 x)) = 0
  rw [koszulBoundary_zero_quotient_formula]
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  have hmem : ∀ i, a i ^ (m + 1) ∈ (Ideal.span (Set.range a)) ^ (m + 1) := by
    intro i
    exact Ideal.pow_mem_pow (Ideal.subset_span (Set.mem_range_self i)) _
  have hrange : LinearMap.range (Finsupp.linearCombination A (fun i ↦ a i ^ (m + 1))) ≤
      ((Ideal.span (Set.range a)) ^ (m + 1) : Ideal A) := by
    rw [Finsupp.range_linearCombination]
    exact Submodule.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact hmem i)
  exact hrange (LinearMap.mem_range_self _ _)

private noncomputable def powerAugmentation (A : Type u) [CommRing A] (r : ℕ)
    (a : Fin r → A) (m : ℕ) :
    koszulComplex A r (fun i ↦ a i ^ (m + 1)) ⟶
      (ChainComplex.single₀ (ModuleCat.{u} A)).obj
        (ModuleCat.of A (A ⧸ (Ideal.span (Set.range a)) ^ (m + 1))) :=
  (ChainComplex.toSingle₀Equiv _ _).symm
    ⟨ModuleCat.ofHom (((Ideal.span (Set.range a)) ^ (m + 1)).mkQ.comp
      (exteriorPower.zeroEquiv A (Fin r →₀ A)).toLinearMap),
      powerAugmentation_cycle A r a m⟩

private noncomputable def powerDiagonal (A : Type u) [CommRing A] (r : ℕ)
    (a : Fin r → A) (d : ℕ) : (Fin r →₀ A) →ₗ[A] (Fin r →₀ A) :=
  Finsupp.linearCombination A (fun i ↦ Finsupp.single i (a i ^ d))

private theorem powerForms_comp (A : Type u) [CommRing A] (r : ℕ)
    (a : Fin r → A) (m k : ℕ) (h : m ≤ k) :
    (Finsupp.linearCombination A (fun i ↦ a i ^ (m + 1))).comp
      (powerDiagonal A r a (k - m)) =
      Finsupp.linearCombination A (fun i ↦ a i ^ (k + 1)) := by
  apply Finsupp.lhom_ext
  intro i x
  have hexp : k - m + (m + 1) = k + 1 := by omega
  simp only [LinearMap.comp_apply, powerDiagonal, Finsupp.linearCombination_single,
    map_smul, smul_eq_mul]
  rw [← pow_add, hexp]

private theorem powerTransition_comm (A : Type u) [CommRing A] (r : ℕ)
    (a : Fin r → A) (m k : ℕ) (h : m ≤ k) (n : ℕ) :
    (koszulComplex A r (fun i ↦ a i ^ (k + 1))).d (n + 1) n ≫
      ModuleCat.ofHom (exteriorPower.map n (powerDiagonal A r a (k - m))) =
    ModuleCat.ofHom (exteriorPower.map (n + 1) (powerDiagonal A r a (k - m))) ≫
      (koszulComplex A r (fun i ↦ a i ^ (m + 1))).d (n + 1) n := by
  have hd (f : Fin r → A) : (koszulComplex A r f).d (n + 1) n =
      ModuleCat.ofHom (koszulBoundary A r f n) := by
    dsimp only [koszulComplex]
    exact ChainComplex.of_d _ _ n
  rw [hd, hd]
  apply ModuleCat.hom_ext
  change (exteriorPower.map n _).comp (koszulBoundary A r _ n) =
    (koszulBoundary A r _ n).comp (exteriorPower.map (n + 1) _)
  apply exteriorPower.linearMap_ext
  ext v
  simp only [LinearMap.compAlternatingMap_apply, LinearMap.comp_apply,
    exteriorPower.map_apply_ιMulti, boundary_wedge, map_sum, map_smul]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  simp only [Function.comp_apply]
  rw [show Finsupp.linearCombination A (fun i ↦ a i ^ (m + 1))
      (powerDiagonal A r a (k - m) (v i)) =
      Finsupp.linearCombination A (fun i ↦ a i ^ (k + 1)) (v i) from
        LinearMap.congr_fun (powerForms_comp A r a m k h) (v i)]
  rfl

private noncomputable def powerTransition (A : Type u) [CommRing A] (r : ℕ)
    (a : Fin r → A) (m k : ℕ) (h : m ≤ k) :
    koszulComplex A r (fun i ↦ a i ^ (k + 1)) ⟶
      koszulComplex A r (fun i ↦ a i ^ (m + 1)) :=
  ChainComplex.ofHom
    (fun n ↦ ModuleCat.ofHom (exteriorPower.map n (powerDiagonal A r a (k - m))))
    (fun n ↦ (powerTransition_comm A r a m k h n).symm)

private noncomputable def powerQuotient (A : Type u) [CommRing A] (r : ℕ)
    (a : Fin r → A) (m k : ℕ) (h : m ≤ k) :
    (ChainComplex.single₀ (ModuleCat.{u} A)).obj
        (ModuleCat.of A (A ⧸ (Ideal.span (Set.range a)) ^ (k + 1))) ⟶
      (ChainComplex.single₀ (ModuleCat.{u} A)).obj
        (ModuleCat.of A (A ⧸ (Ideal.span (Set.range a)) ^ (m + 1))) :=
  (ChainComplex.single₀ (ModuleCat.{u} A)).map
    (ModuleCat.ofHom (Submodule.factor (show
      ((Ideal.span (Set.range a)) ^ (k + 1) : Ideal A) ≤
        (Ideal.span (Set.range a)) ^ (m + 1) from
      Ideal.pow_le_pow_right (Nat.add_le_add_right h 1))))

private theorem powerSquare (A : Type u) [CommRing A] (r : ℕ)
    (a : Fin r → A) (m k : ℕ) (h : m ≤ k) :
    powerTransition A r a m k h ≫ powerAugmentation A r a m =
      powerAugmentation A r a k ≫ powerQuotient A r a m k h := by
  apply HomologicalComplex.to_single_hom_ext
  simp only [HomologicalComplex.comp_f, powerAugmentation,
    ChainComplex.toSingle₀Equiv_symm_apply_f_zero]
  apply ModuleCat.hom_ext
  change (((Ideal.span (Set.range a)) ^ (m + 1)).mkQ.comp
    (exteriorPower.zeroEquiv A (Fin r →₀ A)).toLinearMap).comp
      (exteriorPower.map 0 (powerDiagonal A r a (k - m))) = _
  rw [LinearMap.comp_assoc, exteriorPower.zeroEquiv_naturality]
  rfl

private theorem powerDiagonal_zero (A : Type u) [CommRing A] (r : ℕ)
    (a : Fin r → A) : powerDiagonal A r a 0 = LinearMap.id := by
  apply Finsupp.lhom_ext
  intro i x
  simp [powerDiagonal, Finsupp.linearCombination_single]

private theorem powerDiagonal_comp (A : Type u) [CommRing A] (r : ℕ)
    (a : Fin r → A) (m k l : ℕ) (hmk : m ≤ k) (hkl : k ≤ l) :
    (powerDiagonal A r a (k - m)).comp (powerDiagonal A r a (l - k)) =
      powerDiagonal A r a (l - m) := by
  apply Finsupp.lhom_ext
  intro i x
  have hexp : l - k + (k - m) = l - m := by omega
  simp only [LinearMap.comp_apply, powerDiagonal, Finsupp.linearCombination_single,
    Finsupp.smul_single, smul_eq_mul]
  rw [mul_assoc, ← pow_add, hexp]

private theorem powerTransition_id (A : Type u) [CommRing A] (r : ℕ)
    (a : Fin r → A) (m : ℕ) : powerTransition A r a m m le_rfl = 𝟙 _ := by
  apply HomologicalComplex.hom_ext
  intro n
  change ModuleCat.ofHom (exteriorPower.map n (powerDiagonal A r a (m - m))) = 𝟙 _
  rw [Nat.sub_self, powerDiagonal_zero, exteriorPower.map_id]
  rfl

private theorem powerTransition_comp (A : Type u) [CommRing A] (r : ℕ)
    (a : Fin r → A) (m k l : ℕ) (hmk : m ≤ k) (hkl : k ≤ l) :
    powerTransition A r a k l hkl ≫ powerTransition A r a m k hmk =
      powerTransition A r a m l (hmk.trans hkl) := by
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  change (exteriorPower.map n (powerDiagonal A r a (k - m))).comp
    (exteriorPower.map n (powerDiagonal A r a (l - k))) = _
  rw [← exteriorPower.map_comp, powerDiagonal_comp A r a m k l hmk hkl]
  rfl

private theorem powerQuotient_id (A : Type u) [CommRing A] (r : ℕ)
    (a : Fin r → A) (m : ℕ) : powerQuotient A r a m m le_rfl = 𝟙 _ := by
  apply HomologicalComplex.from_single_hom_ext
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective ((Ideal.span (Set.range a)) ^ (m + 1)) x
  rfl

private theorem powerQuotient_comp (A : Type u) [CommRing A] (r : ℕ)
    (a : Fin r → A) (m k l : ℕ) (hmk : m ≤ k) (hkl : k ≤ l) :
    powerQuotient A r a k l hkl ≫ powerQuotient A r a m k hmk =
      powerQuotient A r a m l (hmk.trans hkl) := by
  apply HomologicalComplex.from_single_hom_ext
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective ((Ideal.span (Set.range a)) ^ (l + 1)) x
  rfl

private theorem koszulTerm_isZero (A : Type u) [CommRing A] (r : ℕ)
    (f : Fin r → A) (n : ℕ) (hn : r < n) : IsZero ((koszulComplex A r f).X n) := by
  classical
  let b := (Finsupp.basisSingleOne : Module.Basis (Fin r) A (Fin r →₀ A)).exteriorPower n
  have : IsEmpty (Set.powersetCard (Fin r) n) := ⟨by
    intro s
    have h := Finset.card_le_univ (s : Finset (Fin r))
    simp only [Fintype.card_fin] at h
    have hs : (s : Finset (Fin r)).card = n := s.property
    omega⟩
  have : Subsingleton (⋀[A]^n (Fin r →₀ A)) :=
    Function.Injective.subsingleton b.repr.injective
  exact ModuleCat.isZero_of_subsingleton (ModuleCat.of A (⋀[A]^n (Fin r →₀ A)))

private theorem extend_term_isZero (A : Type u) [CommRing A]
    (K : ChainComplex (ModuleCat.{u} A) ℕ) (r : ℕ)
    (hK : ∀ n, r < n → IsZero (K.X n)) (j : ℤ) (hj : j < -(r : ℤ) ∨ 0 < j) :
    IsZero ((K.extend ComplexShape.embeddingDownNat).X j) := by
  by_cases he : ∃ n : ℕ, -(n : ℤ) = j
  · obtain ⟨n, rfl⟩ := he
    exact (hK n (by omega)).of_iso (K.extendXIso ComplexShape.embeddingDownNat rfl)
  · apply K.isZero_extend_X
    intro n hn
    exact he ⟨n, hn⟩

private theorem powerCone_bounded (A : Type u) [CommRing A]
    [HasDerivedCategory.{w} (ModuleCat.{u} A)] (r : ℕ) (a : Fin r → A)
    (m : ℕ) (j : ℤ) (hj : j < -(r : ℤ) - 1 ∨ 0 < j) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) j).obj
      (DerivedCategory.Q.obj (HomologicalComplex.homotopyCofiber
        (HomologicalComplex.extendMap (powerAugmentation A r a m)
          ComplexShape.embeddingDownNat)))) := by
  let K := koszulComplex A r (fun i ↦ a i ^ (m + 1))
  let S := (ChainComplex.single₀ (ModuleCat.{u} A)).obj
    (ModuleCat.of A (A ⧸ (Ideal.span (Set.range a)) ^ (m + 1)))
  let ε := HomologicalComplex.extendMap (powerAugmentation A r a m)
    ComplexShape.embeddingDownNat
  have hz : IsZero ((HomologicalComplex.homotopyCofiber ε).X j) := by
    apply HomologicalComplex.homotopyCofiber.isZero_X ε
    · apply extend_term_isZero A S 0
      · intro n hn
        exact HomologicalComplex.isZero_single_obj_X (.down ℕ) 0 _ n (by omega)
      · rcases hj with hj | hj
        · left; omega
        · exact Or.inr hj
    · intro l hl
      apply extend_term_isZero A K r (koszulTerm_isZero A r _)
      change j + 1 = l at hl
      omega
  exact (HomologicalComplex.ExactAt.of_isZero hz).isZero_homology.of_iso
    ((DerivedCategory.homologyFunctorFactors (ModuleCat.{u} A) j).app _)

private noncomputable def powerArrowTower (A : Type u) [CommRing A] (r : ℕ)
    (a : Fin r → A) : ℕᵒᵖ ⥤ Arrow (CochainComplex (ModuleCat.{u} A) ℤ) where
  obj m := Arrow.mk (HomologicalComplex.extendMap (powerAugmentation A r a m.unop)
    ComplexShape.embeddingDownNat)
  map {k m} h := Arrow.homMk
    (HomologicalComplex.extendMap (powerTransition A r a m.unop k.unop (leOfHom h.unop))
      ComplexShape.embeddingDownNat)
    (HomologicalComplex.extendMap (powerQuotient A r a m.unop k.unop (leOfHom h.unop))
      ComplexShape.embeddingDownNat)
    (by
      dsimp only [Arrow.mk_hom]
      rw [← HomologicalComplex.extendMap_comp, ← HomologicalComplex.extendMap_comp,
        powerSquare])
  map_id m := by
    apply Arrow.hom_ext
    · simp [powerTransition_id, HomologicalComplex.extendMap_id]
    · simp [powerQuotient_id, HomologicalComplex.extendMap_id]
  map_comp {k l m} h g := by
    apply Arrow.hom_ext
    · simp only [Arrow.comp_left, Arrow.homMk_left]
      rw [← HomologicalComplex.extendMap_comp, powerTransition_comp]
    · simp only [Arrow.comp_right, Arrow.homMk_right]
      rw [← HomologicalComplex.extendMap_comp, powerQuotient_comp]

private noncomputable def strictConeFunctor (A : Type u) [CommRing A] :
    Arrow (CochainComplex (ModuleCat.{u} A) ℤ) ⥤ CochainComplex (ModuleCat.{u} A) ℤ where
  obj f := HomologicalComplex.homotopyCofiber f.hom
  map {f g} h := HomologicalComplex.homotopyCofiber.mapArrowHom f.hom g.hom
    (fun j : ℤ ↦ ⟨j - 1, sub_add_cancel j 1⟩) h
  map_id _ := HomologicalComplex.homotopyCofiber.mapArrowHom_id _ _
  map_comp _ _ := HomologicalComplex.homotopyCofiber.mapArrowHom_comp _ _ _ _ _ _

/-- The canonical augmentations and power transitions exist and their strict cone transitions
are eventually zero in the derived category. Indices `m : ℕ` mean exponent `m + 1`.
The exterior model is the signed total tensor model: a wedge indexed by an increasing
subset is the corresponding tensor basis vector. All maps are specified on components;
the quotient transition is specified after the surjective quotient map. Thus the existential
maps are uniquely determined, including their strict commuting squares.

Source: Stacks Project, Tags 0921, 0922 and 0G3B
(auxiliary; not a blueprint node).

Proof: put J_m = (a_i^(m+1)). The exterior contraction differential has the usual alternating
signs; the exterior power of the diagonal a_i^(k-m) commutes with contraction. The quotient
kills the degree-one differential, giving the augmentation and strict squares. Signed
insertion of a generator gives dh+hd = a_i^(m+1), so J_m annihilates Koszul homology.
Apply Artin--Rees (lem-weil-pbc-artin-rees) to the cycles inside each finite free term.
For large k the negative-degree transition has image in J_m^(c+1), so its cycle image
lies in J_m times the cycles and hence in boundaries. A maximum kills all negative degrees.
The augmentation cone has H^0=0, H^(-1)=I^(m+1)/J_m, and lower cohomology the shifted
negative Koszul homology. The containment I^(r*m+1) ≤ J_m kills the degree-minus-one
transition eventually. All cones are supported in [-r-1,0]. Apply the uniform bounded-tower
lemma (lem-weil-pbc-bounded-derived-tower-pro-zero), Tag 0G3B, to upgrade eventual
cohomological vanishing to vanishing of these very cone maps. For r=0 the augmentation
is the identity under the degree-zero exterior identification, so its cone is acyclic. -/
theorem noetherian_koszul_augmentation_pro_zero
    (A : Type u) [CommRing A] [IsNoetherianRing A]
    [HasDerivedCategory.{w} (ModuleCat.{u} A)] (r : ℕ) (a : Fin r → A) :
    ∃ (ε : ∀ m : ℕ, koszulComplex A r (fun i ↦ a i ^ (m + 1)) ⟶
        (ChainComplex.single₀ (ModuleCat.{u} A)).obj
          (ModuleCat.of A (A ⧸ (Ideal.span (Set.range a)) ^ (m + 1))))
      (t : ∀ m k : ℕ, m ≤ k →
        (koszulComplex A r (fun i ↦ a i ^ (k + 1)) ⟶
          koszulComplex A r (fun i ↦ a i ^ (m + 1))))
      (q : ∀ m k : ℕ, m ≤ k →
        ((ChainComplex.single₀ (ModuleCat.{u} A)).obj
            (ModuleCat.of A (A ⧸ (Ideal.span (Set.range a)) ^ (k + 1))) ⟶
          (ChainComplex.single₀ (ModuleCat.{u} A)).obj
            (ModuleCat.of A (A ⧸ (Ideal.span (Set.range a)) ^ (m + 1))))),
      (∀ m, (ε m).f 0 = ModuleCat.ofHom
        (((Ideal.span (Set.range a)) ^ (m + 1)).mkQ.comp
          (_root_.exteriorPower.zeroEquiv A (Fin r →₀ A)).toLinearMap)) ∧
      (∀ m k h n, (t m k h).f n = ModuleCat.ofHom
        (_root_.exteriorPower.map n (Finsupp.linearCombination A
          (fun i ↦ Finsupp.single i (a i ^ (k - m)))))) ∧
      (∀ m k h, ModuleCat.ofHom ((Ideal.span (Set.range a)) ^ (k + 1)).mkQ ≫
        (q m k h).f 0 = ModuleCat.ofHom ((Ideal.span (Set.range a)) ^ (m + 1)).mkQ) ∧
      ∃ hc : ∀ m k h,
        HomologicalComplex.extendMap (t m k h) ComplexShape.embeddingDownNat ≫
            HomologicalComplex.extendMap (ε m) ComplexShape.embeddingDownNat =
          HomologicalComplex.extendMap (ε k) ComplexShape.embeddingDownNat ≫
            HomologicalComplex.extendMap (q m k h) ComplexShape.embeddingDownNat,
        ∀ m : ℕ, ∃ (k : ℕ) (h : m ≤ k),
          DerivedCategory.Q.map
            (HomologicalComplex.homotopyCofiber.mapArrowHom
              (HomologicalComplex.extendMap (ε k) ComplexShape.embeddingDownNat)
              (HomologicalComplex.extendMap (ε m) ComplexShape.embeddingDownNat)
              (fun j : ℤ ↦ ⟨j - 1, sub_add_cancel j 1⟩)
              (Arrow.homMk
                (HomologicalComplex.extendMap (t m k h) ComplexShape.embeddingDownNat)
                (HomologicalComplex.extendMap (q m k h) ComplexShape.embeddingDownNat)
                (hc m k h))) = 0 := by
  let ε := powerAugmentation A r a
  let t := powerTransition A r a
  let q := powerQuotient A r a
  have hε : ∀ m, (ε m).f 0 = ModuleCat.ofHom
      (((Ideal.span (Set.range a)) ^ (m + 1)).mkQ.comp
        (exteriorPower.zeroEquiv A (Fin r →₀ A)).toLinearMap) := fun _ ↦
    ChainComplex.toSingle₀Equiv_symm_apply_f_zero _ _
  have ht : ∀ m k h n, (t m k h).f n = ModuleCat.ofHom
      (exteriorPower.map n (Finsupp.linearCombination A
        (fun i ↦ Finsupp.single i (a i ^ (k - m))))) := fun _ _ _ _ ↦ rfl
  have hq : ∀ m k h, ModuleCat.ofHom ((Ideal.span (Set.range a)) ^ (k + 1)).mkQ ≫
      (q m k h).f 0 = ModuleCat.ofHom ((Ideal.span (Set.range a)) ^ (m + 1)).mkQ :=
    fun _ _ _ ↦ rfl
  have hc : ∀ m k h, HomologicalComplex.extendMap (t m k h)
      ComplexShape.embeddingDownNat ≫ HomologicalComplex.extendMap (ε m)
        ComplexShape.embeddingDownNat =
      HomologicalComplex.extendMap (ε k) ComplexShape.embeddingDownNat ≫
        HomologicalComplex.extendMap (q m k h) ComplexShape.embeddingDownNat := by
    intro m k h
    rw [← HomologicalComplex.extendMap_comp, ← HomologicalComplex.extendMap_comp]
    exact congrArg (fun f ↦ HomologicalComplex.extendMap f
      ComplexShape.embeddingDownNat) (powerSquare A r a m k h)
  refine ⟨ε, t, q, hε, ht, hq, hc, ?_⟩
  let X : ℕᵒᵖ ⥤ DerivedCategory (ModuleCat.{u} A) :=
    powerArrowTower A r a ⋙ strictConeFunctor A ⋙ DerivedCategory.Q
  have hbounded : ∀ (n : ℕ) (j : ℤ), j < -(r : ℤ) - 1 ∨ 0 < j →
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) j).obj
        (X.obj (op n))) := powerCone_bounded A r a
  have hpro : ∀ (j : ℤ) (m : ℕ), ∃ (k : ℕ) (h : m ≤ k),
      (DerivedCategory.homologyFunctor (ModuleCat.{u} A) j).map
        (X.map (homOfLE h).op) = 0 := by
    intro j m
    obtain ⟨k, h, hk⟩ := koszul_cone_homology_transition_pro_zero A r a ε t q hε ht hc
      (koszul_power_homology_pro_zero A r a t ht) j m
    refine ⟨k, h, ?_⟩
    apply (cancel_mono ((DerivedCategory.homologyFunctorFactors
      (ModuleCat.{u} A) j).hom.app _)).mp
    rw [zero_comp]
    change (DerivedCategory.homologyFunctor (ModuleCat.{u} A) j).map
      (DerivedCategory.Q.map _) ≫ _ = _
    rw [DerivedCategory.homologyFunctorFactors_hom_naturality]
    have hz : HomologicalComplex.homologyMap
        ((strictConeFunctor A).map ((powerArrowTower A r a).map (homOfLE h).op)) j = 0 := hk
    rw [hz, comp_zero]
  exact DerivedCategory.tower_proZero_of_bounded_homology_proZero X
    (-(r : ℤ) - 1) 0 (by omega) hbounded hpro

end ExteriorAlgebra
