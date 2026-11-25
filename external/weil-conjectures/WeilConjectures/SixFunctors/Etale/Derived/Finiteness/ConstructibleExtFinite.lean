/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.ConstructibleHomFinite
public import WeilConjectures.EtaleCohomology.Purity.Smooth.CohomologyHom
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.Ext.Finite
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.TStructure

/-!
# Morphisms between bounded constructible complexes form a finite set

Let `k` be a separably closed field, `Λ` a finite ring whose exponent is invertible in `k`, and
`X` a separated scheme of finite type over `k`. For bounded constructible complexes `K`, `L` of
étale sheaves of `Λ`-modules on `X`, the set of morphisms `K ⟶ L` in the derived category is finite
(`AlgebraicGeometry.Etale.finite_hom_of_boundedConstructible`).

The case of sheaves in degrees `0` and `n`
(`AlgebraicGeometry.Etale.finite_ext_of_isConstructibleSheaf`, finiteness of `Extⁿ(F, G)`) is
proved by induction on `n` for all constructible `F` at once: `F` is a quotient of a finite sum of
extensions by zero `v_! Λ` along affine étale maps, with constructible kernel `F'`, and in the
long exact sequence `Extⁿ⁻¹(F', G) ⟶ Extⁿ(F, G) ⟶ Extⁿ(⊕ v_! Λ, G)` the right term is
`⊕ Hⁿ(V, G)` (by the adjunction `v_! ⊣ v^*`), finite by the finiteness of cohomology
(`AlgebraicGeometry.Etale.finite_hom_singleFunctor_lowerShriekUnit_shift`). The general case
follows by induction on the amplitudes, along the truncation triangles
(`DerivedCategory.prop_of_bounded_of_degreewise`).
-/

@[expose] public section

universe w u

open CategoryTheory Limits Opposite

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ] {k : Type u} [Field k] [IsSepClosed k]
  [HasInvertibleExponent Λ (Spec (.of k))]

/-- The morphisms `Λ_Y ⟶ G[n]` from the constant complex to a constructible sheaf placed in
degree `-n` form a finite set, for `Y` quasi-compact and locally of finite type over a separably
closed field: they are the étale cohomology `Hⁿ(Y, G)`. -/
theorem finite_hom_constantComplex_shift {Y : Scheme.{u}} (q : Y ⟶ Spec (.of k))
    [LocallyOfFiniteType q] [QuasiCompact q]
    (H : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) [IsConstructibleSheaf H] (n : ℤ) :
    Finite (constantComplex Λ Y ⟶
      ((_root_.DerivedCategory.singleFunctor _ 0).obj H)⟦n⟧) := by
  have hd := boundedConstructible_rightDerivedLowerStar_of_finite Λ q (𝟙 _) q (Category.comp_id q)
    (DerivedCategory.boundedConstructible_singleFunctor_obj H 0)
  have hR := boundedFiniteCohomology_rightDerivedGlobalSections_of_rightDerivedLowerStar q hd
  have h₀ := ((_root_.DerivedCategory.boundedFiniteCohomology_iff_finite _).1 hR).2 n
  exact @Finite.of_equiv _ _ h₀ (homConstantComplexLinearEquivCohomology Λ Y _ n).toEquiv.symm

open _root_.DerivedCategory in
/-- The morphisms `v_! Λ ⟶ G[n]` in the derived category form a finite set, for `v : W ⟶ X`
étale with `W` affine and `G` constructible: by the adjunction `v_! ⊣ v^*` they are the
morphisms `Λ_W ⟶ (v^* G)[n]`, that is the cohomology `Hⁿ(W, v^* G)`. -/
theorem finite_hom_singleFunctor_lowerShriekUnit_shift {X : Scheme.{u}} (p : X ⟶ Spec (.of k))
    [LocallyOfFiniteType p] (G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    [IsConstructibleSheaf G] {W : Scheme.{u}} [IsAffine W] (v : W ⟶ X) (h : Etale v) (n : ℤ) :
    Finite ((singleFunctor _ 0).obj (lowerShriekUnit (Λ := Λ) v h) ⟶
      ((singleFunctor _ 0).obj G)⟦n⟧) := by
  let L := etaleLowerShriek (ModuleCat.{u + 1} Λ) v h
  let R := (v)^*[ModuleCat.{u + 1} Λ]
  let adj := (etaleLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) v
    h).mapDerivedCategoryAdjunction
  have := IsConstructibleSheaf.upperStar v G
  have := finite_hom_constantComplex_shift (Λ := Λ) (v ≫ p) (R.obj G) n
  let e₁ : (singleFunctor _ 0).obj (lowerShriekUnit (Λ := Λ) v h) ≅
      L.mapDerivedCategory.obj (constantComplex Λ W) :=
    ((L.mapDerivedCategorySingleFunctor 0).app _).symm ≪≫
      L.mapDerivedCategory.mapIso
        ((((constantSheaf W.smallEtaleTopology
          (ModuleCat.{u + 1} Λ)).mapDerivedCategorySingleFunctor 0).app _).symm ≪≫
            constantFunctorObjSingleIso Λ W)
  let e₂ : R.mapDerivedCategory.obj (((singleFunctor _ 0).obj G)⟦n⟧) ≅
      ((singleFunctor _ 0).obj (R.obj G))⟦n⟧ :=
    (R.mapDerivedCategory.commShiftIso n).app _ ≪≫
      (shiftFunctor _ n).mapIso ((R.mapDerivedCategorySingleFunctor 0).app G)
  exact Finite.of_equiv _ ((e₁.homCongr (Iso.refl _)).trans
    ((adj.homEquiv _ _).trans ((Iso.refl _).homCongr e₂))).symm

/-- `Extⁿ(v_! Λ, G)` is finite for `v : W ⟶ X` étale with `W` affine and `G` constructible. -/
theorem finite_ext_lowerShriekUnit {X : Scheme.{u}} (p : X ⟶ Spec (.of k))
    [LocallyOfFiniteType p] (G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    [IsConstructibleSheaf G] {W : Scheme.{u}} [IsAffine W] (v : W ⟶ X) (h : Etale v)
    [HasExt.{w} (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))] (n : ℕ) :
    Finite (Abelian.Ext (lowerShriekUnit (Λ := Λ) v h) G n) :=
  @Finite.of_equiv _ _ (finite_hom_singleFunctor_lowerShriekUnit_shift p G v h n)
    Abelian.Ext.homEquiv.symm

attribute [local instance] Abelian.hasFiniteBiproducts in
/-- A constructible sheaf `F` on a Noetherian scheme is the quotient of a finite direct sum of
extensions by zero `v_! Λ` along étale maps `v` with affine source. -/
theorem exists_epi_biproduct_lowerShriekUnit {X : Scheme.{u}} [IsNoetherian X]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) [IsConstructibleSheaf F] :
    ∃ (J : Type (u + 1)) (_ : Finite J) (W : J → Scheme.{u}) (_ : ∀ j, IsAffine (W j))
      (v : ∀ j, W j ⟶ X) (h : ∀ j, Etale (v j))
      (_ : IsConstructibleSheaf (⨁ fun j ↦ lowerShriekUnit (Λ := Λ) (v j) (h j)))
      (π : (⨁ fun j ↦ lowerShriekUnit (Λ := Λ) (v j) (h j)) ⟶ F), Epi π := by
  obtain ⟨S, hS⟩ := exists_epi_ι_app_of_isConstructibleSheaf
    (isColimitFinsetSectionImageCocone F) (mono_finsetSectionImageCocone_ι_app F) ‹_›
  have hepi : Epi (finsetSigmaDesc (sectionGenerator F) (sectionGeneratorHom F) S) := by
    rw [← imageSubobject_arrow_comp
      (finsetSigmaDesc (sectionGenerator F) (sectionGeneratorHom F) S)]
    exact @epi_comp _ _ _ _ _ _ inferInstance _ hS
  have (i : SectionIndex F) : IsConstructibleSheaf (sectionGenerator F i) :=
    have : IsAffine ((𝟭 Scheme).obj i.1.1.left) := i.1.2
    have : Etale i.1.1.hom := i.1.1.prop
    isConstructibleSheaf_lowerShriekUnit_of_isAffine_source (X := X) i.1.1.hom
  have := isConstructibleSheaf_finsetSigma (sectionGenerator F) S
  exact ⟨S, inferInstance, fun i ↦ i.1.1.1.left, fun i ↦ i.1.1.2, fun i ↦ i.1.1.1.hom,
    fun i ↦ i.1.1.1.prop,
    IsConstructibleSheaf.of_iso (biproduct.isoCoproduct fun i : S ↦ sectionGenerator F i.1).symm,
    (biproduct.isoCoproduct _).hom ≫
      finsetSigmaDesc (sectionGenerator F) (sectionGeneratorHom F) S, epi_comp _ _⟩

attribute [local instance] Abelian.hasFiniteBiproducts in
/-- `Extⁿ(F, G)` is finite for constructible `F` and `G`, by induction on `n` for all `F` at
once, along a presentation `0 ⟶ F' ⟶ ⨁ v_! Λ ⟶ F ⟶ 0`. -/
theorem finite_ext_nat_of_isConstructibleSheaf {X : Scheme.{u}} (p : X ⟶ Spec (.of k))
    [LocallyOfFiniteType p] [QuasiCompact p] [IsSeparated p]
    [HasExt.{w} (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))]
    (G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) [IsConstructibleSheaf G] (n : ℕ) :
    ∀ (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) [IsConstructibleSheaf F],
      Finite (Abelian.Ext F G n) := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace p
  have : IsNoetherian X := {}
  induction n with
  | zero =>
    intro F _
    have := finite_hom_of_isConstructibleSheaf p F G
    exact Finite.of_equiv _ Abelian.Ext.homEquiv₀.symm
  | succ n ih =>
    intro F _
    obtain ⟨J, _, W, _, v, h, _, π, _⟩ := exists_epi_biproduct_lowerShriekUnit (Λ := Λ) F
    have (j : J) : Finite (Abelian.Ext (lowerShriekUnit (Λ := Λ) (v j) (h j)) G (n + 1)) :=
      finite_ext_lowerShriekUnit p G (v j) (h j) (n + 1)
    have : Finite (Abelian.Ext (⨁ fun j ↦ lowerShriekUnit (Λ := Λ) (v j) (h j)) G (n + 1)) :=
      Abelian.Ext.finite_of_isBilimit (biproduct.isBilimit _) G (n + 1)
    have : IsConstructibleSheaf (kernel π) := IsConstructibleSheaf.kernel π
    have := ih (kernel π)
    have hS : (ShortComplex.mk (kernel.ι π) π (kernel.condition π)).ShortExact :=
      { exact := ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel π) }
    exact Abelian.Ext.finite_of_shortExact hS G n

/-- **Finiteness of `Extⁿ` between constructible sheaves**: over a separated scheme of finite type
over a separably closed field, with coefficients a finite ring with invertible exponent. -/
theorem finite_ext_of_isConstructibleSheaf {X : Scheme.{u}} (p : X ⟶ Spec (.of k))
    [LocallyOfFiniteType p] [QuasiCompact p] [IsSeparated p] (n : ℤ)
    (F G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) [IsConstructibleSheaf F]
    [IsConstructibleSheaf G] :
    Finite ((_root_.DerivedCategory.singleFunctor _ 0).obj F ⟶
      ((_root_.DerivedCategory.singleFunctor _ 0).obj G)⟦n⟧) := by
  have := HasExt.standard (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
  rcases lt_or_ge n 0 with hn | hn
  · have : _root_.DerivedCategory.TStructure.t.IsGE
        (((_root_.DerivedCategory.singleFunctor _ 0).obj G)⟦n⟧) (-n) :=
      _root_.DerivedCategory.TStructure.t.isGE_shift _ 0 n (-n) (by lia)
    refine @Finite.of_subsingleton _ ⟨fun f g ↦ ?_⟩
    rw [_root_.DerivedCategory.TStructure.t.zero f 0 (-n) (by lia),
      _root_.DerivedCategory.TStructure.t.zero g 0 (-n) (by lia)]
  · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hn
    exact @Finite.of_equiv _ _ (finite_ext_nat_of_isConstructibleSheaf p G m F)
      Abelian.Ext.homEquiv

open _root_.DerivedCategory in
/-- The morphisms between constructible sheaves placed in arbitrary degrees `a` and `b` form a
finite set: this is `Extᵇ⁻ᵃ`. -/
theorem finite_hom_singleFunctor_of_isConstructibleSheaf {X : Scheme.{u}} (p : X ⟶ Spec (.of k))
    [LocallyOfFiniteType p] [QuasiCompact p] [IsSeparated p] (a b : ℤ)
    (F G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) [IsConstructibleSheaf F]
    [IsConstructibleSheaf G] :
    Finite ((singleFunctor _ a).obj F ⟶ (singleFunctor _ b).obj G) := by
  have := finite_ext_of_isConstructibleSheaf p (a - b) F G
  let e₁ : (singleFunctor _ a).obj F ≅ ((singleFunctor _ 0).obj F)⟦-a⟧ :=
    (((singleFunctors _).shiftIso (-a) a 0 (by lia)).app F).symm
  let e₂ : (singleFunctor _ b).obj G ≅ ((singleFunctor _ 0).obj G)⟦a - b⟧⟦-a⟧ :=
    (((singleFunctors _).shiftIso (-b) b 0 (by lia)).app G).symm ≪≫
      (shiftFunctorAdd' _ (a - b) (-a) (-b) (by lia)).app _
  exact Finite.of_equiv _
    ((Functor.FullyFaithful.ofFullyFaithful (shiftFunctor _ (-a))).homEquiv.trans
      (e₁.homCongr e₂).symm)

open _root_.DerivedCategory in
/-- The morphisms from a bounded constructible complex to a constructible sheaf placed in some
degree form a finite set, by induction on the amplitude of the source. -/
theorem finite_hom_singleFunctor_of_boundedConstructible {X : Scheme.{u}} (p : X ⟶ Spec (.of k))
    [LocallyOfFiniteType p] [QuasiCompact p] [IsSeparated p]
    {K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hK : Etale.DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) X K) (b : ℤ)
    (G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) [IsConstructibleSheaf G] :
    Finite (K ⟶ (singleFunctor _ b).obj G) := by
  let P : ℤ → ObjectProperty (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :=
    fun _ F ↦ IsConstructibleSheaf F
  have hP (q : ℤ) : (P q).IsClosedUnderIsomorphisms :=
    ⟨fun e h ↦ have : IsConstructibleSheaf _ := h; IsConstructibleSheaf.of_iso e⟩
  let Q : ObjectProperty (_root_.DerivedCategory (Sheaf X.smallEtaleTopology
      (ModuleCat.{u + 1} Λ))) :=
    fun K ↦ Finite (K ⟶ (singleFunctor _ b).obj G)
  have : Q.IsClosedUnderIsomorphisms :=
    ⟨fun e h ↦ have : Finite _ := h; Finite.of_equiv _ (e.homCongr (Iso.refl _))⟩
  exact @prop_of_bounded_of_degreewise _ _ _ _ Q _
    (fun M hM ↦ @Finite.of_subsingleton _ ⟨fun f g ↦ hM.eq_of_src f g⟩)
    (fun T hT (h₁ : Finite _) (h₃ : Finite _) ↦ T.finite_hom_obj₂_of_yoneda hT _) P hP
    (fun a F (hF : IsConstructibleSheaf F) ↦
      finite_hom_singleFunctor_of_isConstructibleSheaf p a b F G) K hK.1 hK.2

/-- **Morphisms between bounded constructible complexes form a finite set**, over a separated
scheme of finite type over a separably closed field, with coefficients a finite ring with
invertible exponent. -/
theorem finite_hom_of_boundedConstructible {X : Scheme.{u}} (p : X ⟶ Spec (.of k))
    [LocallyOfFiniteType p] [QuasiCompact p] [IsSeparated p]
    {K L : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hK : Etale.DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) X K)
    (hL : Etale.DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) X L) :
    Finite (K ⟶ L) := by
  let P : ℤ → ObjectProperty (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :=
    fun _ F ↦ IsConstructibleSheaf F
  have hP (q : ℤ) : (P q).IsClosedUnderIsomorphisms :=
    ⟨fun e h ↦ have : IsConstructibleSheaf _ := h; IsConstructibleSheaf.of_iso e⟩
  let Q : ObjectProperty (_root_.DerivedCategory (Sheaf X.smallEtaleTopology
      (ModuleCat.{u + 1} Λ))) :=
    fun L ↦ Finite (K ⟶ L)
  have : Q.IsClosedUnderIsomorphisms :=
    ⟨fun e h ↦ have : Finite _ := h; Finite.of_equiv _ ((Iso.refl _).homCongr e)⟩
  exact @_root_.DerivedCategory.prop_of_bounded_of_degreewise _ _ _ _ Q _
    (fun M hM ↦ @Finite.of_subsingleton _ ⟨fun f g ↦ hM.eq_of_tgt f g⟩)
    (fun T hT (h₁ : Finite _) (h₃ : Finite _) ↦ T.finite_hom_obj₂_of_coyoneda hT _) P hP
    (fun b G (hG : IsConstructibleSheaf G) ↦
      finite_hom_singleFunctor_of_boundedConstructible p hK b G) L hL.1 hL.2

end Etale

end AlgebraicGeometry
