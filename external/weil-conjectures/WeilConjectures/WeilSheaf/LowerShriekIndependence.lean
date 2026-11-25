/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Compactification.CommonRefinement
public import WeilConjectures.WeilSheaf.ExtensionByZeroDerived
public import WeilConjectures.WeilSheaf.FiniteLeray
public import WeilConjectures.WeilSheaf.LowerShriek
public import WeilConjectures.WeilSheaf.LowerStarId
public import WeilConjectures.WeilSheaf.ProperBaseChangeFunctor

/-!
# Proper direct image of an extension by zero, and independence of the compactification

Consider a commutative square of `k₀`-schemes
```
X' --a--> W
|         |
q         b
v         v
Y' --i--> Z
```
with `a` and `i` open immersions and `b`, `q` proper. Then `Rb_* ∘ a_! ≅ i_! ∘ Rq_*` on Weil
complexes on `X'` (`AlgebraicGeometry.ProEtaleWeilSheaf.rightDerivedLowerStarExtensionByZeroIso`).
The proof: `E = Rb_* a_! K` vanishes on the closed complement of `Y'` by proper base change
(`AlgebraicGeometry.WeilComplex.nonempty_derivedLowerStar_comp_upperStar_iso_of_isProper`), so the
counit `i_! i^* E ⟶ E` is an isomorphism, `i^*` and the pullback to the complement jointly
detecting isomorphisms; and `i^* E ≅ Rq_* K` by proper base change along `i`, since `X'` is open
and closed in `b⁻¹(Y')`, on which `q` factors.

This is the comparison of the blueprint (`proposition-construction-independence-rf-shriek`,
`proposition-composition-base-change-rf-shriek--1`) behind the compatibilities of
`Rf₀! = Rḡ_* ∘ ī_!` (`AlgebraicGeometry.WeilComplex.derivedLowerShriek`):

- for a refinement `c' ⟶ c` of compactifications of `f`, `R^{c'} f_! ≅ R^c f_!`, hence the
  independence of the compactification
  (`AlgebraicGeometry.ProEtaleWeilSheaf.rightDerivedLowerShriekIsoOfCompactification`).
-/

@[expose] public section

-- A scheme lies over itself through the identity. Some imports also bring `specOverSpec` into
-- scope, which makes `Spec R` lie over itself through `Spec` of the algebra map `R → R`; give
-- the identity precedence, as in the files that do not import `specOverSpec`.
attribute [instance 1100] CategoryTheory.instOverClass

universe u

open CategoryTheory Limits Endofunctor Pretriangulated

namespace AlgebraicGeometry

open ProEtale

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

section ExtensionByZero

variable {U X : Scheme.{u}} [U.Over (Spec (CommRingCat.of k₀))]
  [X.Over (Spec (CommRingCat.of k₀))] (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
  [j.IsOver (Spec (CommRingCat.of k₀))]

omit [Fact (ringChar k₀ ≠ l)] in
/-- The derived extension by zero along a quasi-compact open immersion carries Weil complexes to
Weil complexes: it is exact and preserves constructibility
(`AlgebraicGeometry.WeilSheaf.isAdicConstructibleSheaf_extensionByZero`). -/
theorem WeilComplex.objectProperty_extensionByZero
    (K : _root_.DerivedCategory (ProEtaleWeilSheaf k₀ l U))
    (hK : WeilComplex.objectProperty k₀ l U K) :
    WeilComplex.objectProperty k₀ l X
      ((ProEtaleWeilSheaf.extensionByZero k₀ l j).mapDerivedCategory.obj K) :=
  ⟨(ProEtaleWeilSheaf.extensionByZero k₀ l j).bounded_mapDerivedCategory_obj hK.1,
    fun n ↦ (WeilSheaf.objectProperty k₀ l X).prop_of_iso
      (((ProEtaleWeilSheaf.extensionByZero k₀ l j).mapDerivedCategoryHomologyFunctorIso
        n).app K) (WeilSheaf.isAdicConstructibleSheaf_extensionByZero j _ (hK.2 n))⟩

/-- The extension by zero `j_!` of Weil complexes along a quasi-compact open immersion `j`: the
functor induced on derived categories by the exact extension by zero of pro-étale Weil
sheaves, restricted to Weil complexes. -/
noncomputable def WeilComplex.extensionByZero : WeilComplex k₀ l U ⥤ WeilComplex k₀ l X :=
  (WeilComplex.objectProperty k₀ l U).liftFullSubcategory (WeilComplex.objectProperty k₀ l X)
    (ProEtaleWeilSheaf.extensionByZero k₀ l j).mapDerivedCategory
    (WeilComplex.objectProperty_extensionByZero j)

end ExtensionByZero

section Vanishing

variable {X' W Z C : Scheme.{u}} [X'.Over (Spec (CommRingCat.of k₀))]
  [W.Over (Spec (CommRingCat.of k₀))] [Z.Over (Spec (CommRingCat.of k₀))]
  [C.Over (Spec (CommRingCat.of k₀))]
  (a : X' ⟶ W) [IsOpenImmersion a] [QuasiCompact a] [a.IsOver (Spec (CommRingCat.of k₀))]
  (b : W ⟶ Z) [IsProper b] [b.IsOver (Spec (CommRingCat.of k₀))]
  (ι : C ⟶ Z) [ι.IsOver (Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (Z ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (Z ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (C ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (C ↘ Spec (CommRingCat.of k₀))]

/-- For an open immersion `a`, a proper `b` and a morphism `ι` whose range misses that of
`a ≫ b`, the pullback along `ι` of `Rb_* a_! K` vanishes for a Weil complex `K`: by proper base
change it is `Rb'_*` of the pullback of `a_! K` to `W ×_Z C`, which misses the range of `a`. -/
lemma ProEtaleWeilSheaf.isZero_upperStar_obj_rightDerivedLowerStar_obj_extensionByZero_obj
    (h : Disjoint (Set.range (a ≫ b).base) (Set.range ι.base)) (K : WeilComplex k₀ l X') :
    IsZero ((ProEtaleWeilSheaf.upperStar k₀ l ι).mapDerivedCategory.obj
      ((ProEtaleWeilSheaf.lowerStar k₀ l b).rightDerivedFunctor.obj
        ((ProEtaleWeilSheaf.extensionByZero k₀ l a).mapDerivedCategory.obj K.obj))) := by
  let _ : (pullback b ι).Over (Spec (CommRingCat.of k₀)) :=
    OverClass.ofHom (pullback.snd b ι ≫ C ↘ Spec (CommRingCat.of k₀))
  have : (pullback.snd b ι).IsOver (Spec (CommRingCat.of k₀)) := ⟨rfl⟩
  have : (pullback.fst b ι).IsOver (Spec (CommRingCat.of k₀)) := ⟨by
    change pullback.fst b ι ≫ W ↘ Spec (CommRingCat.of k₀) =
      pullback.snd b ι ≫ C ↘ Spec (CommRingCat.of k₀)
    rw [← comp_over b, pullback.condition_assoc, comp_over ι]⟩
  obtain ⟨e⟩ := WeilComplex.nonempty_derivedLowerStar_comp_upperStar_iso_of_isProper
    (k₀ := k₀) (l := l) (f := b) (g := ι) (f' := pullback.snd b ι) (g' := pullback.fst b ι)
    inferInstance (IsPullback.of_hasPullback b ι)
  have hd : Disjoint (Set.range a.base) (Set.range (pullback.fst b ι).base) := by
    rw [Set.disjoint_left]
    rintro _ ⟨x, rfl⟩ ⟨p, hp⟩
    refine Set.disjoint_left.1 h ⟨x, rfl⟩ ⟨(pullback.snd b ι).base p, ?_⟩
    rw [← Scheme.Hom.comp_apply, ← pullback.condition, Scheme.Hom.comp_apply, hp,
      Scheme.Hom.comp_apply]
  have hN : IsZero ((WeilComplex.upperStar (pullback.fst b ι)).obj
      ((WeilComplex.extensionByZero a).obj K)) :=
    IsZero.of_full_of_faithful_of_isZero (ObjectProperty.ι _) _
      (ProEtaleWeilSheaf.isZero_mapDerivedCategory_upperStar_obj_extensionByZero_obj a
        (pullback.fst b ι) hd K.obj)
  exact (ObjectProperty.ι _).map_isZero
    (((WeilComplex.derivedLowerStar (pullback.snd b ι)).map_isZero hN).of_iso
      (e.app ((WeilComplex.extensionByZero a).obj K)))

end Vanishing

section Key

variable (k₀ l) in
/-- Extensions by zero of pro-étale Weil sheaves along equal open immersions are isomorphic. -/
noncomputable def ProEtaleWeilSheaf.extensionByZeroCongr {U X : Scheme.{u}}
    [U.Over (Spec (CommRingCat.of k₀))] [X.Over (Spec (CommRingCat.of k₀))] {φ φ' : U ⟶ X}
    [IsOpenImmersion φ] [IsOpenImmersion φ'] [φ.IsOver (Spec (CommRingCat.of k₀))]
    [φ'.IsOver (Spec (CommRingCat.of k₀))] (h : φ = φ') :
    ProEtaleWeilSheaf.extensionByZero k₀ l φ ≅ ProEtaleWeilSheaf.extensionByZero k₀ l φ' := by
  subst h
  exact Iso.refl _

variable {X' Y' W Z : Scheme.{u}} [X'.Over (Spec (CommRingCat.of k₀))]
  [Y'.Over (Spec (CommRingCat.of k₀))] [W.Over (Spec (CommRingCat.of k₀))]
  [Z.Over (Spec (CommRingCat.of k₀))]
  (a : X' ⟶ W) [IsOpenImmersion a] [QuasiCompact a] [a.IsOver (Spec (CommRingCat.of k₀))]
  (b : W ⟶ Z) [IsProper b] [b.IsOver (Spec (CommRingCat.of k₀))]
  (q : X' ⟶ Y') [IsProper q] [q.IsOver (Spec (CommRingCat.of k₀))]
  (i : Y' ⟶ Z) [IsOpenImmersion i] [QuasiCompact i] [i.IsOver (Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (Z ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (Z ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (Y' ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (Y' ↘ Spec (CommRingCat.of k₀))]

omit [IsProper q] [q.IsOver (Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (Y' ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (Y' ↘ Spec (CommRingCat.of k₀))] in
/-- Auxiliary form of
`ProEtaleWeilSheaf.isIso_counit_app_rightDerivedLowerStar_obj_extensionByZero_obj`,
for a given closed immersion `ι` complementary to `i`. -/
lemma ProEtaleWeilSheaf.isIso_counit_app_rightDerivedLowerStar_obj_extensionByZero_obj_aux
    {C : Scheme.{u}} [C.Over (Spec (CommRingCat.of k₀))] (ι : C ⟶ Z) [IsClosedImmersion ι]
    [ι.IsOver (Spec (CommRingCat.of k₀))] (h₁ : LocallyOfFiniteType (C ↘ Spec (CommRingCat.of k₀)))
    (h₂ : QuasiCompact (C ↘ Spec (CommRingCat.of k₀)))
    (hc : IsCompl (Set.range ι.base) (Set.range i.base)) (w : a ≫ b = q ≫ i)
    (K : WeilComplex k₀ l X') :
    IsIso ((ProEtaleWeilSheaf.derivedExtensionByZeroUpperStarAdjunction k₀ l i).counit.app
      ((ProEtaleWeilSheaf.lowerStar k₀ l b).rightDerivedFunctor.obj
        ((ProEtaleWeilSheaf.extensionByZero k₀ l a).mapDerivedCategory.obj K.obj))) := by
  refine ProEtaleWeilSheaf.isIso_of_isIso_upperStar_map ι i hc _ ?_ ?_
  · have hz₁ := ProEtaleWeilSheaf.isZero_mapDerivedCategory_upperStar_obj_extensionByZero_obj
      (k₀ := k₀) (l := l) i ι hc.disjoint.symm
      ((ProEtaleWeilSheaf.upperStar k₀ l i).mapDerivedCategory.obj
        ((ProEtaleWeilSheaf.lowerStar k₀ l b).rightDerivedFunctor.obj
          ((ProEtaleWeilSheaf.extensionByZero k₀ l a).mapDerivedCategory.obj K.obj)))
    have hz₂ := ProEtaleWeilSheaf.isZero_upperStar_obj_rightDerivedLowerStar_obj_extensionByZero_obj
      (k₀ := k₀) (l := l) a b ι ?_ K
    · exact isIso_of_source_target_iso_zero _ hz₁.isoZero hz₂.isoZero
    rw [w]
    refine Disjoint.mono_left ?_ hc.disjoint.symm
    rintro _ ⟨x, rfl⟩
    exact ⟨q.base x, (Scheme.Hom.comp_apply _ _ _).symm⟩
  · have h := (ProEtaleWeilSheaf.derivedExtensionByZeroUpperStarAdjunction k₀ l
      i).right_triangle_components ((ProEtaleWeilSheaf.lowerStar k₀ l b).rightDerivedFunctor.obj
        ((ProEtaleWeilSheaf.extensionByZero k₀ l a).mapDerivedCategory.obj K.obj))
    exact @IsIso.of_isIso_comp_left _ _ _ _ _ _ _ inferInstance (by rw [h]; infer_instance)

omit [IsProper q] [q.IsOver (Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (Y' ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (Y' ↘ Spec (CommRingCat.of k₀))] in
/-- For a commutative square `a ≫ b = q ≫ i` with `a`, `i` open immersions and `b`, `q` proper,
the counit `i_! i^* E ⟶ E` is an isomorphism for `E = Rb_* a_! K`, `K` a Weil complex: its
pullback along `i` is invertible, `D(i_!)` being fully faithful, and its pullback to the closed
complement of `i` is a morphism between zero objects. -/
lemma ProEtaleWeilSheaf.isIso_counit_app_rightDerivedLowerStar_obj_extensionByZero_obj
    (w : a ≫ b = q ≫ i) (K : WeilComplex k₀ l X') :
    IsIso ((ProEtaleWeilSheaf.derivedExtensionByZeroUpperStarAdjunction k₀ l i).counit.app
      ((ProEtaleWeilSheaf.lowerStar k₀ l b).rightDerivedFunctor.obj
        ((ProEtaleWeilSheaf.extensionByZero k₀ l a).mapDerivedCategory.obj K.obj))) := by
  let _ := OverClass.ofHom (i.closedComplement ≫ Z ↘ Spec (CommRingCat.of k₀))
  have : i.closedComplement.IsOver (Spec (CommRingCat.of k₀)) := ⟨rfl⟩
  refine ProEtaleWeilSheaf.isIso_counit_app_rightDerivedLowerStar_obj_extensionByZero_obj_aux
    a b q i i.closedComplement
    (inferInstanceAs (LocallyOfFiniteType (i.closedComplement ≫ Z ↘ Spec (CommRingCat.of k₀))))
    (inferInstanceAs (QuasiCompact (i.closedComplement ≫ Z ↘ Spec (CommRingCat.of k₀)))) ?_ w K
  rw [Scheme.Hom.range_closedComplement]
  exact isCompl_compl.symm

variable (k₀ l) in
/-- **The proper direct image of an extension by zero** (blueprint
`proposition-construction-independence-rf-shriek`): for a commutative square `a ≫ b = q ≫ i` of
`k₀`-schemes with `a`, `i` quasi-compact open immersions and `b`, `q` proper,
`Rb_* ∘ a_! ≅ i_! ∘ Rq_*` on Weil complexes. With `W' = W ×_Z Y'`, the counit
`i_! i^* E ⟶ E` is an isomorphism for `E = Rb_* a_! K`, `i^* Rb_* ≅ Rb'_* k^*` by proper base
change, `k^* a_! ≅ a'_!` for the factorization `a = a' ≫ k` through the open immersion
`k : W' ⟶ W`, and `a'_! ≅ a'_*` since `a'` is also proper (it is a section of `b'` over `X'`),
so that `Rb'_* a'_! ≅ R(a' ≫ b')_* = Rq_*`. -/
noncomputable def ProEtaleWeilSheaf.rightDerivedLowerStarExtensionByZeroIso
    (w : a ≫ b = q ≫ i) :
    (WeilComplex.objectProperty k₀ l X').ι ⋙
        (ProEtaleWeilSheaf.extensionByZero k₀ l a).mapDerivedCategory ⋙
          (ProEtaleWeilSheaf.lowerStar k₀ l b).rightDerivedFunctor ≅
      (WeilComplex.objectProperty k₀ l X').ι ⋙
        (ProEtaleWeilSheaf.lowerStar k₀ l q).rightDerivedFunctor ⋙
          (ProEtaleWeilSheaf.extensionByZero k₀ l i).mapDerivedCategory := by
  -- the fibre product `W' = W ×_Z Y'` and the factorization `a = a' ≫ k`
  let _ : (pullback b i).Over (Spec (CommRingCat.of k₀)) :=
    OverClass.ofHom (pullback.snd b i ≫ Y' ↘ Spec (CommRingCat.of k₀))
  have : (pullback.snd b i).IsOver (Spec (CommRingCat.of k₀)) := ⟨rfl⟩
  have : (pullback.fst b i).IsOver (Spec (CommRingCat.of k₀)) := ⟨by
    change pullback.fst b i ≫ W ↘ Spec (CommRingCat.of k₀) =
      pullback.snd b i ≫ Y' ↘ Spec (CommRingCat.of k₀)
    rw [← comp_over b, pullback.condition_assoc, comp_over i]⟩
  let a' : X' ⟶ pullback b i := pullback.lift a q w
  have ha' : a' ≫ pullback.fst b i = a := pullback.lift_fst _ _ _
  have hq : a' ≫ pullback.snd b i = q := pullback.lift_snd _ _ _
  have : IsOpenImmersion a' :=
    have : IsOpenImmersion (a' ≫ pullback.fst b i) := by rw [ha']; infer_instance
    IsOpenImmersion.of_comp a' (pullback.fst b i)
  have : IsProper a' :=
    have : IsProper (a' ≫ pullback.snd b i) := by rw [hq]; infer_instance
    IsProper.of_comp a' (pullback.snd b i)
  have : a'.IsOver (Spec (CommRingCat.of k₀)) := ⟨by
    change a' ≫ pullback.snd b i ≫ Y' ↘ Spec (CommRingCat.of k₀) = _
    rw [reassoc_of% hq, comp_over q]⟩
  let F := (WeilComplex.objectProperty k₀ l X').ι ⋙
    (ProEtaleWeilSheaf.extensionByZero k₀ l a).mapDerivedCategory ⋙
      (ProEtaleWeilSheaf.lowerStar k₀ l b).rightDerivedFunctor
  -- the counit `i_! i^* E ⟶ E` is an isomorphism
  have : IsIso (Functor.whiskerLeft F
      (ProEtaleWeilSheaf.derivedExtensionByZeroUpperStarAdjunction k₀ l i).counit) := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro K
    exact ProEtaleWeilSheaf.isIso_counit_app_rightDerivedLowerStar_obj_extensionByZero_obj
      a b q i w K
  let iso₁ : F ⋙ (ProEtaleWeilSheaf.upperStar k₀ l i).mapDerivedCategory ⋙
      (ProEtaleWeilSheaf.extensionByZero k₀ l i).mapDerivedCategory ≅ F :=
    asIso (Functor.whiskerLeft F
      (ProEtaleWeilSheaf.derivedExtensionByZeroUpperStarAdjunction k₀ l i).counit) ≪≫
      F.rightUnitor
  -- proper base change along `i`
  let e := (WeilComplex.nonempty_derivedLowerStar_comp_upperStar_iso_of_isProper
    (k₀ := k₀) (l := l) (f := b) (g := i) (f' := pullback.snd b i) (g' := pullback.fst b i)
    inferInstance (IsPullback.of_hasPullback b i)).some
  let iso₂ : F ⋙ (ProEtaleWeilSheaf.upperStar k₀ l i).mapDerivedCategory ≅
      ((WeilComplex.objectProperty k₀ l X').ι ⋙
        (ProEtaleWeilSheaf.extensionByZero k₀ l a).mapDerivedCategory ⋙
          (ProEtaleWeilSheaf.upperStar k₀ l (pullback.fst b i)).mapDerivedCategory) ⋙
        (ProEtaleWeilSheaf.lowerStar k₀ l (pullback.snd b i)).rightDerivedFunctor :=
    NatIso.ofComponents
      (fun K ↦ (ObjectProperty.ι _).mapIso (e.app ((WeilComplex.extensionByZero a).obj K)))
      (fun f ↦ congrArg (fun φ ↦ (ObjectProperty.ι _).map φ)
        (e.hom.naturality ((WeilComplex.extensionByZero a).map f)))
  -- `k^* a_! ≅ a'_!`
  let iso₃ : (WeilComplex.objectProperty k₀ l X').ι ⋙
        (ProEtaleWeilSheaf.extensionByZero k₀ l a).mapDerivedCategory ⋙
          (ProEtaleWeilSheaf.upperStar k₀ l (pullback.fst b i)).mapDerivedCategory ≅
      (WeilComplex.objectProperty k₀ l X').ι ⋙
        (ProEtaleWeilSheaf.extensionByZero k₀ l a').mapDerivedCategory :=
    Functor.isoWhiskerLeft _
      (Functor.isoWhiskerRight (Functor.mapDerivedCategoryNatIso
          (ProEtaleWeilSheaf.extensionByZeroCongr k₀ l ha').symm ≪≫
          ProEtaleWeilSheaf.mapDerivedCategoryExtensionByZeroCompIso k₀ l a' (pullback.fst b i))
        _ ≪≫ Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft _ (asIso (ProEtaleWeilSheaf.derivedExtensionByZeroUpperStarAdjunction
          k₀ l (pullback.fst b i)).unit).symm ≪≫ Functor.rightUnitor _)
  -- `Rb'_* a'_! ≅ Rq_*`
  let iso₄ : (ProEtaleWeilSheaf.extensionByZero k₀ l a').mapDerivedCategory ⋙
      (ProEtaleWeilSheaf.lowerStar k₀ l (pullback.snd b i)).rightDerivedFunctor ≅
      (ProEtaleWeilSheaf.lowerStar k₀ l q).rightDerivedFunctor :=
    Functor.isoWhiskerRight
        ((ProEtaleWeilSheaf.extensionByZero k₀ l
          a').rightDerivedFunctorIsoMapDerivedCategory.symm ≪≫
          Functor.rightDerivedFunctorNatIso
            (asIso (ProEtaleWeilSheaf.extensionByZeroToLowerStar k₀ l a'))) _ ≪≫
      (ProEtaleWeilSheaf.rightDerivedLowerStarCompIso k₀ l a' (pullback.snd b i)).symm ≪≫
      Functor.rightDerivedFunctorNatIso (ProEtaleWeilSheaf.lowerStarCongr k₀ l hq)
  exact iso₁.symm ≪≫ (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight iso₂ _ ≪≫
    Functor.isoWhiskerRight (Functor.isoWhiskerRight iso₃ _) _ ≪≫
    Functor.isoWhiskerRight (Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ iso₄) _ ≪≫
    Functor.associator _ _ _

end Key

section Independence

attribute [local instance] Compactification.over

variable (k₀ l) in
/-- The total right derived functor of the pushforward along the identity of pro-étale Weil
sheaves is isomorphic to the identity functor. -/
noncomputable def ProEtaleWeilSheaf.rightDerivedLowerStarIdIso (X : Scheme.{u})
    [X.Over (Spec (CommRingCat.of k₀))] :
    (ProEtaleWeilSheaf.lowerStar k₀ l (𝟙 X)).rightDerivedFunctor ≅ 𝟭 _ :=
  Functor.rightDerivedFunctorNatIso (ProEtaleWeilSheaf.lowerStarIdIso k₀ l X) ≪≫
    (𝟭 _).rightDerivedFunctorIsoMapDerivedCategory ≪≫ Functor.mapDerivedCategoryIdIso _

variable {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [Y.Over (Spec (CommRingCat.of k₀))] {f : X ⟶ Y} [f.IsOver (Spec (CommRingCat.of k₀))]
  [QuasiCompact f] [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))]

variable (k₀ l) in
/-- **The direct image with compact support does not change under refinement of the
compactification** (blueprint `proposition-construction-independence-rf-shriek`): for a refinement
`r : c ⟶ d` of compactifications of `f`, `R^c f_! ≅ R^d f_!` on Weil complexes, since
`Rr_* ∘ c.i_! ≅ d.i_!`
(`AlgebraicGeometry.ProEtaleWeilSheaf.rightDerivedLowerStarExtensionByZeroIso`
for the square `c.i ≫ r = 𝟙 ≫ d.i`) and `c.g = r ≫ d.g`. -/
noncomputable def ProEtaleWeilSheaf.rightDerivedLowerShriekIsoOfRefinement
    {c d : Compactification f} (r : c.Refinement d) :
    (WeilComplex.objectProperty k₀ l X).ι ⋙ ProEtaleWeilSheaf.rightDerivedLowerShriek k₀ l f c ≅
      (WeilComplex.objectProperty k₀ l X).ι ⋙
        ProEtaleWeilSheaf.rightDerivedLowerShriek k₀ l f d := by
  have := c.locallyOfFiniteType
  have : LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀)) := by
    rw [← comp_over f (Spec (CommRingCat.of k₀))]
    infer_instance
  have : QuasiCompact (X ↘ Spec (CommRingCat.of k₀)) := by
    rw [← comp_over f (Spec (CommRingCat.of k₀))]
    infer_instance
  have : LocallyOfFiniteType (d.Z ↘ Spec (CommRingCat.of k₀)) :=
    inferInstanceAs (LocallyOfFiniteType (d.g ≫ Y ↘ Spec (CommRingCat.of k₀)))
  have : QuasiCompact (d.Z ↘ Spec (CommRingCat.of k₀)) :=
    inferInstanceAs (QuasiCompact (d.g ≫ Y ↘ Spec (CommRingCat.of k₀)))
  have : QuasiCompact c.i := c.quasiCompact_openImmersion inferInstance
  have : QuasiCompact d.i := d.quasiCompact_openImmersion inferInstance
  have : r.hom.IsOver (Spec (CommRingCat.of k₀)) := ⟨by
    change r.hom ≫ d.g ≫ Y ↘ Spec (CommRingCat.of k₀) = c.g ≫ Y ↘ Spec (CommRingCat.of k₀)
    rw [reassoc_of% r.hom_g]⟩
  exact Functor.isoWhiskerLeft _ (Functor.isoWhiskerLeft _
      (Functor.rightDerivedFunctorNatIso (ProEtaleWeilSheaf.lowerStarCongr k₀ l r.hom_g.symm) ≪≫
        ProEtaleWeilSheaf.rightDerivedLowerStarCompIso k₀ l r.hom d.g) ≪≫
      (Functor.associator _ _ _).symm) ≪≫ (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (ProEtaleWeilSheaf.rightDerivedLowerStarExtensionByZeroIso k₀ l c.i
      r.hom (𝟙 X) d.i (by rw [r.i_hom, Category.id_comp])) _ ≪≫
    Functor.isoWhiskerRight (Functor.isoWhiskerLeft _ (
      Functor.isoWhiskerRight (ProEtaleWeilSheaf.rightDerivedLowerStarIdIso k₀ l X) _ ≪≫
      Functor.leftUnitor _)) _ ≪≫ Functor.associator _ _ _

variable (k₀ l) in
/-- **Independence of the compactification** (blueprint
`proposition-construction-independence-rf-shriek`, `prop-functor-package` clause 2): for two
compactifications `c`, `d` of `f`, `R^c f_! ≅ R^d f_!` on Weil complexes, through their common
refinement (`AlgebraicGeometry.Compactification.inf`). -/
noncomputable def ProEtaleWeilSheaf.rightDerivedLowerShriekIsoOfCompactification
    (c d : Compactification f) :
    (WeilComplex.objectProperty k₀ l X).ι ⋙ ProEtaleWeilSheaf.rightDerivedLowerShriek k₀ l f c ≅
      (WeilComplex.objectProperty k₀ l X).ι ⋙ ProEtaleWeilSheaf.rightDerivedLowerShriek k₀ l f d :=
  (ProEtaleWeilSheaf.rightDerivedLowerShriekIsoOfRefinement k₀ l
      (Compactification.infFst c d)).symm ≪≫
    ProEtaleWeilSheaf.rightDerivedLowerShriekIsoOfRefinement k₀ l (Compactification.infSnd c d)

variable [IsSeparated f] [LocallyOfFiniteType f] [QuasiSeparated (Y ↘ Spec (CommRingCat.of k₀))]

variable (k₀ l) in
/-- The direct image with compact support `Rf₀!` of Weil complexes, defined through the chosen
compactification of `f`, is computed by any compactification `c` of `f`:
`Rf₀! ≅ R^c f_! = Rc.g_* ∘ c.i_!` (`prop-functor-package`, clause 2). -/
noncomputable def WeilComplex.derivedLowerShriekCompιIso (c : Compactification f) :
    WeilComplex.derivedLowerShriek k₀ l f ⋙ (WeilComplex.objectProperty k₀ l Y).ι ≅
      (WeilComplex.objectProperty k₀ l X).ι ⋙ ProEtaleWeilSheaf.rightDerivedLowerShriek k₀ l f c :=
  ObjectProperty.liftFullSubcategoryCompιIso _ _ _ _ ≪≫
    ProEtaleWeilSheaf.rightDerivedLowerShriekIsoOfCompactification k₀ l _ c

end Independence

section Flexible

variable {X Y Z : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [Y.Over (Spec (CommRingCat.of k₀))] {f : X ⟶ Y} [f.IsOver (Spec (CommRingCat.of k₀))]
  [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))]
  [QuasiSeparated (Y ↘ Spec (CommRingCat.of k₀))]

/-- The direct image with compact support `Rf₀!` of Weil complexes is computed by any
factorization `f = i ≫ g` of `f` into an open immersion `i` followed by a proper morphism `g`
of `k₀`-schemes: `Rf₀! ≅ Rg_* ∘ i_!` (`prop-functor-package`, clause 2). -/
theorem WeilComplex.nonempty_derivedLowerShriek_comp_ι_iso [hZ : Z.Over (Spec (CommRingCat.of k₀))]
    (i : X ⟶ Z) (g : Z ⟶ Y) [IsOpenImmersion i] [IsProper g]
    [i.IsOver (Spec (CommRingCat.of k₀))] [g.IsOver (Spec (CommRingCat.of k₀))]
    (h : f = i ≫ g) :
    Nonempty (WeilComplex.derivedLowerShriek k₀ l f ⋙ (WeilComplex.objectProperty k₀ l Y).ι ≅
      (WeilComplex.objectProperty k₀ l X).ι ⋙
        (ProEtaleWeilSheaf.extensionByZero k₀ l i).mapDerivedCategory ⋙
          (ProEtaleWeilSheaf.lowerStar k₀ l g).rightDerivedFunctor) := by
  let c : Compactification f := ⟨Z, g, i, h, inferInstance, inferInstance⟩
  have e : hZ = Compactification.over (k₀ := k₀) c := by
    have hg := comp_over g (Spec (CommRingCat.of k₀))
    revert hg
    cases hZ
    intro hg
    exact congrArg OverClass.ofHom hg.symm
  subst e
  exact ⟨WeilComplex.derivedLowerShriekCompιIso k₀ l c⟩

end Flexible

section OpenImmersion

variable {U X : Scheme.{u}} [U.Over (Spec (CommRingCat.of k₀))]
  [X.Over (Spec (CommRingCat.of k₀))] (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
  [j.IsOver (Spec (CommRingCat.of k₀))]

instance : (WeilComplex.extensionByZero (k₀ := k₀) (l := l) j).Full :=
  have := (ProEtaleWeilSheaf.fullyFaithfulMapDerivedCategoryExtensionByZero (k₀ := k₀) (l := l)
    j).full
  ObjectProperty.liftFullSubcategory_full _ _ _ _

instance : (WeilComplex.extensionByZero (k₀ := k₀) (l := l) j).Faithful :=
  have := (ProEtaleWeilSheaf.fullyFaithfulMapDerivedCategoryExtensionByZero (k₀ := k₀) (l := l)
    j).faithful
  ObjectProperty.liftFullSubcategory_faithful _ _ _ _

/-- The adjunction `j_! ⊣ j^*` of Weil complexes along a quasi-compact open immersion `j`, the
restriction of `AlgebraicGeometry.ProEtaleWeilSheaf.derivedExtensionByZeroUpperStarAdjunction`. -/
noncomputable def WeilComplex.extensionByZeroUpperStarAdjunction :
    WeilComplex.extensionByZero (k₀ := k₀) (l := l) j ⊣ WeilComplex.upperStar j :=
  (ProEtaleWeilSheaf.derivedExtensionByZeroUpperStarAdjunction k₀ l j).restrictFullyFaithful
    (ObjectProperty.fullyFaithfulι _) (ObjectProperty.fullyFaithfulι _) (Iso.refl _) (Iso.refl _)

/-- The unit `K ⟶ j^* j_! K` of Weil complexes is an isomorphism: `j_!` is fully faithful. -/
instance WeilComplex.isIso_extensionByZeroUpperStarAdjunction_unit :
    IsIso (WeilComplex.extensionByZeroUpperStarAdjunction (k₀ := k₀) (l := l) j).unit :=
  Adjunction.unit_isIso_of_L_fully_faithful _

variable [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))] [QuasiSeparated (X ↘ Spec (CommRingCat.of k₀))]

/-- **The direct image with compact support along an open immersion is the extension by zero**
(`prop-functor-package`, clause 2, for the compactification `U ⟶[j] X ⟶[𝟙] X`):
`Rj₀! ≅ j_!` on Weil complexes. -/
theorem WeilComplex.nonempty_derivedLowerShriek_iso_extensionByZero :
    Nonempty (WeilComplex.derivedLowerShriek k₀ l j ≅ WeilComplex.extensionByZero j) := by
  obtain ⟨e⟩ := WeilComplex.nonempty_derivedLowerShriek_comp_ι_iso (k₀ := k₀) (l := l) (f := j) j
    (𝟙 X) (Category.comp_id j).symm
  exact ⟨((WeilComplex.objectProperty k₀ l X).fullyFaithfulι.whiskeringRight _).preimageIso
    (e ≪≫ Functor.isoWhiskerLeft _ (Functor.isoWhiskerLeft _
      (ProEtaleWeilSheaf.rightDerivedLowerStarIdIso k₀ l X) ≪≫ Functor.rightUnitor _) ≪≫
      (ObjectProperty.liftFullSubcategoryCompιIso _ _ _ _).symm)⟩

end OpenImmersion

section BaseChange

variable (k₀ l) in
/-- Pullbacks of pro-étale Weil sheaves along equal morphisms are isomorphic. -/
noncomputable def ProEtaleWeilSheaf.upperStarCongr {X Y : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of k₀))] [Y.Over (Spec (CommRingCat.of k₀))] {φ φ' : X ⟶ Y}
    [φ.IsOver (Spec (CommRingCat.of k₀))] [φ'.IsOver (Spec (CommRingCat.of k₀))] (h : φ = φ') :
    ProEtaleWeilSheaf.upperStar k₀ l φ ≅ ProEtaleWeilSheaf.upperStar k₀ l φ' := by
  subst h
  exact Iso.refl _

variable (k₀ l) in
/-- The derived pullback along a composite is the composite of the derived pullbacks. -/
noncomputable def ProEtaleWeilSheaf.mapDerivedCategoryUpperStarCompIso {X Y Z : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of k₀))] [Y.Over (Spec (CommRingCat.of k₀))]
    [Z.Over (Spec (CommRingCat.of k₀))] (φ : X ⟶ Y) (ψ : Y ⟶ Z)
    [φ.IsOver (Spec (CommRingCat.of k₀))] [ψ.IsOver (Spec (CommRingCat.of k₀))] :
    (ProEtaleWeilSheaf.upperStar k₀ l (φ ≫ ψ)).mapDerivedCategory ≅
      (ProEtaleWeilSheaf.upperStar k₀ l ψ).mapDerivedCategory ⋙
        (ProEtaleWeilSheaf.upperStar k₀ l φ).mapDerivedCategory :=
  Functor.mapDerivedCategoryNatIso (ProEtaleWeilSheaf.upperStarCompIso k₀ l φ ψ) ≪≫
    (Functor.mapDerivedCategoryCompIso _ _).symm

variable {X X' Z Z' : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [X'.Over (Spec (CommRingCat.of k₀))] [Z.Over (Spec (CommRingCat.of k₀))]
  [Z'.Over (Spec (CommRingCat.of k₀))]
  (g : X' ⟶ X) [g.IsOver (Spec (CommRingCat.of k₀))]
  (i' : X' ⟶ Z') [IsOpenImmersion i'] [QuasiCompact i'] [i'.IsOver (Spec (CommRingCat.of k₀))]
  (i : X ⟶ Z) [IsOpenImmersion i] [i.IsOver (Spec (CommRingCat.of k₀))]
  (p : Z' ⟶ Z) [p.IsOver (Spec (CommRingCat.of k₀))]

omit [Fact (ringChar k₀ ≠ l)] [g.IsOver (Spec (CommRingCat.of k₀))] in
/-- Auxiliary form of
`AlgebraicGeometry.ProEtaleWeilSheaf.isIso_counit_app_upperStar_obj_extensionByZero_obj`, for a
given closed immersion `ι` complementary to `i'`. -/
lemma ProEtaleWeilSheaf.isIso_counit_app_upperStar_obj_extensionByZero_obj_aux
    (hsq : IsPullback g i' i p) {C : Scheme.{u}} [C.Over (Spec (CommRingCat.of k₀))]
    (ι : C ⟶ Z') [IsClosedImmersion ι] [ι.IsOver (Spec (CommRingCat.of k₀))]
    (hc : IsCompl (Set.range ι.base) (Set.range i'.base))
    (K : _root_.DerivedCategory (ProEtaleWeilSheaf k₀ l X)) :
    IsIso ((ProEtaleWeilSheaf.derivedExtensionByZeroUpperStarAdjunction k₀ l i').counit.app
      ((ProEtaleWeilSheaf.upperStar k₀ l p).mapDerivedCategory.obj
        ((ProEtaleWeilSheaf.extensionByZero k₀ l i).mapDerivedCategory.obj K))) := by
  refine ProEtaleWeilSheaf.isIso_of_isIso_upperStar_map ι i' hc _ ?_ ?_
  · have hz₁ := ProEtaleWeilSheaf.isZero_mapDerivedCategory_upperStar_obj_extensionByZero_obj
      (k₀ := k₀) (l := l) i' ι hc.disjoint.symm
      ((ProEtaleWeilSheaf.upperStar k₀ l i').mapDerivedCategory.obj
        ((ProEtaleWeilSheaf.upperStar k₀ l p).mapDerivedCategory.obj
          ((ProEtaleWeilSheaf.extensionByZero k₀ l i).mapDerivedCategory.obj K)))
    have hd : Disjoint (Set.range i.base) (Set.range (ι ≫ p).base) := by
      rw [Set.disjoint_left]
      rintro _ ⟨x, rfl⟩ ⟨z, hz⟩
      have : ι.base z ∈ Set.range i'.base := by
        rw [range_snd_of_isPullback hsq, Set.mem_preimage, ← Scheme.Hom.comp_apply, hz]
        exact ⟨x, rfl⟩
      exact Set.disjoint_left.1 hc.disjoint ⟨z, rfl⟩ this
    have hz₂ := (ProEtaleWeilSheaf.isZero_mapDerivedCategory_upperStar_obj_extensionByZero_obj
      (k₀ := k₀) (l := l) i (ι ≫ p) hd K).of_iso
        ((ProEtaleWeilSheaf.mapDerivedCategoryUpperStarCompIso k₀ l ι p).app _).symm
    exact isIso_of_source_target_iso_zero _ hz₁.isoZero hz₂.isoZero
  · have h := (ProEtaleWeilSheaf.derivedExtensionByZeroUpperStarAdjunction k₀ l
      i').right_triangle_components ((ProEtaleWeilSheaf.upperStar k₀ l p).mapDerivedCategory.obj
        ((ProEtaleWeilSheaf.extensionByZero k₀ l i).mapDerivedCategory.obj K))
    exact @IsIso.of_isIso_comp_left _ _ _ _ _ _ _ inferInstance (by rw [h]; infer_instance)

variable (k₀ l) in
/-- **Base change for the extension by zero** of pro-étale Weil sheaves, on derived categories:
for a cartesian square `g ≫ i = i' ≫ p` with `i` and `i'` open immersions,
`D(p^*) ∘ D(i_!) ≅ D(i'_!) ∘ D(g^*)`. The counit `i'_! i'^* E ⟶ E` is an isomorphism for
`E = p^* i_! K`, which vanishes off the range of `i'`, and `i'^* p^* i_! ≅ g^* i^* i_! ≅ g^*`. -/
noncomputable def ProEtaleWeilSheaf.mapDerivedCategoryExtensionByZeroUpperStarIso
    (hsq : IsPullback g i' i p) :
    (ProEtaleWeilSheaf.extensionByZero k₀ l i).mapDerivedCategory ⋙
        (ProEtaleWeilSheaf.upperStar k₀ l p).mapDerivedCategory ≅
      (ProEtaleWeilSheaf.upperStar k₀ l g).mapDerivedCategory ⋙
        (ProEtaleWeilSheaf.extensionByZero k₀ l i').mapDerivedCategory := by
  have : IsIso (Functor.whiskerLeft ((ProEtaleWeilSheaf.extensionByZero k₀ l i).mapDerivedCategory ⋙
        (ProEtaleWeilSheaf.upperStar k₀ l p).mapDerivedCategory)
      (ProEtaleWeilSheaf.derivedExtensionByZeroUpperStarAdjunction k₀ l i').counit) := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro K
    let _ := OverClass.ofHom (i'.closedComplement ≫ Z' ↘ Spec (CommRingCat.of k₀))
    have : i'.closedComplement.IsOver (Spec (CommRingCat.of k₀)) := ⟨rfl⟩
    refine ProEtaleWeilSheaf.isIso_counit_app_upperStar_obj_extensionByZero_obj_aux g i' i p hsq
      i'.closedComplement ?_ K
    rw [Scheme.Hom.range_closedComplement]
    exact isCompl_compl.symm
  exact (asIso (Functor.whiskerLeft _
      (ProEtaleWeilSheaf.derivedExtensionByZeroUpperStarAdjunction k₀ l i').counit) ≪≫
      Functor.rightUnitor _).symm ≪≫
    Functor.isoWhiskerRight (Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _
      ((ProEtaleWeilSheaf.mapDerivedCategoryUpperStarCompIso k₀ l i' p).symm ≪≫
        Functor.mapDerivedCategoryNatIso (ProEtaleWeilSheaf.upperStarCongr k₀ l hsq.w.symm) ≪≫
        ProEtaleWeilSheaf.mapDerivedCategoryUpperStarCompIso k₀ l g i) ≪≫
      (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight
        (asIso (ProEtaleWeilSheaf.derivedExtensionByZeroUpperStarAdjunction k₀ l i).unit).symm _ ≪≫
      Functor.leftUnitor _) _

end BaseChange

end AlgebraicGeometry
