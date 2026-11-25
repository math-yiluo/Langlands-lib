/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ComparisonUpperStarSectionCoherence
public import WeilConjectures.SmoothPurity.Section.ProEtaleDeformation
public import WeilConjectures.EtaleCohomology.Purity.Smooth.SectionInvariantCtf

/-!
# The pro-étale constancy comparison: normalization, uniqueness and base change

Let `κ : F ≅ La^* 𝒞(g, s)` be the constancy comparison of the pro-étale family object of a
deformation to the normal cone
(`AlgebraicGeometry.Scheme.Hom.DeformationToNormalConeData.proEtaleFamilyObjectIso`). This file
proves the pro-étale forms of `lemma-section-normal-bundle--1` (3) and (4):

* `κ` restricts at `t = 1` to the fibre identification `θ₁ : Li₁^* F ≅ 𝒞(g, s)`
  (`proEtaleFamilyObjectIso_normalization`);
* it is the only comparison doing so (`eq_proEtaleFamilyObjectIso`);
* along a base change `u : B' ⟶ B` its restriction is the only comparison restricting to `Lu^* θ₁`
  at `t = 1` (`proEtaleFamilyObjectIso_baseChange`).

The normalization is transported from the étale one through the compatibility of the
commutations `D(ν^*) ⋙ Lg^* ≅ Lg^* ⋙ D(ν^*)` with the section isomorphisms `Li^* La^* ≅ 𝟭`
(`AlgebraicGeometry.ProEtale.derivedComparisonUpperStarUpperStarIso_inv_app_compSectionIso`).
The uniqueness statements are transported from `𝔸¹`-invariance on the étale site
(`AlgebraicGeometry.Etale.eq_of_leftDerivedUpperStar_oneSection_eq`), `D(ν^*)` being fully
faithful on bounded below complexes.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

attribute [local instance] Etale.neZero_ringChar_of_finite

namespace ProEtale

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] {Y : Scheme.{u}} [HasInvertibleExponent Λ Y]

/-- Blueprint `lemma-section-normal-bundle--1`, pro-étale, on complexes of étale origin: *invariance
along the line.* Let `F` on `𝔸¹_Y` be invertible and `C` on `Y` be étale complexes such that `F`,
`La^* C` and `Li₁^* La^* C` are bounded below. Two isomorphisms `α, β : F' ≅ La^* C'` of pro-étale
complexes, for `F' ≅ ν^* F` and `C' ≅ ν^* C`, with `Li₁^* α = Li₁^* β` are equal: `D(ν^*)` is
fully faithful on bounded below complexes, which reduces the statement to the étale one
(`AlgebraicGeometry.Etale.eq_of_leftDerivedUpperStar_oneSection_eq`). -/
theorem eq_of_leftDerivedUpperStar_oneSection_eq
    (F : _root_.DerivedCategory
      (Sheaf 𝔸(ULift.{u} (Fin 1); Y).smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (C : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hF : Etale.DerivedCategory.isInvertible Λ 𝔸(ULift.{u} (Fin 1); Y) F)
    (hFp : _root_.DerivedCategory.TStructure.t.plus F)
    (hCp : _root_.DerivedCategory.TStructure.t.plus
      ((Etale.upperStar (ModuleCat.{u + 1} Λ)
        (𝔸(ULift.{u} (Fin 1); Y) ↘ Y)).leftDerivedFunctor.obj C))
    (hC₁ : _root_.DerivedCategory.TStructure.t.plus
      ((Etale.upperStar (ModuleCat.{u + 1} Λ)
        (AffineSpace.oneSection (ULift.{u} (Fin 1)) Y)).leftDerivedFunctor.obj
        ((Etale.upperStar (ModuleCat.{u + 1} Λ)
          (𝔸(ULift.{u} (Fin 1); Y) ↘ Y)).leftDerivedFunctor.obj C)))
    {F' : _root_.DerivedCategory
      (Sheaf (Scheme.ProEt.topology 𝔸(ULift.{u} (Fin 1); Y)) (ModuleCat.{u + 1} Λ))}
    {C' : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} Λ))}
    (eF : F' ≅ (comparisonUpperStar (ModuleCat.{u + 1} Λ) _).mapDerivedCategory.obj F)
    (eC : C' ≅ (comparisonUpperStar (ModuleCat.{u + 1} Λ) Y).mapDerivedCategory.obj C)
    (α β : F' ≅
      (ProEtale.upperStar (ModuleCat.{u + 1} Λ)
        (𝔸(ULift.{u} (Fin 1); Y) ↘ Y)).leftDerivedFunctor.obj C')
    (h : (ProEtale.upperStar (ModuleCat.{u + 1} Λ)
        (AffineSpace.oneSection (ULift.{u} (Fin 1)) Y)).leftDerivedFunctor.map α.hom =
      (ProEtale.upperStar (ModuleCat.{u + 1} Λ)
        (AffineSpace.oneSection (ULift.{u} (Fin 1)) Y)).leftDerivedFunctor.map β.hom) :
    α = β := by
  let a := 𝔸(ULift.{u} (Fin 1); Y) ↘ Y
  let i₁ := AffineSpace.oneSection (ULift.{u} (Fin 1)) Y
  let ν := (comparisonUpperStar (ModuleCat.{u + 1} Λ) Y).mapDerivedCategory
  let ν' := (comparisonUpperStar (ModuleCat.{u + 1} Λ) 𝔸(ULift.{u} (Fin 1); Y)).mapDerivedCategory
  let La := (Etale.upperStar (ModuleCat.{u + 1} Λ) a).leftDerivedFunctor
  let Li := (Etale.upperStar (ModuleCat.{u + 1} Λ) i₁).leftDerivedFunctor
  let Lpa := (ProEtale.upperStar (ModuleCat.{u + 1} Λ) a).leftDerivedFunctor
  let Lpi := (ProEtale.upperStar (ModuleCat.{u + 1} Λ) i₁).leftDerivedFunctor
  let da := derivedComparisonUpperStarUpperStarIso (ModuleCat.{u + 1} Λ) a
  let di := derivedComparisonUpperStarUpperStarIso (ModuleCat.{u + 1} Λ) i₁
  -- the comparisons read on `ν^* F ⟶ ν^* La^* C`
  let toMor (γ : F' ≅ Lpa.obj C') : ν'.obj F ⟶ ν'.obj (La.obj C) :=
    eF.inv ≫ γ.hom ≫ Lpa.map eC.hom ≫ da.hom.app C
  let invMor (γ : F' ≅ Lpa.obj C') : ν'.obj (La.obj C) ⟶ ν'.obj F :=
    da.inv.app C ≫ Lpa.map eC.inv ≫ γ.inv ≫ eF.hom
  have b₁ := bijective_comparisonUpperStar_mapDerivedCategory_map F (La.obj C) hCp
  have b₂ := bijective_comparisonUpperStar_mapDerivedCategory_map (La.obj C) F hFp
  have b₃ := bijective_comparisonUpperStar_mapDerivedCategory_map F F hFp
  have b₄ := bijective_comparisonUpperStar_mapDerivedCategory_map (La.obj C) (La.obj C) hCp
  have b₅ := bijective_comparisonUpperStar_mapDerivedCategory_map (Li.obj F) (Li.obj (La.obj C)) hC₁
  -- the étale comparison underlying `γ`
  let et (γ : F' ≅ Lpa.obj C') : F ≅ La.obj C :=
    { hom := (b₁.2 (toMor γ)).choose
      inv := (b₂.2 (invMor γ)).choose
      hom_inv_id := b₃.1 (by
        simp only [Functor.map_comp, CategoryTheory.Functor.map_id, (b₁.2 (toMor γ)).choose_spec,
          (b₂.2 (invMor γ)).choose_spec, toMor, invMor, Category.assoc, Iso.hom_inv_id_app_assoc,
          ← Functor.map_comp_assoc, Iso.hom_inv_id]
        simp)
      inv_hom_id := b₄.1 (by
        simp only [Functor.map_comp, CategoryTheory.Functor.map_id, (b₁.2 (toMor γ)).choose_spec,
          (b₂.2 (invMor γ)).choose_spec, toMor, invMor, Category.assoc]
        simp [← Functor.map_comp_assoc]
        rfl) }
  have hν (γ : F' ≅ Lpa.obj C') : ν'.map (et γ).hom = toMor γ := (b₁.2 (toMor γ)).choose_spec
  -- `Li₁^*` of the étale comparisons agree
  have hi (γ : F' ≅ Lpa.obj C') : ν.map (Li.map (et γ).hom) =
      di.inv.app F ≫ Lpi.map (toMor γ) ≫ di.hom.app _ := by
    rw [← hν]
    have := di.hom.naturality (et γ).hom
    simp only [Functor.comp_obj, Functor.comp_map] at this
    rw [this, Iso.inv_hom_id_app_assoc]
  have hab : et α = et β := by
    refine Etale.eq_of_leftDerivedUpperStar_oneSection_eq Λ F C hF _ _ (b₅.1 ?_)
    change ν.map (Li.map (et α).hom) = ν.map (Li.map (et β).hom)
    rw [hi, hi]
    simp only [toMor, Functor.map_comp]
    rw [show Lpi.map α.hom = Lpi.map β.hom from h]
  have hm : toMor α = toMor β := by rw [← hν, ← hν, hab]
  ext
  have := congrArg (· ≫ da.inv.app C ≫ Lpa.map eC.inv) hm
  simpa [toMor, ← Functor.map_comp] using this

omit [Finite Λ] in
/-- The exchanges `Lg₁^* Lg₂^* ≅ L(g₁ ≫ g₂)^* = L(g₁' ≫ g₂')^* ≅ Lg₁'^* Lg₂'^*` of pro-étale
pullbacks are natural. -/
@[reassoc]
lemma leftDerivedUpperStarComp_inv_congr_comp_hom_naturality {T S S' R : Scheme.{u}}
    (g₁ : T ⟶ S) (g₂ : S ⟶ R) (g₁' : T ⟶ S') (g₂' : S' ⟶ R) (hg : g₁ ≫ g₂ = g₁' ≫ g₂')
    {M M' : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology R) (ModuleCat.{u + 1} Λ))}
    (f : M ⟶ M') :
    (ProEtale.upperStar (ModuleCat.{u + 1} Λ) g₁).leftDerivedFunctor.map
        ((ProEtale.upperStar (ModuleCat.{u + 1} Λ) g₂).leftDerivedFunctor.map f) ≫
      (leftDerivedUpperStarComp _ g₁ g₂).inv.app M' ≫
        (leftDerivedUpperStarCongr _ hg).hom.app M' ≫
          (leftDerivedUpperStarComp _ g₁' g₂').hom.app M' =
    ((leftDerivedUpperStarComp _ g₁ g₂).inv.app M ≫ (leftDerivedUpperStarCongr _ hg).hom.app M ≫
        (leftDerivedUpperStarComp _ g₁' g₂').hom.app M) ≫
      (ProEtale.upperStar (ModuleCat.{u + 1} Λ) g₁').leftDerivedFunctor.map
        ((ProEtale.upperStar (ModuleCat.{u + 1} Λ) g₂').leftDerivedFunctor.map f) := by
  have n₁ := (leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) g₁ g₂).inv.naturality f
  have n₂ := (leftDerivedUpperStarCongr (ModuleCat.{u + 1} Λ) hg).hom.naturality f
  have n₃ := (leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) g₁' g₂').hom.naturality f
  simp only [Functor.comp_obj, Functor.comp_map] at n₁ n₃
  rw [reassoc_of% n₁, reassoc_of% n₂, n₃, Category.assoc, Category.assoc]

omit [Finite Λ] in
/-- The compatibility of base change with section isomorphisms transports across an
isomorphism to a complex of étale origin. -/
private lemma leftDerivedUpperStar_map_comp_compSectionIso_of_iso {B B' P P' : Scheme.{u}}
    (u : B' ⟶ B) (a : P ⟶ B) (a' : P' ⟶ B') (v : P' ⟶ P) (i : B ⟶ P) (i' : B' ⟶ P')
    (hv : v ≫ a = a' ≫ u) (hi : i' ≫ v = u ≫ i) (h : i ≫ a = 𝟙 B) (h' : i' ≫ a' = 𝟙 B')
    (C : _root_.DerivedCategory (Sheaf B.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    {C' : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology B) (ModuleCat.{u + 1} Λ))}
    (e : C' ≅ (comparisonUpperStar (ModuleCat.{u + 1} Λ) B).mapDerivedCategory.obj C) :
    (ProEtale.upperStar (ModuleCat.{u + 1} Λ) i').leftDerivedFunctor.map
        ((leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) v a).inv.app _ ≫
          (leftDerivedUpperStarCongr (ModuleCat.{u + 1} Λ) hv).hom.app _ ≫
          (leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) a' u).hom.app C') ≫
        (leftDerivedUpperStarCompSectionIso (ModuleCat.{u + 1} Λ) i' a' h').hom.app _ =
      ((leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) i' v).inv.app _ ≫
          (leftDerivedUpperStarCongr (ModuleCat.{u + 1} Λ) hi).hom.app _ ≫
          (leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) u i).hom.app _) ≫
        (ProEtale.upperStar (ModuleCat.{u + 1} Λ) u).leftDerivedFunctor.map
          ((leftDerivedUpperStarCompSectionIso (ModuleCat.{u + 1} Λ) i a h).hom.app C') := by
  let A := ModuleCat.{u + 1} Λ
  let ε := leftDerivedUpperStarCompSectionIso A i a h
  let ε' := leftDerivedUpperStarCompSectionIso A i' a' h'
  have hPC := leftDerivedUpperStar_map_comp_compSectionIso_comparisonUpperStar A
    u a a' v i i' hv hi h h' C
  have n₁ := leftDerivedUpperStarComp_inv_congr_comp_hom_naturality Λ v a a' u hv e.inv
  have n₂ := leftDerivedUpperStarComp_inv_congr_comp_hom_naturality Λ i' v u i hi
    ((ProEtale.upperStar A a).leftDerivedFunctor.map e.inv)
  have nε' := ε'.hom.naturality ((ProEtale.upperStar A u).leftDerivedFunctor.map e.inv)
  have nε := ε.hom.naturality e.inv
  have n₁' := congrArg (ProEtale.upperStar A i').leftDerivedFunctor.map n₁
  rw [← cancel_epi ((ProEtale.upperStar A i').leftDerivedFunctor.map
    ((ProEtale.upperStar A v).leftDerivedFunctor.map
      ((ProEtale.upperStar A a).leftDerivedFunctor.map e.inv)))]
  simp only [Functor.map_comp, Category.assoc] at n₁' n₂ hPC ⊢
  simp only [Functor.comp_obj, Functor.comp_map, Functor.id_map, Functor.id_obj] at nε nε'
  have nε'' : (ProEtale.upperStar A u).leftDerivedFunctor.map
        ((ProEtale.upperStar A i).leftDerivedFunctor.map
          ((ProEtale.upperStar A a).leftDerivedFunctor.map e.inv)) ≫
      (ProEtale.upperStar A u).leftDerivedFunctor.map (ε.hom.app C') =
      (ProEtale.upperStar A u).leftDerivedFunctor.map (ε.hom.app _) ≫
        (ProEtale.upperStar A u).leftDerivedFunctor.map e.inv := by
    rw [← Functor.map_comp, nε, Functor.map_comp]
  rw [reassoc_of% n₁', nε', reassoc_of% hPC, reassoc_of% n₂, nε'']

end ProEtale

namespace Scheme.Hom.DeformationToNormalConeData

open _root_.AlgebraicGeometry.ProEtale

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] {V B : Scheme.{u}} {d : ℕ}
  {g : V ⟶ B} {s : B ⟶ V} {N : NormalConeData d s} (D : DeformationToNormalConeData d g s N)
  [HasInvertibleExponent Λ B] [HasCompactification g] {k : Type u} [Field k]
  (aB : B ⟶ Spec (.of k)) [IsSeparated aB] [LocallyOfFiniteType aB] [QuasiCompact D.proj]
  [QuasiSeparatedSpace B] [QuasiCompact g]

/-- Blueprint `lemma-section-normal-bundle--1` (3), pro-étale: *normalization at `t = 1`.* The
constancy comparison `κ : F ≅ La^* 𝒞(g, s)` restricts at the unit section to the fibre
identification `θ₁ : Li₁^* F ≅ 𝒞(g, s)`, under `Li₁^* La^* ≅ 𝟭`. -/
theorem proEtaleFamilyObjectIso_normalization :
    (ProEtale.upperStar (ModuleCat.{u + 1} Λ)
          (AffineSpace.oneSection (ULift.{u} (Fin 1)) B)).leftDerivedFunctor.mapIso
        (D.proEtaleFamilyObjectIso Λ aB) ≪≫
      (ProEtale.leftDerivedUpperStarCompSectionIso (ModuleCat.{u + 1} Λ) _ _
        (AffineSpace.oneSection_comp_over (ULift.{u} (Fin 1)) B)).app _ =
      D.proEtaleOneFibreIso Λ := by
  let i₁ := AffineSpace.oneSection (ULift.{u} (Fin 1)) B
  let a := 𝔸(ULift.{u} (Fin 1); B) ↘ B
  let ν := (comparisonUpperStar (ModuleCat.{u + 1} Λ) B).mapDerivedCategory
  let εp := ProEtale.leftDerivedUpperStarCompSectionIso (ModuleCat.{u + 1} Λ) i₁ a
    (AffineSpace.oneSection_comp_over (ULift.{u} (Fin 1)) B)
  let εe := Etale.leftDerivedUpperStarCompSectionIso (ModuleCat.{u + 1} Λ) i₁ a
    (AffineSpace.oneSection_comp_over (ULift.{u} (Fin 1)) B)
  let cC := ProEtale.sectionInvariantComparisonIso Λ g s
  let κe := D.familyObjectIso Λ aB (D.oneFibreIso Λ)
  -- the étale normalization
  have he := D.leftDerivedUpperStar_map_familyObjectIso_hom_comp Λ aB (D.oneFibreIso Λ)
  -- `εp` is natural, and `D(ν^*)` carries `εe` to `εp`
  have hn := εp.hom.naturality cC.inv
  have hK := derivedComparisonUpperStarUpperStarIso_inv_app_compSectionIso
    (ModuleCat.{u + 1} Λ) i₁ a (AffineSpace.oneSection_comp_over (ULift.{u} (Fin 1)) B)
    (Etale.sectionInvariant Λ g s)
  have hd := (derivedComparisonUpperStarUpperStarIso (ModuleCat.{u + 1} Λ) i₁).hom.naturality κe.hom
  simp only [Functor.comp_obj, Functor.comp_map, Functor.id_map] at hn hd
  ext
  rw [proEtaleOneFibreIso_eq_comparison]
  simp only [proEtaleFamilyObjectIso, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Iso.app_hom,
    Iso.app_inv, Functor.map_comp, Category.assoc]
  erw [hn, reassoc_of% hK, reassoc_of% hd, ← Functor.map_comp_assoc, he]

omit [IsSeparated aB] [LocallyOfFiniteType aB] [QuasiCompact D.proj] [QuasiSeparatedSpace B]
  [QuasiCompact g] in
include D in
/-- The étale family object and the étale section invariant are bounded constructible: they lie
in `D^b_{ctf}`. -/
theorem boundedConstructible_familyObject_and_sectionInvariant :
    Etale.DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) _ (D.familyObject Λ) ∧
      Etale.DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) B
        (Etale.sectionInvariant Λ g s) := by
  have := D.hasInvertibleExponent_scheme Λ
  have : SmoothOfRelativeDimension d g :=
    have := smoothOfRelativeDimension_isStableUnderBaseChange (n := d)
    MorphismProperty.of_isPullback (P := @SmoothOfRelativeDimension d) D.isPullback_oneFibre
      inferInstance
  have : HasInvertibleExponent Λ V := .of_hom g
  open _root_.AlgebraicGeometry.Etale in
  exact ⟨(isInvertible_and_boundedConstructibleFiniteTor_sectionInvariant Λ (d := d) D.proj
      D.sect).2.1,
    (isInvertible_and_boundedConstructibleFiniteTor_sectionInvariant Λ (d := d) g s).2.1⟩

/-- Blueprint `lemma-section-normal-bundle--1` (3), pro-étale: *uniqueness.* The constancy
comparison is the only isomorphism `F ≅ La^* 𝒞(g, s)` restricting at the unit section to the
fibre identification `θ₁ : Li₁^* F ≅ 𝒞(g, s)`. -/
theorem eq_proEtaleFamilyObjectIso
    (κ : D.proEtaleFamilyObject Λ ≅
      (ProEtale.upperStar (ModuleCat.{u + 1} Λ)
          (𝔸(ULift.{u} (Fin 1); B) ↘ B)).leftDerivedFunctor.obj
        (ProEtale.sectionInvariant Λ g s))
    (hκ : (ProEtale.upperStar (ModuleCat.{u + 1} Λ)
          (AffineSpace.oneSection (ULift.{u} (Fin 1)) B)).leftDerivedFunctor.mapIso κ ≪≫
        (ProEtale.leftDerivedUpperStarCompSectionIso (ModuleCat.{u + 1} Λ) _ _
          (AffineSpace.oneSection_comp_over (ULift.{u} (Fin 1)) B)).app _ =
      D.proEtaleOneFibreIso Λ) :
    κ = D.proEtaleFamilyObjectIso Λ aB := by
  obtain ⟨hF, hC⟩ := D.boundedConstructible_familyObject_and_sectionInvariant Λ
  have hCa := Etale.boundedConstructible_leftDerivedUpperStar (ModuleCat.{u + 1} Λ)
    (𝔸(ULift.{u} (Fin 1); B) ↘ B) hC
  have hC₁ := Etale.boundedConstructible_leftDerivedUpperStar (ModuleCat.{u + 1} Λ)
    (AffineSpace.oneSection (ULift.{u} (Fin 1)) B) hCa
  refine ProEtale.eq_of_leftDerivedUpperStar_oneSection_eq Λ (D.familyObject Λ)
    (Etale.sectionInvariant Λ g s) (D.isInvertible_familyObject Λ) hF.1.1 hCa.1.1 hC₁.1.1
    (ProEtale.sectionInvariantComparisonIso Λ D.proj D.sect)
    (ProEtale.sectionInvariantComparisonIso Λ g s) _ _ ?_
  have h := congrArg Iso.hom (hκ.trans (D.proEtaleFamilyObjectIso_normalization Λ aB).symm)
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom] at h
  exact (cancel_mono _).1 h

/-- Blueprint `lemma-section-normal-bundle--1` (4), pro-étale: *base change.* Let `u : B' ⟶ B`,
with base change `v₁ : 𝔸¹_{B'} ⟶ 𝔸¹_B`. The restriction of the constancy comparison,
`Lv₁^* κ : Lv₁^* F ≅ Lv₁^* La^* 𝒞(g, s) ≅ La'^* Lu^* 𝒞(g, s)`, restricts at `t = 1` to the
restriction `Lu^* θ₁` of the fibre identification, and it is the only comparison
`Lv₁^* F ≅ La'^* Lu^* 𝒞(g, s)` doing so. -/
theorem proEtaleFamilyObjectIso_baseChange {B' : Scheme.{u}} (u : B' ⟶ B)
    (κ' : (ProEtale.upperStar (ModuleCat.{u + 1} Λ)
          (AffineSpace.map (ULift.{u} (Fin 1)) u)).leftDerivedFunctor.obj
        (D.proEtaleFamilyObject Λ) ≅
      (ProEtale.upperStar (ModuleCat.{u + 1} Λ)
          (𝔸(ULift.{u} (Fin 1); B') ↘ B')).leftDerivedFunctor.obj
        ((ProEtale.upperStar (ModuleCat.{u + 1} Λ) u).leftDerivedFunctor.obj
          (ProEtale.sectionInvariant Λ g s))) :
    (ProEtale.upperStar (ModuleCat.{u + 1} Λ)
          (AffineSpace.oneSection (ULift.{u} (Fin 1)) B')).leftDerivedFunctor.map κ'.hom ≫
        (ProEtale.leftDerivedUpperStarCompSectionIso (ModuleCat.{u + 1} Λ) _ _
          (AffineSpace.oneSection_comp_over (ULift.{u} (Fin 1)) B')).hom.app _ =
      ((leftDerivedUpperStarComp _ (AffineSpace.oneSection (ULift.{u} (Fin 1)) B')
            (AffineSpace.map (ULift.{u} (Fin 1)) u)).inv.app _ ≫
          (leftDerivedUpperStarCongr _ (AffineSpace.oneSection_comp_map u)).hom.app _ ≫
          (leftDerivedUpperStarComp _ u (AffineSpace.oneSection (ULift.{u} (Fin 1)) B)).hom.app _) ≫
        (ProEtale.upperStar (ModuleCat.{u + 1} Λ) u).leftDerivedFunctor.map
          (D.proEtaleOneFibreIso Λ).hom ↔
    κ'.hom = (ProEtale.upperStar (ModuleCat.{u + 1} Λ)
          (AffineSpace.map (ULift.{u} (Fin 1)) u)).leftDerivedFunctor.map
          (D.proEtaleFamilyObjectIso Λ aB).hom ≫
        (leftDerivedUpperStarComp _ (AffineSpace.map (ULift.{u} (Fin 1)) u)
          (𝔸(ULift.{u} (Fin 1); B) ↘ B)).inv.app _ ≫
        (leftDerivedUpperStarCongr _ (AffineSpace.map_over (n := ULift.{u} (Fin 1)) u)).hom.app _ ≫
        (leftDerivedUpperStarComp _ (𝔸(ULift.{u} (Fin 1); B') ↘ B') u).hom.app _ := by
  let A := ModuleCat.{u + 1} Λ
  let i₁ := AffineSpace.oneSection (ULift.{u} (Fin 1)) B
  let i₁' := AffineSpace.oneSection (ULift.{u} (Fin 1)) B'
  let a := 𝔸(ULift.{u} (Fin 1); B) ↘ B
  let a' := 𝔸(ULift.{u} (Fin 1); B') ↘ B'
  let v₁ := AffineSpace.map (ULift.{u} (Fin 1)) u
  let ε := ProEtale.leftDerivedUpperStarCompSectionIso A i₁ a
    (AffineSpace.oneSection_comp_over (ULift.{u} (Fin 1)) B)
  let ε' := ProEtale.leftDerivedUpperStarCompSectionIso A i₁' a'
    (AffineSpace.oneSection_comp_over (ULift.{u} (Fin 1)) B')
  let κ := D.proEtaleFamilyObjectIso Λ aB
  let cC := ProEtale.sectionInvariantComparisonIso Λ g s
  -- the two exchanges at the section invariant agree with the section isomorphisms
  have PQ : (ProEtale.upperStar A i₁').leftDerivedFunctor.map
        ((leftDerivedUpperStarComp A v₁ a).inv.app _ ≫
          (leftDerivedUpperStarCongr A (AffineSpace.map_over u)).hom.app _ ≫
          (leftDerivedUpperStarComp A a' u).hom.app (ProEtale.sectionInvariant Λ g s)) ≫
        ε'.hom.app _ =
      ((leftDerivedUpperStarComp A i₁' v₁).inv.app _ ≫
          (leftDerivedUpperStarCongr A (AffineSpace.oneSection_comp_map u)).hom.app _ ≫
          (leftDerivedUpperStarComp A u i₁).hom.app _) ≫
        (ProEtale.upperStar A u).leftDerivedFunctor.map
          (ε.hom.app (ProEtale.sectionInvariant Λ g s)) := by
    exact leftDerivedUpperStar_map_comp_compSectionIso_of_iso Λ u a a' v₁ i₁ i₁'
      (AffineSpace.map_over u) (AffineSpace.oneSection_comp_map u)
      (AffineSpace.oneSection_comp_over _ B) (AffineSpace.oneSection_comp_over _ B')
      (Etale.sectionInvariant Λ g s) cC
  -- the restriction of `κ` restricts at `t = 1` to `Lu^* θ₁`
  have ha : (ProEtale.upperStar A i₁').leftDerivedFunctor.map
        ((ProEtale.upperStar A v₁).leftDerivedFunctor.map κ.hom ≫
          (leftDerivedUpperStarComp A v₁ a).inv.app _ ≫
          (leftDerivedUpperStarCongr A (AffineSpace.map_over u)).hom.app _ ≫
          (leftDerivedUpperStarComp A a' u).hom.app _) ≫ ε'.hom.app _ =
      ((leftDerivedUpperStarComp A i₁' v₁).inv.app _ ≫
          (leftDerivedUpperStarCongr A (AffineSpace.oneSection_comp_map u)).hom.app _ ≫
          (leftDerivedUpperStarComp A u i₁).hom.app _) ≫
        (ProEtale.upperStar A u).leftDerivedFunctor.map (D.proEtaleOneFibreIso Λ).hom := by
    have hθ := congrArg Iso.hom (D.proEtaleFamilyObjectIso_normalization Λ aB)
    simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom] at hθ
    rw [← hθ]
    have n := leftDerivedUpperStarComp_inv_congr_comp_hom_naturality Λ i₁' v₁ u i₁
      (AffineSpace.oneSection_comp_map u) κ.hom
    simp only [Functor.map_comp, Category.assoc] at PQ n ⊢
    rw [PQ, ← reassoc_of% n]
  constructor
  · intro h
    have : HasInvertibleExponent Λ B' := .of_hom u
    have : HasInvertibleExponent Λ 𝔸(ULift.{u} (Fin 1); B) := .of_hom a
    have : HasInvertibleExponent Λ 𝔸(ULift.{u} (Fin 1); B') := .of_hom a'
    obtain ⟨hF, hC⟩ := D.boundedConstructible_familyObject_and_sectionInvariant Λ
    have hF' := Etale.boundedConstructible_leftDerivedUpperStar A v₁ hF
    have hC' := Etale.boundedConstructible_leftDerivedUpperStar A u hC
    have hCa := Etale.boundedConstructible_leftDerivedUpperStar A a' hC'
    have hC₁ := Etale.boundedConstructible_leftDerivedUpperStar A i₁' hCa
    let X := (ProEtale.upperStar A v₁).leftDerivedFunctor.mapIso κ ≪≫
      ((leftDerivedUpperStarComp A v₁ a).app _).symm ≪≫
      (leftDerivedUpperStarCongr A (AffineSpace.map_over u)).app _ ≪≫
      (leftDerivedUpperStarComp A a' u).app _
    refine congrArg Iso.hom (ProEtale.eq_of_leftDerivedUpperStar_oneSection_eq Λ
      ((Etale.upperStar A v₁).leftDerivedFunctor.obj (D.familyObject Λ))
      ((Etale.upperStar A u).leftDerivedFunctor.obj (Etale.sectionInvariant Λ g s))
      (Etale.DerivedCategory.isInvertible.leftDerivedUpperStar v₁ (D.isInvertible_familyObject Λ))
      hF'.1.1 hCa.1.1 hC₁.1.1
      ((ProEtale.upperStar A v₁).leftDerivedFunctor.mapIso
          (ProEtale.sectionInvariantComparisonIso Λ D.proj D.sect) ≪≫
        (derivedComparisonUpperStarUpperStarIso A v₁).app _)
      ((ProEtale.upperStar A u).leftDerivedFunctor.mapIso cC ≪≫
        (derivedComparisonUpperStarUpperStarIso A u).app _) κ' X ?_)
    rw [← cancel_mono (ε'.hom.app _), h, ← ha]
    rfl
  · intro h
    rw [h]
    exact ha

end Scheme.Hom.DeformationToNormalConeData

end AlgebraicGeometry
