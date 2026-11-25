/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.BaseChange.Derived
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.KInjective

/-!
# The derived base change map on K-injective resolutions

Consider a cartesian square of schemes
```
  X' --g'--> X
  |          |
  f'         f
  ↓          ↓
  Y' --g---> Y
```
an object `K ∈ D⁺(X_ét)` represented by a K-injective complex `I` (via `s : K ≅ Qh I`), and a
K-injective resolution `j : g'^* I ⟶ J` of the pullback. Then the derived base change map
`g^* Rf_* K ⟶ Rf'_* g'^* K` is computed termwise: up to the canonical identifications
`Rf_* K ≅ f_* I` and `Rf'_* (g'^* K) ≅ f'_* J`, it is the composite
`g^* f_* I ⟶ f'_* g'^* I ⟶ f'_* J` of the underived base change map applied in each degree
with `f'_* j`.

The identifications `Rf_* K ≅ f_* I` and `Rf'_* (g'^* K) ≅ f'_* J` come from the comparison
maps `I ⟶ P` and `J ⟶ P'` to the bounded below injective complexes `P`, `P'` chosen by
`DerivedCategory.Plus.injectiveObjectEquivalence` to compute `Rf_*` and `Rf'_*`; these
comparison maps are unique in the homotopy category and are homotopy equivalences.

## Main statements

- `AlgebraicGeometry.Etale.existsUnique_derivedBaseChangeMapPlus_comparison`: the comparison
  maps `I ⟶ P` and `J ⟶ P'` exist and are unique.
- `AlgebraicGeometry.Etale.derivedBaseChangeMapPlus_eq_termwise`: the comparison maps are
  isomorphisms, and the derived base change map on `K` agrees with the termwise one.

(blueprint: `prose-04-06`)
-/

@[expose] public section

universe u' u

open CategoryTheory Category Limits Opposite

namespace AlgebraicGeometry

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]

open Etale

variable {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}

/-- **Uniqueness of the comparison maps.** Let `K ∈ D⁺(X_ét)` be represented by a K-injective
complex `I` via `s : K ≅ Qh I`, and let `j : g'^* I ⟶ J` be a K-injective resolution. Let `P`,
`P'` be the bounded below injective complexes representing `K` and `g'^* K` under
`DerivedCategory.Plus.injectiveObjectEquivalence`, with the isomorphisms `ρ : K ≅ Qh P` and
`ρ' : g'^* K ≅ Qh P'`. Then there are unique maps `h₁ : I ⟶ P` and `h₂ : J ⟶ P'` in the
homotopy category compatible with `s`, `ρ` and with `t : g'^* K ≅ Qh J` (induced by `s` and
`j`), `ρ'` respectively. (blueprint: `prose-04-06`) -/
lemma Etale.existsUnique_derivedBaseChangeMapPlus_comparison
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology A))
    (I : CochainComplex (Sheaf X.smallEtaleTopology A) ℤ) [I.IsKInjective]
    (s : DerivedCategory.Plus.ι.obj K ≅
      DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj I))
    (J : CochainComplex (Sheaf X'.smallEtaleTopology A) ℤ) [J.IsKInjective]
    (j : (((g')^*[A]).mapHomologicalComplex (.up ℤ)).obj I ⟶ J) [QuasiIso j] :
    let C := Sheaf X.smallEtaleTopology A
    let C' := Sheaf X'.smallEtaleTopology A
    let q := HomotopyCategory.quotient C (.up ℤ)
    let q' := HomotopyCategory.quotient C' (.up ℤ)
    let G' := (g')^*[A]
    let E := DerivedCategory.Plus.injectiveObjectEquivalence C
    let E' := DerivedCategory.Plus.injectiveObjectEquivalence C'
    let K' := G'.mapDerivedCategoryPlus.obj K
    let P := (InjectiveObject.ι C).mapHomotopyCategoryPlus.obj (E.inverse.obj K)
    let P' := (InjectiveObject.ι C').mapHomotopyCategoryPlus.obj (E'.inverse.obj K')
    let ρ := DerivedCategory.Plus.ι.map (E.counitIso.inv.app K)
    let ρ' := DerivedCategory.Plus.ι.map (E'.counitIso.inv.app K')
    let t := G'.mapDerivedCategory.map s.hom ≫
      G'.mapDerivedCategoryFactorsh.hom.app (q.obj I) ≫
      DerivedCategory.Qh.map (q'.map j)
    ∃! h : (q.obj I ⟶ P.obj) × (q'.obj J ⟶ P'.obj),
      s.hom ≫ DerivedCategory.Qh.map h.1 = ρ ∧ t ≫ DerivedCategory.Qh.map h.2 = ρ' := by
  intro C C' q q' G' E E' K' P P' ρ ρ' t
  have : IsIso (DerivedCategory.Qh.map (q'.map j)) := by
    rw [DerivedCategory.isIso_Qh_map_iff, HomotopyCategory.quotient_map_mem_quasiIso_iff,
      HomologicalComplex.mem_quasiIso_iff]
    infer_instance
  have : IsIso t := IsIso.comp_isIso' inferInstance (IsIso.comp_isIso' inferInstance this)
  have hP := CochainComplex.IsKInjective.Qh_map_bijective (q.obj I) P.obj.as
  have hP' := CochainComplex.IsKInjective.Qh_map_bijective (q'.obj J) P'.obj.as
  obtain ⟨h₁, hh₁⟩ := hP.2 (s.inv ≫ ρ)
  obtain ⟨h₂, hh₂⟩ := hP'.2 (inv t ≫ ρ')
  refine ⟨(h₁, h₂), ⟨?_, ?_⟩, fun h ⟨hh₁', hh₂'⟩ ↦ Prod.ext (hP.1 ?_) (hP'.1 ?_)⟩
  · exact (congrArg (s.hom ≫ ·) hh₁).trans (Iso.hom_inv_id_assoc s ρ)
  · exact (congrArg (t ≫ ·) hh₂).trans (IsIso.hom_inv_id_assoc t ρ')
  · exact ((Iso.inv_hom_id_assoc s _).symm.trans (congrArg (s.inv ≫ ·) hh₁')).trans hh₁.symm
  · exact ((IsIso.inv_hom_id_assoc t _).symm.trans (congrArg (inv t ≫ ·) hh₂')).trans hh₂.symm

set_option backward.isDefEq.respectTransparency false in
/-- **The derived base change map on K-injective resolutions.** In the situation of
`AlgebraicGeometry.Etale.existsUnique_derivedBaseChangeMapPlus_comparison`, the comparison maps
`h₁ : I ⟶ P` and `h₂ : J ⟶ P'` are isomorphisms in the homotopy category, and so are the induced
identifications `χ : f_* I ≅ Rf_* K`, `χ' : f'_* J ≅ Rf'_* (g'^* K)` and
`σ : g^* f_* I ≅ g^* Rf_* K`. Under them the derived base change map on `K` is the termwise map
`e : g^* f_* I ⟶ f'_* g'^* I ⟶ f'_* J`, i.e. the square
```
  g^* f_* I ---------e---------> f'_* J
      |                            |
      σ                            χ'
      ↓                            ↓
  g^* Rf_* K --(base change)--> Rf'_* g'^* K
```
commutes. (blueprint: `prose-04-06`) -/
lemma Etale.derivedBaseChangeMapPlus_eq_termwise (sq : CommSq g' f' f g)
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology A))
    (I : CochainComplex (Sheaf X.smallEtaleTopology A) ℤ) [I.IsKInjective]
    (s : DerivedCategory.Plus.ι.obj K ≅
      DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj I))
    (J : CochainComplex (Sheaf X'.smallEtaleTopology A) ℤ) [J.IsKInjective]
    (j : (((g')^*[A]).mapHomologicalComplex (.up ℤ)).obj I ⟶ J) [QuasiIso j] :
    let C := Sheaf X.smallEtaleTopology A
    let C' := Sheaf X'.smallEtaleTopology A
    let q := HomotopyCategory.quotient C (.up ℤ)
    let q' := HomotopyCategory.quotient C' (.up ℤ)
    let qY := HomotopyCategory.quotient (Sheaf Y'.smallEtaleTopology A) (.up ℤ)
    let F := (f)_*[A]
    let F' := (f')_*[A]
    let G := (g)^*[A]
    let G' := (g')^*[A]
    let E := DerivedCategory.Plus.injectiveObjectEquivalence C
    let E' := DerivedCategory.Plus.injectiveObjectEquivalence C'
    let K' := G'.mapDerivedCategoryPlus.obj K
    let P := (InjectiveObject.ι C).mapHomotopyCategoryPlus.obj (E.inverse.obj K)
    let P' := (InjectiveObject.ι C').mapHomotopyCategoryPlus.obj (E'.inverse.obj K')
    let ρ := DerivedCategory.Plus.ι.map (E.counitIso.inv.app K)
    let ρ' := DerivedCategory.Plus.ι.map (E'.counitIso.inv.app K')
    let t := G'.mapDerivedCategory.map s.hom ≫
      G'.mapDerivedCategoryFactorsh.hom.app (q.obj I) ≫
      DerivedCategory.Qh.map (q'.map j)
    let e := (NatTrans.mapHomologicalComplex (Etale.baseChangeMap A sq) (.up ℤ)).app I ≫
      (F'.mapHomologicalComplex (.up ℤ)).map j
    ∀ h : (q.obj I ⟶ P.obj) × (q'.obj J ⟶ P'.obj),
      s.hom ≫ DerivedCategory.Qh.map h.1 = ρ →
      t ≫ DerivedCategory.Qh.map h.2 = ρ' →
      let χ := DerivedCategory.Qh.map ((F.mapHomotopyCategory (.up ℤ)).map h.1) ≫
        DerivedCategory.Plus.ι.map (F.rightDerivedFunctorPlusUnith.app P ≫
          F.rightDerivedFunctorPlus.map (E.counitIso.hom.app K))
      let χ' := DerivedCategory.Qh.map ((F'.mapHomotopyCategory (.up ℤ)).map h.2) ≫
        DerivedCategory.Plus.ι.map (F'.rightDerivedFunctorPlusUnith.app P' ≫
          F'.rightDerivedFunctorPlus.map (E'.counitIso.hom.app K'))
      let σ := G.mapDerivedCategoryFactorsh.inv.app
        ((F.mapHomotopyCategory (.up ℤ)).obj (q.obj I)) ≫ G.mapDerivedCategory.map χ
      IsIso h.1 ∧ IsIso h.2 ∧ IsIso χ ∧ IsIso χ' ∧ IsIso σ ∧
      σ ≫ DerivedCategory.Plus.ι.map ((Etale.derivedBaseChangeMapPlus A sq).app K) =
        DerivedCategory.Qh.map (qY.map e) ≫ χ' := by
  intro C C' q q' qY F F' G G' E E' K' P P' ρ ρ' t e h hh₁ hh₂ χ χ' σ
  have hj : IsIso (DerivedCategory.Qh.map (q'.map j)) := by
    rw [DerivedCategory.isIso_Qh_map_iff, HomotopyCategory.quotient_map_mem_quasiIso_iff,
      HomologicalComplex.mem_quasiIso_iff]
    infer_instance
  have it : IsIso t := IsIso.comp_isIso' inferInstance (IsIso.comp_isIso' inferInstance hj)
  have iρ : IsIso ρ :=
    inferInstanceAs (IsIso (DerivedCategory.Plus.ι.map (E.counitIso.inv.app K)))
  have iρ' : IsIso ρ' :=
    inferInstanceAs (IsIso (DerivedCategory.Plus.ι.map (E'.counitIso.inv.app K')))
  have hh₁' : DerivedCategory.Qh.map h.1 = s.inv ≫ ρ := (Iso.eq_inv_comp s).2 hh₁
  have hh₂' : DerivedCategory.Qh.map h.2 = inv t ≫ ρ' := (IsIso.eq_inv_comp t).2 hh₂
  have q₁ : IsIso (DerivedCategory.Qh.map h.1) := by
    rw [hh₁']; exact IsIso.comp_isIso' inferInstance iρ
  have q₂ : IsIso (DerivedCategory.Qh.map h.2) := by
    rw [hh₂']; exact IsIso.comp_isIso' inferInstance iρ'
  have i₁ : IsIso h.1 :=
    @CochainComplex.IsKInjective.isIso_of_isIso_Qh_map _ _ _ _ I P.obj.as _ _ h.1 q₁
  have i₂ : IsIso h.2 :=
    @CochainComplex.IsKInjective.isIso_of_isIso_Qh_map _ _ _ _ J P'.obj.as _ _ h.2 q₂
  have iu : IsIso (F.rightDerivedFunctorPlusUnith.app P) :=
    inferInstanceAs (IsIso (F.rightDerivedFunctorPlusUnith.app
      ((InjectiveObject.ι C).mapHomotopyCategoryPlus.obj (E.inverse.obj K))))
  have iu' : IsIso (F'.rightDerivedFunctorPlusUnith.app P') :=
    inferInstanceAs (IsIso (F'.rightDerivedFunctorPlusUnith.app
      ((InjectiveObject.ι C').mapHomotopyCategoryPlus.obj (E'.inverse.obj K'))))
  have iχ : IsIso χ := IsIso.comp_isIso' inferInstance (DerivedCategory.Plus.ι.mapIso
    (@asIso _ _ _ _ (F.rightDerivedFunctorPlusUnith.app P ≫
      F.rightDerivedFunctorPlus.map (E.counitIso.hom.app K))
      (IsIso.comp_isIso' iu
        (F.rightDerivedFunctorPlus.mapIso (E.counitIso.app K)).isIso_hom))).isIso_hom
  have iχ' : IsIso χ' := IsIso.comp_isIso' inferInstance (DerivedCategory.Plus.ι.mapIso
    (@asIso _ _ _ _ (F'.rightDerivedFunctorPlusUnith.app P' ≫
      F'.rightDerivedFunctorPlus.map (E'.counitIso.hom.app K'))
      (IsIso.comp_isIso' iu'
        (F'.rightDerivedFunctorPlus.mapIso (E'.counitIso.app K')).isIso_hom))).isIso_hom
  have iσ : IsIso σ := IsIso.comp_isIso' inferInstance (Functor.map_isIso _ χ)
  refine ⟨i₁, i₂, iχ, iχ', iσ, ?_⟩
  let ι := DerivedCategory.Plus.ι (C := C)
  let ι' := DerivedCategory.Plus.ι (C := C')
  let cK : DerivedCategory.Plus.Qh.obj P ⟶ K := E.counitIso.hom.app K
  let cK' : DerivedCategory.Plus.Qh.obj P' ⟶ K' := E'.counitIso.hom.app K'
  have hρ' : ρ' ≫ ι'.map cK' = 𝟙 _ := by
    rw [← Functor.map_comp, Iso.inv_hom_id_app, CategoryTheory.Functor.map_id]
  have hfac : ι'.map (G'.mapDerivedCategoryPlusFactorsh.inv.app P) =
      G'.mapDerivedCategoryFactorsh.inv.app P.obj :=
    (Iso.inv_eq_inv (ι'.mapIso (G'.mapDerivedCategoryPlusFactorsh.app P))
      (G'.mapDerivedCategoryFactorsh.app P.obj)).2
      (Functor.ι_map_mapDerivedCategoryPlusFactorsh_hom_app G' P)
  let ρ₀ : ι.obj K ⟶ DerivedCategory.Qh.obj (q.obj P.obj.as) := ρ
  have hρ₀' : ι.map cK ≫ ρ₀ = 𝟙 _ := (ι.mapIso (E.counitIso.app K)).hom_inv_id
  obtain ⟨φ₁, hφ₁⟩ := q.map_surjective (X := I) (Y := P.obj.as) h.1
  obtain ⟨ψ₁, hψ₁⟩ := q.map_surjective (X := P.obj.as) (Y := I) (@inv _ _ _ _ h.1 i₁)
  obtain ⟨φ₂, hφ₂⟩ := q'.map_surjective (X := J) (Y := P'.obj.as) h.2
  have hφ₁' : DerivedCategory.Qh.map (q.map φ₁) = s.inv ≫ ρ₀ := hφ₁ ▸ hh₁'
  have hφψ : q.map φ₁ ≫ q.map ψ₁ = 𝟙 _ := by
    rw [hφ₁, hψ₁]
    exact @IsIso.hom_inv_id _ _ _ _ h.1 i₁
  have hψ₁' : DerivedCategory.Qh.map (q.map ψ₁) = ι.map cK ≫ s.hom := by
    calc DerivedCategory.Qh.map (q.map ψ₁)
        = (ι.map cK ≫ s.hom) ≫ (DerivedCategory.Qh.map (q.map φ₁) ≫
            DerivedCategory.Qh.map (q.map ψ₁)) := by
          simp only [hφ₁', assoc, Iso.hom_inv_id_assoc, reassoc_of% hρ₀']
      _ = ι.map cK ≫ s.hom := by
          rw [← Functor.map_comp, hφψ, CategoryTheory.Functor.map_id, comp_id]
  let k : G'.mapHomotopyCategoryPlus.obj P ⟶ P' := ObjectProperty.homMk
    (q'.map ((G'.mapHomologicalComplex _).map ψ₁ ≫ j ≫ φ₂))
  have H₄ : G'.mapDerivedCategoryPlusFactorsh.inv.app P ≫ G'.mapDerivedCategoryPlus.map cK =
      DerivedCategory.Plus.Qh.map k ≫ cK' := by
    apply ι'.map_injective
    rw [Functor.map_comp, Functor.map_comp, hfac]
    change _ ≫ G'.mapDerivedCategory.map (ι.map cK) =
      DerivedCategory.Qh.map k.hom ≫ ι'.map cK'
    have hφ₂' : DerivedCategory.Qh.map (q'.map φ₂) = inv t ≫ ρ' := hφ₂ ▸ hh₂'
    have e₃ := G'.mapDerivedCategoryFactorsh.inv.naturality (q.map ψ₁)
    simp only [Functor.comp_map, hψ₁'] at e₃
    simp only [k, ObjectProperty.homMk_hom, Functor.map_comp, assoc, hφ₂', hρ', t,
      IsIso.inv_comp, IsIso.hom_inv_id_assoc]
    rw [Functor.mapHomotopyCategory_map] at e₃
    erw [Category.comp_id]
    rw [IsIso.inv_eq_of_hom_inv_id (Iso.hom_inv_id_app _ (q.obj I)), ← Functor.map_inv,
      IsIso.Iso.inv_hom, reassoc_of% e₃,
      ← Functor.map_comp, assoc, Iso.hom_inv_id, comp_id]
    rfl
  have H₂ : F'.rightDerivedFunctorPlusUnith.app (G'.mapHomotopyCategoryPlus.obj P) ≫
      F'.rightDerivedFunctorPlus.map
        (G'.mapDerivedCategoryPlusFactorsh.inv.app P ≫ G'.mapDerivedCategoryPlus.map cK) =
      DerivedCategory.Plus.Qh.map (F'.mapHomotopyCategoryPlus.map k) ≫
        F'.rightDerivedFunctorPlusUnith.app P' ≫ F'.rightDerivedFunctorPlus.map cK' := by
    have := F'.rightDerivedFunctorPlusUnith.naturality k
    simp only [Functor.comp_map] at this
    rw [H₄, Functor.map_comp, reassoc_of% this]
  have H₁ : G.mapDerivedCategoryPlus.map (F.rightDerivedFunctorPlusUnith.app P ≫
      F.rightDerivedFunctorPlus.map cK) ≫ (Etale.derivedBaseChangeMapPlus A sq).app K =
      G.mapDerivedCategoryPlusFactorsh.hom.app (F.mapHomotopyCategoryPlus.obj P) ≫
        DerivedCategory.Plus.Qh.map
          ((NatTrans.mapHomotopyCategoryPlus (Etale.baseChangeMap A sq)).app P) ≫
        F'.rightDerivedFunctorPlusUnith.app (G'.mapHomotopyCategoryPlus.obj P) ≫
        F'.rightDerivedFunctorPlus.map
          (G'.mapDerivedCategoryPlusFactorsh.inv.app P ≫ G'.mapDerivedCategoryPlus.map cK) := by
    have := (Etale.derivedBaseChangeMapPlus A sq).naturality cK
    simp only [Functor.comp_map] at this
    rw [Functor.map_comp, assoc, this, Etale.derivedBaseChangeMapPlus_fac_app_assoc,
      Functor.map_comp]
  let ιY := DerivedCategory.Plus.ι (C := Sheaf Y'.smallEtaleTopology A)
  have H₅ :
      G.mapDerivedCategory.map
          (DerivedCategory.Plus.ι.map (F.rightDerivedFunctorPlusUnith.app P)) ≫
      G.mapDerivedCategory.map (DerivedCategory.Plus.ι.map (F.rightDerivedFunctorPlus.map cK)) ≫
        ιY.map ((Etale.derivedBaseChangeMapPlus A sq).app K) =
      G.mapDerivedCategoryFactorsh.hom.app ((F.mapHomotopyCategory _).obj P.obj) ≫
        DerivedCategory.Qh.map (qY.map
          ((NatTrans.mapHomologicalComplex (Etale.baseChangeMap A sq) _).app P.obj.as)) ≫
        DerivedCategory.Qh.map (qY.map ((F'.mapHomologicalComplex _).map
          ((G'.mapHomologicalComplex _).map ψ₁ ≫ j ≫ φ₂))) ≫
        ιY.map (F'.rightDerivedFunctorPlusUnith.app P') ≫
        ιY.map (F'.rightDerivedFunctorPlus.map cK') := by
    have a₁ : ιY.map (G.mapDerivedCategoryPlusFactorsh.hom.app (F.mapHomotopyCategoryPlus.obj P)) =
        G.mapDerivedCategoryFactorsh.hom.app ((F.mapHomotopyCategory _).obj P.obj) :=
      Functor.ι_map_mapDerivedCategoryPlusFactorsh_hom_app G _
    have a₂ : ιY.map (DerivedCategory.Plus.Qh.map
        ((NatTrans.mapHomotopyCategoryPlus (Etale.baseChangeMap A sq)).app P)) =
        DerivedCategory.Qh.map (qY.map
          ((NatTrans.mapHomologicalComplex (Etale.baseChangeMap A sq) _).app P.obj.as)) :=
      (congrArg DerivedCategory.Qh.map (NatTrans.ι_map_mapHomotopyCategoryPlus_app
        (Etale.baseChangeMap A sq) P) :)
    have a₃ : ιY.map (DerivedCategory.Plus.Qh.map (F'.mapHomotopyCategoryPlus.map k)) =
        DerivedCategory.Qh.map (qY.map ((F'.mapHomologicalComplex _).map
          ((G'.mapHomologicalComplex _).map ψ₁ ≫ j ≫ φ₂))) := rfl
    have := congrArg ιY.map H₁
    rw [H₂] at this
    simp only [Functor.map_comp, assoc] at this
    rw [a₁, a₂, a₃] at this
    exact this
  simp only [σ, χ, χ', Functor.map_comp, assoc]
  erw [H₅]
  have e₆ := G.mapDerivedCategoryFactorsh.hom.naturality ((F.mapHomotopyCategory _).map h.1)
  simp only [Functor.comp_map] at e₆
  rw [reassoc_of% e₆, Iso.inv_hom_id_app_assoc]
  have hid : qY.map ((F'.mapHomologicalComplex _).map ((G'.mapHomologicalComplex _).map φ₁)) ≫
      qY.map ((F'.mapHomologicalComplex _).map ((G'.mapHomologicalComplex _).map ψ₁)) = 𝟙 _ := by
    have : (F'.mapHomotopyCategory _).map ((G'.mapHomotopyCategory _).map (q.map φ₁ ≫ q.map ψ₁)) =
        𝟙 _ := by
      rw [hφψ, CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
    simp only [Functor.map_comp] at this
    exact this
  have key : (G.mapHomotopyCategory _).map ((F.mapHomotopyCategory _).map h.1) ≫
      qY.map ((NatTrans.mapHomologicalComplex (Etale.baseChangeMap A sq) _).app P.obj.as) ≫
      qY.map ((F'.mapHomologicalComplex _).map ((G'.mapHomologicalComplex _).map ψ₁ ≫ j ≫ φ₂)) =
      qY.map e ≫ (F'.mapHomotopyCategory _).map h.2 := by
    have nat := (NatTrans.mapHomologicalComplex (Etale.baseChangeMap A sq) (.up ℤ)).naturality φ₁
    rw [← hφ₁, ← hφ₂, Functor.mapHomotopyCategory_map, Functor.mapHomotopyCategory_map,
      Functor.mapHomotopyCategory_map, ← Functor.map_comp, ← Functor.map_comp,
      ← Functor.map_comp, ← assoc]
    erw [nat]
    simp only [e, Functor.map_comp, assoc]
    erw [reassoc_of% hid]
  rw [← Functor.map_comp_assoc, ← Functor.map_comp_assoc, assoc, key]
  simp only [Functor.map_comp, assoc]
  rfl

end AlgebraicGeometry
