/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Adjunction.Mates

/-!

# Abstract diagram chases for re-basing trait models

The diagram chases behind
`NearbyCyclesModel.NearbyDualizingDataOfGenericBase.θ_eq_rebase_of_isProper`, carried out in
abstract categories so that elaboration never unfolds the derived functors to which they are
applied.

* `CategoryTheory.rebase_pullbackExchange_aux`: two factorizations of a pullback exchange of a
  composite morphism of models give a relation between the pullback exchanges of the factors.
* `CategoryTheory.rebase_pushforwardExchange_aux`: the corresponding relation between the mates
  (the pushforward exchanges), involving the mate of a pullback comparison (a base change
  morphism), and its variant `CategoryTheory.rebase_pushforwardExchange_aux_of_eq` at an object
  equal to the pullback.
* `CategoryTheory.rebase_trace_aux`: the trace computation deducing the trace property of the
  re-based dualizing map.

-/

@[expose] public section

open CategoryTheory

namespace CategoryTheory

/-- Two factorizations `αc ∘ c₁ = I'(αa) ≫ αr` and `αc ∘ c₂ = sU(ατ) ≫ αe` of a pullback
exchange `αc` (up to composition isomorphisms `c₁, c₂, c₁', c₂'`, with `I' ≅ 𝟭`, `Ik ≅ 𝟭`
compatible with them) relate the exchanges of the factors:
`αa ≫ e'⁻¹ ≫ αr = sU(ek⁻¹ ≫ ατ) ≫ αe ≫ ΨM'(c₂⁻¹ ≫ c₁)`. -/
lemma rebase_pullbackExchange_aux {DF DX Dη DXη Dk Ds : Type*} [Category DF] [Category DX]
    [Category Dη] [Category DXη] [Category Dk] [Category Ds]
    {aU : DF ⥤ DX} {eU : Dη ⥤ DXη} {sU : Dk ⥤ Ds} {ιU : DF ⥤ Dη} {πU : DX ⥤ DXη}
    {cU : DF ⥤ DXη} {cS : Dk ⥤ Ds} {I' : Ds ⥤ Ds} {Ik : Dk ⥤ Dk}
    {ΨF : DF ⥤ Dk} {Ψη : Dη ⥤ Dk} {ΨM : DX ⥤ Ds} {ΨM' : DXη ⥤ Ds}
    (c₁ : cU ≅ aU ⋙ πU) (c₂ : cU ≅ ιU ⋙ eU) (c₁' : cS ≅ sU ⋙ I') (c₂' : cS ≅ Ik ⋙ sU)
    (e' : I' ≅ 𝟭 Ds) (ek : Ik ≅ 𝟭 Dk)
    (hunit : ∀ Y, c₁'.hom.app Y ≫ e'.hom.app (sU.obj Y) =
      c₂'.hom.app Y ≫ sU.map (ek.hom.app Y))
    (αc : ΨF ⋙ cS ⟶ cU ⋙ ΨM') (αa : ΨF ⋙ sU ⟶ aU ⋙ ΨM) (αr : ΨM ⋙ I' ⟶ πU ⋙ ΨM')
    (ατ : ΨF ⋙ Ik ⟶ ιU ⋙ Ψη) (αe : Ψη ⋙ sU ⟶ eU ⋙ ΨM')
    (h₁ : ∀ C, αc.app C ≫ ΨM'.map (c₁.hom.app C) =
      c₁'.hom.app (ΨF.obj C) ≫ I'.map (αa.app C) ≫ αr.app (aU.obj C))
    (h₂ : ∀ C, αc.app C ≫ ΨM'.map (c₂.hom.app C) =
      c₂'.hom.app (ΨF.obj C) ≫ sU.map (ατ.app C) ≫ αe.app (ιU.obj C))
    (C : DF) (θ : eU.obj (ιU.obj C) ⟶ πU.obj (aU.obj C))
    (hθ : c₂.inv.app C ≫ c₁.hom.app C = θ) :
    αa.app C ≫ e'.inv.app (ΨM.obj (aU.obj C)) ≫ αr.app (aU.obj C) =
      sU.map (ek.inv.app (ΨF.obj C) ≫ ατ.app C) ≫ αe.app (ιU.obj C) ≫ ΨM'.map θ := by
  subst hθ
  have hc₂' : c₂'.hom.app (ΨF.obj C) =
      c₁'.hom.app (ΨF.obj C) ≫ e'.hom.app _ ≫ sU.map (ek.inv.app (ΨF.obj C)) := by
    rw [reassoc_of% (hunit (ΨF.obj C)), ← Functor.map_comp, Iso.hom_inv_id_app,
      Functor.map_id, Category.comp_id]
  have hαc : αc.app C = c₂'.hom.app (ΨF.obj C) ≫ sU.map (ατ.app C) ≫ αe.app (ιU.obj C) ≫
      ΨM'.map (c₂.inv.app C) := by
    rw [← reassoc_of% (h₂ C), ← Functor.map_comp, Iso.hom_inv_id_app, Functor.map_id,
      Category.comp_id]
  have hnat := e'.inv.naturality (αa.app C)
  simp only [Functor.id_map] at hnat
  have h₁' : I'.map (αa.app C) ≫ αr.app (aU.obj C) =
      c₁'.inv.app (ΨF.obj C) ≫ αc.app C ≫ ΨM'.map (c₁.hom.app C) := by
    rw [h₁ C, Iso.inv_hom_id_app_assoc]
  simp only [Functor.comp_obj, Functor.id_obj] at hnat
  rw [reassoc_of% hnat, h₁', hαc, hc₂']
  simp only [Functor.map_comp, Category.assoc, Iso.inv_hom_id_app_assoc, Functor.id_obj,
    Functor.comp_obj]

/-- The mates of the pullback exchanges related by `CategoryTheory.rebase_pullbackExchange_aux`:
for the mates `χa`, `χe` of `αa`, `αe` and the mate `bc` of the comparison `θ`,
`χa ≫ sL(ρ) = β ≫ Ψη(bc) ≫ χe(πU)`. -/
lemma rebase_pushforwardExchange_aux {DF DX Dη DXη Dk Ds : Type*} [Category DF] [Category DX]
    [Category Dη] [Category DXη] [Category Dk] [Category Ds]
    {aU : DF ⥤ DX} {aL : DX ⥤ DF} (adjA : aU ⊣ aL) {eU : Dη ⥤ DXη} {eL : DXη ⥤ Dη}
    (adjE : eU ⊣ eL) {sU : Dk ⥤ Ds} {sL : Ds ⥤ Dk} (adjS : sU ⊣ sL)
    {ιU : DF ⥤ Dη} {πU : DX ⥤ DXη}
    {ΨF : DF ⥤ Dk} {Ψη : Dη ⥤ Dk} {ΨM : DX ⥤ Ds} {ΨM' : DXη ⥤ Ds}
    (αa : ΨF ⋙ sU ⟶ aU ⋙ ΨM) (αe : Ψη ⋙ sU ⟶ eU ⋙ ΨM') (θ : ιU ⋙ eU ⟶ aU ⋙ πU)
    (ρ : ∀ A, ΨM.obj A ⟶ ΨM'.obj (πU.obj A))
    (hρ : ∀ {A B : DX} (f : A ⟶ B), ΨM.map f ≫ ρ B = ρ A ≫ ΨM'.map (πU.map f))
    (β : ∀ K, ΨF.obj K ⟶ Ψη.obj (ιU.obj K))
    (hyp : ∀ K, αa.app K ≫ ρ (aU.obj K) =
      sU.map (β K) ≫ αe.app (ιU.obj K) ≫ ΨM'.map (θ.app K))
    (χa : aL ⋙ ΨF ⟶ ΨM ⋙ sL) (hχa : χa = (mateEquiv adjA adjS αa))
    (χe : eL ⋙ Ψη ⟶ ΨM' ⋙ sL) (hχe : χe = (mateEquiv adjE adjS αe))
    (bc : aL ⋙ ιU ⟶ πU ⋙ eL) (hbc : bc = (mateEquiv adjA adjE θ)) (E : DX) :
    χa.app E ≫ sL.map (ρ E) = β (aL.obj E) ≫ Ψη.map (bc.app E) ≫ χe.app (πU.obj E) := by
  subst hχa hχe hbc
  apply (adjS.homEquiv _ _).symm.injective
  rw [Adjunction.homEquiv_counit, Adjunction.homEquiv_counit]
  have hca := mateEquiv_counit adjA adjS αa E
  have hce := mateEquiv_counit adjE adjS αe (πU.obj E)
  have hcb := mateEquiv_counit adjA adjE θ E
  have hne := αe.naturality ((mateEquiv adjA adjE θ).app E)
  simp only [Functor.comp_map] at hne
  simp only [Functor.map_comp, Category.assoc, Adjunction.counit_naturality]
  rw [reassoc_of% hca, hρ, reassoc_of% (hyp (aL.obj E)), hce, reassoc_of% hne,
    ← Functor.map_comp, ← Functor.map_comp, hcb]

/-- `CategoryTheory.rebase_pushforwardExchange_aux` with the object `πU.obj E` replaced by an
equal object `P`, through `eqToHom`: this lets the statement be instantiated at an object which is
only definitionally equal to `πU.obj E`. -/
lemma rebase_pushforwardExchange_aux_of_eq {DF DX Dη DXη Dk Ds : Type*} [Category DF]
    [Category DX] [Category Dη] [Category DXη] [Category Dk] [Category Ds]
    {aU : DF ⥤ DX} {aL : DX ⥤ DF} (adjA : aU ⊣ aL) {eU : Dη ⥤ DXη} {eL : DXη ⥤ Dη}
    (adjE : eU ⊣ eL) {sU : Dk ⥤ Ds} {sL : Ds ⥤ Dk} (adjS : sU ⊣ sL)
    {ιU : DF ⥤ Dη} {πU : DX ⥤ DXη}
    {ΨF : DF ⥤ Dk} {Ψη : Dη ⥤ Dk} {ΨM : DX ⥤ Ds} {ΨM' : DXη ⥤ Ds}
    (αa : ΨF ⋙ sU ⟶ aU ⋙ ΨM) (αe : Ψη ⋙ sU ⟶ eU ⋙ ΨM') (θ : ιU ⋙ eU ⟶ aU ⋙ πU)
    (ρ : ∀ A, ΨM.obj A ⟶ ΨM'.obj (πU.obj A))
    (hρ : ∀ {A B : DX} (f : A ⟶ B), ΨM.map f ≫ ρ B = ρ A ≫ ΨM'.map (πU.map f))
    (β : ∀ K, ΨF.obj K ⟶ Ψη.obj (ιU.obj K))
    (hyp : ∀ K, αa.app K ≫ ρ (aU.obj K) =
      sU.map (β K) ≫ αe.app (ιU.obj K) ≫ ΨM'.map (θ.app K))
    (χa : aL ⋙ ΨF ⟶ ΨM ⋙ sL) (hχa : χa = (mateEquiv adjA adjS αa))
    (χe : eL ⋙ Ψη ⟶ ΨM' ⋙ sL) (hχe : χe = (mateEquiv adjE adjS αe))
    (bc : aL ⋙ ιU ⟶ πU ⋙ eL) (hbc : bc = (mateEquiv adjA adjE θ)) (E : DX)
    (P : DXη) (hP : πU.obj E = P) :
    χa.app E ≫ sL.map (ρ E ≫ ΨM'.map (eqToHom hP)) =
      β (aL.obj E) ≫ Ψη.map (bc.app E ≫ eL.map (eqToHom hP)) ≫ χe.app P := by
  subst hP
  simpa using rebase_pushforwardExchange_aux adjA adjE adjS αa αe θ ρ hρ β hyp χa hχa χe hχe bc
    hbc E

/-- The trace computation of the re-based dualizing map: from the relation `hstar` between the
exchanges, the trace property `htrη` over the new base, the trace compatibility `hφ` of the
comparison of dualizing complexes and the unit relation `hunit`, the re-based map
`ρ ≫ ΨM'(φ) ≫ θ'` has the trace property `χF ≫ sL(-) ≫ trs = ΨF(tr) ≫ σF⁻¹`. -/
lemma rebase_trace_aux {CF CX Cη CXη Ck Cs : Type*} [Category CF] [Category CX] [Category Cη]
    [Category CXη] [Category Ck] [Category Cs] {aL : CX ⥤ CF} {eL : CXη ⥤ Cη} {sL : Cs ⥤ Ck}
    {ιU : CF ⥤ Cη} {πU : CX ⥤ CXη} {ΨF : CF ⥤ Ck} {Ψη : Cη ⥤ Ck} {ΨM : CX ⥤ Cs}
    {ΨM' : CXη ⥤ Cs} (χF : aL ⋙ ΨF ⟶ ΨM ⋙ sL) (χη : eL ⋙ Ψη ⟶ ΨM' ⋙ sL)
    (β : ΨF ⟶ ιU ⋙ Ψη) (bc : aL ⋙ ιU ⟶ πU ⋙ eL) (ρ : ΨM ⟶ πU ⋙ ΨM')
    {ω : CX} {ωη : CXη} {ωs : Cs} {oF : CF} {oη : Cη} {ok : Ck}
    (tr : aL.obj ω ⟶ oF) (trη : eL.obj ωη ⟶ oη) (trs : sL.obj ωs ⟶ ok)
    (φ : πU.obj ω ⟶ ωη) (θ' : ΨM'.obj ωη ⟶ ωs) (ε : oη ⟶ ιU.obj oF) [IsIso ε]
    (σF : ok ⟶ ΨF.obj oF) [IsIso σF] (ση : ok ⟶ Ψη.obj oη) [IsIso ση]
    (hstar : χF.app ω ≫ sL.map (ρ.app ω) =
      β.app (aL.obj ω) ≫ Ψη.map (bc.app ω) ≫ χη.app (πU.obj ω))
    (htrη : χη.app ωη ≫ sL.map θ' ≫ trs = Ψη.map trη ≫ inv ση)
    (hφ : bc.app ω ≫ eL.map φ ≫ trη = ιU.map tr ≫ inv ε)
    (hunit : σF ≫ β.app oF = ση ≫ Ψη.map ε) :
    χF.app ω ≫ sL.map (ρ.app ω ≫ ΨM'.map φ ≫ θ') ≫ trs = ΨF.map tr ≫ inv σF := by
  have hnat := χη.naturality φ
  simp only [Functor.comp_map] at hnat
  have hβ := β.naturality tr
  simp only [Functor.comp_map] at hβ
  have hunit' : β.app oF ≫ Ψη.map (inv ε) ≫ inv ση = inv σF := by
    rw [← cancel_epi σF, reassoc_of% hunit, ← Functor.map_comp_assoc, IsIso.hom_inv_id,
      Functor.map_id, Category.id_comp, IsIso.hom_inv_id, IsIso.hom_inv_id]
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% hstar, ← reassoc_of% hnat, htrη, ← Functor.map_comp_assoc,
    ← Functor.map_comp_assoc, Category.assoc, hφ, Functor.map_comp_assoc,
    ← reassoc_of% hβ, hunit']

end CategoryTheory
