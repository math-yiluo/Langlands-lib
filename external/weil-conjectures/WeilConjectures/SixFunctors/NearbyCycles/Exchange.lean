/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.NearbyCycles.Basic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Localizing
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperStarUnitCoherence
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.WeaklyEtale
public import WeilConjectures.CategoryTheory.Adjunction.ExchangeRightPaste

/-!

# Exchange maps of nearby cycles

Let `φ : M ⟶ N` be a morphism of models
(`AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel.Hom`) over `f : X ⟶ Y` and
`f' : X' ⟶ Y'`, with morphisms `t` of total spaces and `g` of geometric generic fibres. This file
constructs the exchange maps of the nearby cycles `Ψ = Li^* Rj_* Lε^*` on the
unbounded derived categories of module objects (blueprint `prose-E-03`):

* the *pullback exchange* `α_f : Lf'^* Ψ_N ⟶ Ψ_M Lf^*`
  (`NearbyCyclesModel.Hom.pullbackExchange`), assembled from the pullback comparisons of the
  squares of special fibres and of identifications, and the base change morphism
  `Lt^* Rj_{N*} ⟶ Rj_{M*} Lg^*` of the square of geometric generic fibres;
* the *pushforward exchange* `χ_f : Ψ_N Rf_* ⟶ Rf'_* Ψ_M`
  (`NearbyCyclesModel.Hom.pushforwardExchange`), the mate of `α_f`;
* the *specialization unit* `σ : Λ_{X'} ⟶ Ψ(Λ_X)` (`NearbyCyclesModel.unit`), the restriction
  to the special fibre of the unit of `Lj^* ⊣ Rj_*`.

## Main results

- `NearbyCyclesModel.Hom.map_unit_comp_pullbackExchange_app`: the unit law
  `α_f(Λ) ∘ Lf'^* σ_N = Ψ_M(ε_f) ∘ σ_M ∘ ε_{f'}⁻¹` (blueprint
  `sec-Base-change-for-nearby-cycles` (2)).
- `NearbyCyclesModel.Hom.unit_comp_map_comp_pushforwardExchange_app`: the unit identity
  `χ_f ∘ Ψ_N(η_f) ∘ σ_N = Rf'_*(σ_M) ∘ η_{f'}` (blueprint `proposition-specialization-trace-class`),
  and `NearbyCyclesModel.Hom.homEquiv_symm_unit_comp_pushforwardExchange_app`: specialization
  commutes with the adjunction `Lf^* ⊣ Rf_*`.
- `NearbyCyclesModel.Hom.isIso_pullbackExchange_of_isIso`: a morphism of models whose morphisms
  of total spaces and of geometric generic fibres are isomorphisms has an invertible pullback
  exchange.

## Implementation notes

The unit law and the unit identity are proved in abstract categories (the private `_aux`
lemmas) and then instantiated: on the derived categories of module objects, `rw` and `simp`
trigger expensive unfoldings of the derived functors, and the kernel must not be asked to compare
different proofs of equalities of derived pullbacks (hence
`ProEtale.CondensedRing.pullbackSquareComparison_eq_trans`). The unit comparisons used are
`ProEtale.CondensedRing.leftDerivedUpperStarUnitIso`.

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

/-! ### Abstract computations

The computations below take place in abstract categories, where they are cheap; they are applied to
the derived categories of module objects afterwards. -/

section Abstract

private lemma squareComparison_app_unit_aux {DX DY DX' DY' : Type*} [Category DX] [Category DY]
    [Category DX'] [Category DY'] {UA UB : DY ⥤ DX'} {Ug : DY ⥤ DY'} {Up' : DY' ⥤ DX'}
    {Up : DY ⥤ DX} {Ug' : DX ⥤ DX'} (c₁ : UA ≅ Ug ⋙ Up') (c₂ : UB ≅ Up ⋙ Ug') (e : UA = UB)
    {oY : DY} {oY' : DY'} {oX : DX} {oX' : DX'} (ug : Ug.obj oY ≅ oY') (up' : Up'.obj oY' ≅ oX')
    (up : Up.obj oY ≅ oX) (ug' : Ug'.obj oX ≅ oX') (uA : UA.obj oY ≅ oX') (uB : UB.obj oY ≅ oX')
    (he : (eqToHom e).app oY = uA.hom ≫ uB.inv)
    (h₁ : c₁.hom.app oY ≫ Up'.map ug.hom ≫ up'.hom = uA.hom)
    (h₂ : c₂.hom.app oY ≫ Ug'.map up.hom ≫ ug'.hom = uB.hom) :
    (c₁.symm ≪≫ eqToIso e ≪≫ c₂).hom.app oY =
      Up'.map ug.hom ≫ up'.hom ≫ ug'.inv ≫ Ug'.map up.inv := by
  simp only [Iso.trans_hom, Iso.symm_hom, eqToIso.hom, NatTrans.comp_app, Category.assoc, he,
    ← h₁, Iso.inv_hom_id_app_assoc]
  congr 2
  rw [Iso.inv_comp_eq, ← h₂]
  simp [← Functor.map_comp]

private lemma unit_pullbackExchange_aux
    {DY' DX' DTN DTM DGN DGM DY DX : Type*} [Category DY'] [Category DX'] [Category DTN]
    [Category DTM] [Category DGN] [Category DGM] [Category DY] [Category DX]
    {Fp' : DY' ⥤ DX'} {IN : DTN ⥤ DY'} {IM : DTM ⥤ DX'} {T : DTN ⥤ DTM}
    {JN : DTN ⥤ DGN} {JNs : DGN ⥤ DTN} {JM : DTM ⥤ DGM} {JMs : DGM ⥤ DTM}
    (adjN : JN ⊣ JNs) (adjM : JM ⊣ JMs)
    {G : DGN ⥤ DGM} {EN : DY ⥤ DGN} {EM : DX ⥤ DGM} {F : DY ⥤ DX}
    (θi : IN ⋙ Fp' ⟶ T ⋙ IM) (θj : T ⋙ JM ⟶ JN ⋙ G) (θε : EN ⋙ G ⟶ F ⋙ EM)
    {oY' : DY'} {oX' : DX'} {oTN : DTN} {oTM : DTM} {oGN : DGN} {oGM : DGM} {oY : DY} {oX : DX}
    (uf' : Fp'.obj oY' ≅ oX') (uiN : IN.obj oTN ≅ oY') (uiM : IM.obj oTM ≅ oX')
    (ut : T.obj oTN ≅ oTM) (ujN : JN.obj oTN ≅ oGN) (ujM : JM.obj oTM ≅ oGM)
    (ug : G.obj oGN ≅ oGM) (uεN : EN.obj oY ≅ oGN) (uεM : EM.obj oX ≅ oGM) (uf : F.obj oY ≅ oX)
    (hi : θi.app oTN = Fp'.map uiN.hom ≫ uf'.hom ≫ uiM.inv ≫ IM.map ut.inv)
    (hj : θj.app oTN = JM.map ut.hom ≫ ujM.hom ≫ ug.inv ≫ G.map ujN.inv)
    (hε : θε.app oY = G.map uεN.hom ≫ ug.hom ≫ uεM.inv ≫ EM.map uf.inv) :
    Fp'.map (uiN.inv ≫ IN.map (adjN.unit.app oTN ≫ JNs.map (ujN.hom ≫ uεN.inv))) ≫
        θi.app (JNs.obj (EN.obj oY)) ≫
          IM.map ((mateEquiv adjN adjM θj).app (EN.obj oY) ≫ JMs.map (θε.app oY)) =
      uf'.hom ≫ (uiM.inv ≫ IM.map (adjM.unit.app oTM ≫ JMs.map (ujM.hom ≫ uεM.inv))) ≫
        IM.map (JMs.map (EM.map uf.inv)) := by
  have nat := θi.naturality (adjN.unit.app oTN ≫ JNs.map (ujN.hom ≫ uεN.inv))
  simp only [Functor.comp_map] at nat
  have hβ := (mateEquiv adjN adjM θj).naturality (ujN.hom ≫ uεN.inv)
  simp only [Functor.comp_map, Functor.map_comp, Category.assoc] at hβ
  have hu := unit_mateEquiv adjN adjM θj oTN
  have hn := adjM.unit.naturality ut.inv
  simp only [Functor.id_map, Functor.comp_map] at hn
  rw [Functor.map_comp, Category.assoc, reassoc_of% nat, hi]
  simp only [Category.assoc, Iso.inv_hom_id_map_assoc, ← Functor.map_comp]
  congr 3
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% hβ, reassoc_of% hu, reassoc_of% hn, hj, hε]
  simp only [← Functor.map_comp, Category.assoc, Iso.inv_hom_id_map_assoc, Iso.inv_hom_id_assoc,
    Iso.inv_hom_id_map_assoc]

private lemma homEquiv_symm_comp_mateEquiv_aux {DY DX DY' DX' : Type*} [Category DY] [Category DX]
    [Category DY'] [Category DX'] {Ff : DY ⥤ DX} {Rf : DX ⥤ DY} {Ff' : DY' ⥤ DX'}
    {Rf' : DX' ⥤ DY'} (adjf : Ff ⊣ Rf) (adjf' : Ff' ⊣ Rf') {ΨN : DY ⥤ DY'} {ΨM : DX ⥤ DX'}
    (α : TwoSquare ΨN Ff Ff' ΨM) {oY : DY} {oX : DX} {oY' : DY'} {oX' : DX'}
    (σN : oY' ⟶ ΨN.obj oY) (σM : oX' ⟶ ΨM.obj oX) (uf' : Ff'.obj oY' ≅ oX')
    (uf : Ff.obj oY ≅ oX) (ha : Ff'.map σN ≫ α.app oY = uf'.hom ≫ σM ≫ ΨM.map uf.inv)
    {E : DX} (h : oY ⟶ Rf.obj E) :
    (adjf'.homEquiv _ _).symm (σN ≫ ΨN.map h ≫ (mateEquiv adjf adjf' α).app E) =
      uf'.hom ≫ σM ≫ ΨM.map (uf.inv ≫ (adjf.homEquiv _ _).symm h) := by
  have hn := α.naturality h
  simp only [Functor.comp_map] at hn
  rw [Adjunction.homEquiv_counit, Adjunction.homEquiv_counit, Functor.map_comp, Functor.map_comp,
    Category.assoc, Category.assoc, mateEquiv_counit, reassoc_of% hn, reassoc_of% ha]
  simp only [Functor.map_comp]

private lemma unit_comp_mateEquiv_aux {DY DX DY' DX' : Type*} [Category DY] [Category DX]
    [Category DY'] [Category DX'] {Ff : DY ⥤ DX} {Rf : DX ⥤ DY} {Ff' : DY' ⥤ DX'}
    {Rf' : DX' ⥤ DY'} (adjf : Ff ⊣ Rf) (adjf' : Ff' ⊣ Rf') {ΨN : DY ⥤ DY'} {ΨM : DX ⥤ DX'}
    (α : TwoSquare ΨN Ff Ff' ΨM) {oY : DY} {oX : DX} {oY' : DY'} {oX' : DX'}
    (σN : oY' ⟶ ΨN.obj oY) (σM : oX' ⟶ ΨM.obj oX) (uf' : Ff'.obj oY' ≅ oX')
    (uf : Ff.obj oY ≅ oX) (ha : Ff'.map σN ≫ α.app oY = uf'.hom ≫ σM ≫ ΨM.map uf.inv) :
    σN ≫ ΨN.map (adjf.unit.app oY ≫ Rf.map uf.hom) ≫ (mateEquiv adjf adjf' α).app oX =
      adjf'.unit.app oY' ≫ Rf'.map (uf'.hom ≫ σM) := by
  apply (adjf'.homEquiv _ _).symm.injective
  rw [homEquiv_symm_comp_mateEquiv_aux adjf adjf' α σN σM uf' uf ha,
    Adjunction.homEquiv_counit, Adjunction.homEquiv_counit]
  simp

private lemma unit_pullbackExchange_aux'
    {DY' DX' DTN DTM DGN DGM DY DX : Type*} [Category DY'] [Category DX'] [Category DTN]
    [Category DTM] [Category DGN] [Category DGM] [Category DY] [Category DX]
    {Fp' : DY' ⥤ DX'} {IN : DTN ⥤ DY'} {IM : DTM ⥤ DX'} {T : DTN ⥤ DTM}
    {JN : DTN ⥤ DGN} {JNs : DGN ⥤ DTN} {JM : DTM ⥤ DGM} {JMs : DGM ⥤ DTM}
    (adjN : JN ⊣ JNs) (adjM : JM ⊣ JMs)
    {G : DGN ⥤ DGM} {EN : DY ⥤ DGN} {EM : DX ⥤ DGM} {F : DY ⥤ DX}
    (θi : IN ⋙ Fp' ⟶ T ⋙ IM) (θj : T ⋙ JM ⟶ JN ⋙ G) (θε : EN ⋙ G ⟶ F ⋙ EM)
    {oY' : DY'} {oX' : DX'} {oTN : DTN} {oTM : DTM} {oGN : DGN} {oGM : DGM} {oY : DY} {oX : DX}
    (uf' : Fp'.obj oY' ≅ oX') (uiN : IN.obj oTN ≅ oY') (uiM : IM.obj oTM ≅ oX')
    (ut : T.obj oTN ≅ oTM) (ujN : JN.obj oTN ≅ oGN) (ujM : JM.obj oTM ≅ oGM)
    (ug : G.obj oGN ≅ oGM) (uεN : EN.obj oY ≅ oGN) (uεM : EM.obj oX ≅ oGM) (uf : F.obj oY ≅ oX)
    (hi : θi.app oTN = Fp'.map uiN.hom ≫ uf'.hom ≫ uiM.inv ≫ IM.map ut.inv)
    (hj : θj.app oTN = JM.map ut.hom ≫ ujM.hom ≫ ug.inv ≫ G.map ujN.inv)
    (hε : θε.app oY = G.map uεN.hom ≫ ug.hom ≫ uεM.inv ≫ EM.map uf.inv) :
    Fp'.map (uiN.inv ≫ IN.map (adjN.unit.app oTN ≫ JNs.map (ujN.hom ≫ uεN.inv))) ≫
        (Functor.whiskerLeft (EN ⋙ JNs) θi ≫
          Functor.whiskerRight (Functor.whiskerLeft EN (mateEquiv adjN adjM θj) ≫
            Functor.whiskerRight θε JMs) IM).app oY =
      uf'.hom ≫ (uiM.inv ≫ IM.map (adjM.unit.app oTM ≫ JMs.map (ujM.hom ≫ uεM.inv))) ≫
        (EM ⋙ JMs ⋙ IM).map uf.inv := by
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.comp_map, Functor.map_comp, Category.assoc]
  have := unit_pullbackExchange_aux adjN adjM θi θj θε uf' uiN uiM ut ujN ujM ug uεN uεM uf hi hj hε
  simp only [Functor.map_comp, Category.assoc] at this
  exact this

private lemma unit_pullbackExchange_aux''
    {DY' DX' DTN DTM DGN DGM DY DX : Type*} [Category DY'] [Category DX'] [Category DTN]
    [Category DTM] [Category DGN] [Category DGM] [Category DY] [Category DX]
    {Fp' : DY' ⥤ DX'} {IN : DTN ⥤ DY'} {IM : DTM ⥤ DX'} {T : DTN ⥤ DTM}
    {JN : DTN ⥤ DGN} {JNs : DGN ⥤ DTN} {JM : DTM ⥤ DGM} {JMs : DGM ⥤ DTM}
    (adjN : JN ⊣ JNs) (adjM : JM ⊣ JMs)
    {G : DGN ⥤ DGM} {EN : DY ⥤ DGN} {EM : DX ⥤ DGM} {F : DY ⥤ DX}
    (θi : IN ⋙ Fp' ⟶ T ⋙ IM) (θj : T ⋙ JM ⟶ JN ⋙ G) (θε : EN ⋙ G ⟶ F ⋙ EM)
    {oY' : DY'} {oX' : DX'} {oTN : DTN} {oTM : DTM} {oGN : DGN} {oGM : DGM} {oY : DY} {oX : DX}
    (uf' : Fp'.obj oY' ≅ oX') (uiN : IN.obj oTN ≅ oY') (uiM : IM.obj oTM ≅ oX')
    (ut : T.obj oTN ≅ oTM) (ujN : JN.obj oTN ≅ oGN) (ujM : JM.obj oTM ≅ oGM)
    (ug : G.obj oGN ≅ oGM) (uεN : EN.obj oY ≅ oGN) (uεM : EM.obj oX ≅ oGM) (uf : F.obj oY ≅ oX)
    (hi : θi.app oTN = Fp'.map uiN.hom ≫ uf'.hom ≫ uiM.inv ≫ IM.map ut.inv)
    (hj : θj.app oTN = JM.map ut.hom ≫ ujM.hom ≫ ug.inv ≫ G.map ujN.inv)
    (hε : θε.app oY = G.map uεN.hom ≫ ug.hom ≫ uεM.inv ≫ EM.map uf.inv)
    (α : (EN ⋙ JNs ⋙ IN) ⋙ Fp' ⟶ F ⋙ EM ⋙ JMs ⋙ IM)
    (hα : α = Functor.whiskerLeft (EN ⋙ JNs) θi ≫
          Functor.whiskerRight (Functor.whiskerLeft EN (mateEquiv adjN adjM θj) ≫
            Functor.whiskerRight θε JMs) IM)
    (σN : oY' ⟶ (EN ⋙ JNs ⋙ IN).obj oY)
    (hσN : σN = uiN.inv ≫ IN.map (adjN.unit.app oTN ≫ JNs.map (ujN.hom ≫ uεN.inv)))
    (σM : oX' ⟶ (EM ⋙ JMs ⋙ IM).obj oX)
    (hσM : σM = uiM.inv ≫ IM.map (adjM.unit.app oTM ≫ JMs.map (ujM.hom ≫ uεM.inv))) :
    Fp'.map σN ≫ α.app oY = uf'.hom ≫ σM ≫ (EM ⋙ JMs ⋙ IM).map uf.inv := by
  subst hα hσN hσM
  exact unit_pullbackExchange_aux' adjN adjM θi θj θε uf' uiN uiM ut ujN ujM ug uεN uεM uf hi hj hε

private lemma homEquiv_symm_comp_mateEquiv_aux' {DY DX DY' DX' : Type*} [Category DY]
    [Category DX] [Category DY'] [Category DX'] {Ff : DY ⥤ DX} {Rf : DX ⥤ DY} {Ff' : DY' ⥤ DX'}
    {Rf' : DX' ⥤ DY'} (adjf : Ff ⊣ Rf) (adjf' : Ff' ⊣ Rf') {ΨN : DY ⥤ DY'} {ΨM : DX ⥤ DX'}
    (α : ΨN ⋙ Ff' ⟶ Ff ⋙ ΨM) (χ : Rf ⋙ ΨN ⟶ ΨM ⋙ Rf')
    (hχ : χ = (mateEquiv adjf adjf' α)) {oY : DY} {oX : DX} {oY' : DY'} {oX' : DX'}
    (σN : oY' ⟶ ΨN.obj oY) (σM : oX' ⟶ ΨM.obj oX) (uf' : Ff'.obj oY' ≅ oX')
    (uf : Ff.obj oY ≅ oX) (ha : Ff'.map σN ≫ α.app oY = uf'.hom ≫ σM ≫ ΨM.map uf.inv)
    {E : DX} (h : oY ⟶ Rf.obj E) :
    (adjf'.homEquiv _ _).symm (σN ≫ ΨN.map h ≫ χ.app E) =
      uf'.hom ≫ σM ≫ ΨM.map (uf.inv ≫ (adjf.homEquiv _ _).symm h) := by
  subst hχ
  exact homEquiv_symm_comp_mateEquiv_aux adjf adjf' α σN σM uf' uf ha h

private lemma unit_comp_mateEquiv_aux' {DY DX DY' DX' : Type*} [Category DY] [Category DX]
    [Category DY'] [Category DX'] {Ff : DY ⥤ DX} {Rf : DX ⥤ DY} {Ff' : DY' ⥤ DX'}
    {Rf' : DX' ⥤ DY'} (adjf : Ff ⊣ Rf) (adjf' : Ff' ⊣ Rf') {ΨN : DY ⥤ DY'} {ΨM : DX ⥤ DX'}
    (α : ΨN ⋙ Ff' ⟶ Ff ⋙ ΨM) (χ : Rf ⋙ ΨN ⟶ ΨM ⋙ Rf')
    (hχ : χ = (mateEquiv adjf adjf' α)) {oY : DY} {oX : DX} {oY' : DY'} {oX' : DX'}
    (σN : oY' ⟶ ΨN.obj oY) (σM : oX' ⟶ ΨM.obj oX) (uf' : Ff'.obj oY' ≅ oX')
    (uf : Ff.obj oY ≅ oX) (ha : Ff'.map σN ≫ α.app oY = uf'.hom ≫ σM ≫ ΨM.map uf.inv) :
    σN ≫ ΨN.map (adjf.unit.app oY ≫ Rf.map uf.hom) ≫ χ.app oX =
      adjf'.unit.app oY' ≫ Rf'.map (uf'.hom ≫ σM) := by
  subst hχ
  exact unit_comp_mateEquiv_aux adjf adjf' α σN σM uf' uf ha

private lemma unit_mateEquiv_aux {DY DX DY' DX' : Type*} [Category DY] [Category DX]
    [Category DY'] [Category DX'] {Ff : DY ⥤ DX} {Rf : DX ⥤ DY} {Ff' : DY' ⥤ DX'}
    {Rf' : DX' ⥤ DY'} (adjf : Ff ⊣ Rf) (adjf' : Ff' ⊣ Rf') {ΨN : DY ⥤ DY'} {ΨM : DX ⥤ DX'}
    (α : ΨN ⋙ Ff' ⟶ Ff ⋙ ΨM) (χ : Rf ⋙ ΨN ⟶ ΨM ⋙ Rf')
    (hχ : χ = (mateEquiv adjf adjf' α)) (K : DY) :
    ΨN.map (adjf.unit.app K) ≫ χ.app (Ff.obj K) =
      adjf'.unit.app (ΨN.obj K) ≫ Rf'.map (α.app K) := by
  subst hχ
  exact unit_mateEquiv adjf adjf' α K

private lemma mateEquiv_counit_aux {DY DX DY' DX' : Type*} [Category DY] [Category DX]
    [Category DY'] [Category DX'] {Ff : DY ⥤ DX} {Rf : DX ⥤ DY} {Ff' : DY' ⥤ DX'}
    {Rf' : DX' ⥤ DY'} (adjf : Ff ⊣ Rf) (adjf' : Ff' ⊣ Rf') {ΨN : DY ⥤ DY'} {ΨM : DX ⥤ DX'}
    (α : ΨN ⋙ Ff' ⟶ Ff ⋙ ΨM) (χ : Rf ⋙ ΨN ⟶ ΨM ⋙ Rf')
    (hχ : χ = (mateEquiv adjf adjf' α)) (E : DX) :
    Ff'.map (χ.app E) ≫ adjf'.counit.app (ΨM.obj E) =
      α.app (Rf.obj E) ≫ ΨM.map (adjf.counit.app E) := by
  subst hχ
  exact mateEquiv_counit adjf adjf' α E

private lemma unit_comp_mateEquiv_aux₂ {DY DX DY' DX' : Type*} [Category DY] [Category DX]
    [Category DY'] [Category DX'] {Ff : DY ⥤ DX} {Rf : DX ⥤ DY} {Ff' : DY' ⥤ DX'}
    {Rf' : DX' ⥤ DY'} (adjf : Ff ⊣ Rf) (adjf' : Ff' ⊣ Rf') {ΨN : DY ⥤ DY'} {ΨM : DX ⥤ DX'}
    (α : ΨN ⋙ Ff' ⟶ Ff ⋙ ΨM) (χ : Rf ⋙ ΨN ⟶ ΨM ⋙ Rf')
    (hχ : χ = (mateEquiv adjf adjf' α)) {oY : DY} {oX : DX} {oY' : DY'} {oX' : DX'}
    (σN : oY' ⟶ ΨN.obj oY) (σM : oX' ⟶ ΨM.obj oX) (uf' : Ff'.obj oY' ≅ oX')
    (uf : Ff.obj oY ≅ oX) (ha : Ff'.map σN ≫ α.app oY = uf'.hom ≫ σM ≫ ΨM.map uf.inv) :
    σN ≫ ΨN.map (adjf.unit.app oY) ≫ χ.app (Ff.obj oY) =
      adjf'.unit.app oY' ≫ Rf'.map (uf'.hom ≫ σM ≫ ΨM.map uf.inv) := by
  have hb := unit_comp_mateEquiv_aux adjf adjf' α σN σM uf' uf ha
  subst hχ
  have hn := (mateEquiv adjf adjf' α).naturality uf.hom
  simp only [Functor.comp_map] at hn
  rw [Functor.map_comp, Category.assoc, hn] at hb
  rw [← cancel_mono (Rf'.map (ΨM.map uf.hom))]
  simp only [Category.assoc] at hb ⊢
  rw [hb]
  simp [← Functor.map_comp]

end Abstract

/-! ### The pullback comparisons at the unit -/

section Unit

variable {X Y X' Y' : Scheme.{u}}

/-- The transport `L(a)^* = L(b)^*` along an equality `a = b` is, at the unit, the composite of
the unit comparisons `L(a)^* Λ ≅ Λ ≅ L(b)^* Λ`. -/
lemma eqToHom_app_unit_leftDerivedUpperStar {a b : X ⟶ Y} (h : a = b)
    (e : L((a)^*⟦Λ⟧) = L((b)^*⟦Λ⟧)) :
    (eqToHom e).app (𝟙_ _) =
      (leftDerivedUpperStarUnitIso Λ a).hom ≫ (leftDerivedUpperStarUnitIso Λ b).inv := by
  subst h
  simp

variable {p : X ⟶ Y} {g : Y' ⟶ Y} {p' : X' ⟶ Y'} {g' : X' ⟶ X}

/-- The pullback comparison of a commutative square is the composite of the composition
isomorphisms with the transport along any proof of the equality of the two derived pullbacks. -/
lemma pullbackSquareComparison_eq_trans (sq : CommSq g' p' p g)
    (e : L((p' ≫ g)^*⟦Λ⟧) = L((g' ≫ p)^*⟦Λ⟧)) :
    pullbackSquareComparison Λ sq =
      (leftDerivedUpperStarComp Λ p' g).symm ≪≫ eqToIso e ≪≫ leftDerivedUpperStarComp Λ g' p :=
  rfl

/-- The pullback comparison `Lp'^* Lg^* ≅ Lg'^* Lp^*` of a commutative square is, at the unit,
the composite of the unit comparisons `Lp'^* Lg^* Λ ≅ Λ ≅ Lg'^* Lp^* Λ`. -/
lemma pullbackSquareComparison_hom_app_unit (sq : CommSq g' p' p g) :
    (pullbackSquareComparison Λ sq).hom.app (𝟙_ _) =
      L((p')^*⟦Λ⟧).map (leftDerivedUpperStarUnitIso Λ g).hom ≫
        (leftDerivedUpperStarUnitIso Λ p').hom ≫ (leftDerivedUpperStarUnitIso Λ g').inv ≫
          L((g')^*⟦Λ⟧).map (leftDerivedUpperStarUnitIso Λ p).inv := by
  obtain e : L((p' ≫ g)^*⟦Λ⟧) = L((g' ≫ p)^*⟦Λ⟧) := by rw [sq.w]
  refine (congrArg (fun i ↦ i.hom.app (𝟙_ _)) (pullbackSquareComparison_eq_trans Λ sq e)).trans ?_
  exact squareComparison_app_unit_aux _ _ e (leftDerivedUpperStarUnitIso Λ g)
    (leftDerivedUpperStarUnitIso Λ p') (leftDerivedUpperStarUnitIso Λ p)
    (leftDerivedUpperStarUnitIso Λ g') _ _ (eqToHom_app_unit_leftDerivedUpperStar Λ sq.w.symm e)
    (leftDerivedUpperStarComp_hom_app_unit Λ p' g) (leftDerivedUpperStarComp_hom_app_unit Λ g' p)

end Unit

namespace NearbyCyclesModel

variable {X X' Y Y' : Scheme.{u}}

/-- Nearby cycles preserve zero objects. -/
lemma isZero_nearbyCycles_obj (M : NearbyCyclesModel X X')
    {E : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))}
    (hE : IsZero E) : IsZero ((M.nearbyCycles Λ).obj E) :=
  Functor.map_isZero (L((M.ε)^*⟦Λ⟧) ⋙ R((M.j)_*⟦Λ⟧) ⋙ L((M.i)^*⟦Λ⟧)) hE

/-- The *specialization unit* `σ : Λ_{X'} ⟶ Ψ(Λ_X)` of a model: the restriction
`Li^* (Λ ⟶ Rj_* Lj^* Λ)` to the special fibre of the unit of `Lj^* ⊣ Rj_*`, combined with the
unit comparisons `Λ_{X'} ≅ Li^* Λ` and `Lj^* Λ ≅ Λ ≅ Lε^* Λ`. -/
noncomputable def unit (M : NearbyCyclesModel X X') :
    𝟙_ _ ⟶ (M.nearbyCycles Λ).obj (𝟙_ _) :=
  (leftDerivedUpperStarUnitIso Λ M.i).inv ≫
    L((M.i)^*⟦Λ⟧).map ((derivedUpperStarLowerStarAdjunction Λ M.j).unit.app (𝟙_ _) ≫
      R((M.j)_*⟦Λ⟧).map ((leftDerivedUpperStarUnitIso Λ M.j).hom ≫
        (leftDerivedUpperStarUnitIso Λ M.ε).inv))

variable {M : NearbyCyclesModel X X'} {N : NearbyCyclesModel Y Y'} {f : X ⟶ Y} {f' : X' ⟶ Y'}

namespace Hom

variable (φ : M.Hom N f f')

/-- The square `M.i ≫ total = f' ≫ N.i` of special fibres. -/
lemma commSq_i : CommSq M.i f' φ.total N.i := ⟨φ.comm_i.symm⟩

/-- The square `generic ≫ N.j = M.j ≫ total` of geometric generic fibres. -/
lemma commSq_j : CommSq φ.generic M.j N.j φ.total := ⟨φ.comm_j⟩

/-- The square `M.ε ≫ f = generic ≫ N.ε` of identifications. -/
lemma commSq_ε : CommSq M.ε φ.generic f N.ε := ⟨φ.comm_ε.symm⟩

/-- The *pullback exchange* `α_f : Lf'^* Ψ_N ⟶ Ψ_M Lf^*` of a morphism of models (blueprint
`prose-E-03` (1)): the pullback comparison `Lf'^* Li_N^* ≅ Li_M^* Lt^*` of the
special fibres (`t` the morphism of total spaces), then `Li_M^*` of the base change morphism
`Lt^* Rj_{N*} ⟶ Rj_{M*} Lg^*` of the square of geometric generic fibres (`g` the morphism of
geometric generic fibres; the mate of the pullback comparison `Lj_M^* Lt^* ≅ Lg^* Lj_N^*`, that is
`ProEtale.CondensedRing.baseChangeMap` by `Adjunction.exchangeRight_eq_mateEquiv`), and finally
`Li_M^* Rj_{M*}` of the pullback comparison `Lg^* Lε_N^* ≅ Lε_M^* Lf^*`. -/
noncomputable def pullbackExchange :
    N.nearbyCycles Λ ⋙ L((f')^*⟦Λ⟧) ⟶ L((f)^*⟦Λ⟧) ⋙ M.nearbyCycles Λ :=
  Functor.whiskerLeft (L((N.ε)^*⟦Λ⟧) ⋙ R((N.j)_*⟦Λ⟧))
      (pullbackSquareComparison Λ φ.commSq_i).hom ≫
    Functor.whiskerRight
      (Functor.whiskerLeft L((N.ε)^*⟦Λ⟧)
          (mateEquiv (derivedUpperStarLowerStarAdjunction Λ N.j)
            (derivedUpperStarLowerStarAdjunction Λ M.j)
            (pullbackSquareComparison Λ φ.commSq_j).hom) ≫
        Functor.whiskerRight (pullbackSquareComparison Λ φ.commSq_ε).hom R((M.j)_*⟦Λ⟧))
      L((M.i)^*⟦Λ⟧)

/-- If the morphisms of total spaces and of geometric generic fibres of a morphism of models are
isomorphisms, its pullback exchange `α : Lf'^* Ψ_N ⟶ Ψ_M Lf^*` is an isomorphism: the base change
morphism of the square of geometric generic fibres is invertible by weakly étale base change.
The morphism of models is the commutative diagram
```
X ←─ε── M.generic ──j─→ M.total ←──i── X'
│f      │φ.generic      │φ.total       │f'
Y ←─ε── N.generic ──j─→ N.total ←──i── Y'
```
-/
lemma isIso_pullbackExchange_of_isIso [IsIso φ.total] [IsIso φ.generic] :
    IsIso (φ.pullbackExchange Λ) := by
  have : IsIso (mateEquiv (derivedUpperStarLowerStarAdjunction Λ N.j)
      (derivedUpperStarLowerStarAdjunction Λ M.j)
      (pullbackSquareComparison Λ φ.commSq_j).hom) := by
    have := isIso_baseChangeMap_of_weaklyEtale Λ (IsPullback.of_horiz_isIso φ.commSq_j)
    rwa [baseChangeMap, Adjunction.exchangeRight_eq_mateEquiv] at this
  unfold pullbackExchange
  infer_instance

/-- The *pushforward exchange* `χ_f : Ψ_N Rf_* ⟶ Rf'_* Ψ_M` of a morphism of models (blueprint
`prose-E-03` (2)): the mate of the pullback exchange `α_f` along the
adjunctions `Lf^* ⊣ Rf_*` and `Lf'^* ⊣ Rf'_*`. -/
noncomputable def pushforwardExchange :
    R((f)_*⟦Λ⟧) ⋙ N.nearbyCycles Λ ⟶ M.nearbyCycles Λ ⋙ R((f')_*⟦Λ⟧) :=
  (mateEquiv (derivedUpperStarLowerStarAdjunction Λ f)
    (derivedUpperStarLowerStarAdjunction Λ f') (φ.pullbackExchange Λ))

/-- The pushforward exchange is the mate of the pullback exchange: compatibility with the units
of `Lf^* ⊣ Rf_*` and `Lf'^* ⊣ Rf'_*`. -/
lemma map_unit_app_comp_pushforwardExchange_app
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj Λ Y))) :
    (N.nearbyCycles Λ).map ((derivedUpperStarLowerStarAdjunction Λ f).unit.app K) ≫
        (φ.pushforwardExchange Λ).app (L((f)^*⟦Λ⟧).obj K) =
      (derivedUpperStarLowerStarAdjunction Λ f').unit.app ((N.nearbyCycles Λ).obj K) ≫
        R((f')_*⟦Λ⟧).map ((φ.pullbackExchange Λ).app K) :=
  unit_mateEquiv_aux (derivedUpperStarLowerStarAdjunction Λ f)
    (derivedUpperStarLowerStarAdjunction Λ f') (φ.pullbackExchange Λ) (φ.pushforwardExchange Λ)
    rfl K

/-- The pushforward exchange is the mate of the pullback exchange: compatibility with the counits
of `Lf^* ⊣ Rf_*` and `Lf'^* ⊣ Rf'_*`. -/
lemma map_pushforwardExchange_app_comp_counit_app
    (E : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X))) :
    L((f')^*⟦Λ⟧).map ((φ.pushforwardExchange Λ).app E) ≫
        (derivedUpperStarLowerStarAdjunction Λ f').counit.app ((M.nearbyCycles Λ).obj E) =
      (φ.pullbackExchange Λ).app (R((f)_*⟦Λ⟧).obj E) ≫
        (M.nearbyCycles Λ).map ((derivedUpperStarLowerStarAdjunction Λ f).counit.app E) :=
  mateEquiv_counit_aux (derivedUpperStarLowerStarAdjunction Λ f)
    (derivedUpperStarLowerStarAdjunction Λ f') (φ.pullbackExchange Λ) (φ.pushforwardExchange Λ)
    rfl E

/-- **Unit law of the pullback exchange** (blueprint `sec-Base-change-for-nearby-cycles` (2)):
`α_f(Λ) ∘ Lf'^* σ_N = Ψ_M(ε_f) ∘ σ_M ∘ ε_{f'}⁻¹`, where `ε_f : Λ_X ≅ Lf^* Λ_Y` and
`ε_{f'} : Λ_{X'} ≅ Lf'^* Λ_{Y'}` are the unit comparisons. -/
lemma map_unit_comp_pullbackExchange_app :
    L((f')^*⟦Λ⟧).map (N.unit Λ) ≫ (φ.pullbackExchange Λ).app (𝟙_ _) =
      (leftDerivedUpperStarUnitIso Λ f').hom ≫ M.unit Λ ≫
        (M.nearbyCycles Λ).map (leftDerivedUpperStarUnitIso Λ f).inv := by
  exact unit_pullbackExchange_aux'' (derivedUpperStarLowerStarAdjunction Λ N.j)
    (derivedUpperStarLowerStarAdjunction Λ M.j) (pullbackSquareComparison Λ φ.commSq_i).hom
    (pullbackSquareComparison Λ φ.commSq_j).hom (pullbackSquareComparison Λ φ.commSq_ε).hom
    (leftDerivedUpperStarUnitIso Λ f') (leftDerivedUpperStarUnitIso Λ N.i)
    (leftDerivedUpperStarUnitIso Λ M.i) (leftDerivedUpperStarUnitIso Λ φ.total)
    (leftDerivedUpperStarUnitIso Λ N.j) (leftDerivedUpperStarUnitIso Λ M.j)
    (leftDerivedUpperStarUnitIso Λ φ.generic) (leftDerivedUpperStarUnitIso Λ N.ε)
    (leftDerivedUpperStarUnitIso Λ M.ε) (leftDerivedUpperStarUnitIso Λ f)
    (pullbackSquareComparison_hom_app_unit Λ φ.commSq_i)
    (pullbackSquareComparison_hom_app_unit Λ φ.commSq_j)
    (pullbackSquareComparison_hom_app_unit Λ φ.commSq_ε)
    (φ.pullbackExchange Λ) rfl (N.unit Λ) rfl (M.unit Λ) rfl

/-- **Specialization commutes with the adjunction `Lf^* ⊣ Rf_*`**: for `h : Λ_Y ⟶ Rf_* E`, the
`Lf'^* ⊣ Rf'_*` adjoint of `χ_f(E) ∘ Ψ_N(h) ∘ σ_N : Λ_{Y'} ⟶ Rf'_* Ψ_M(E)` is
`Ψ_M(h^♭ ∘ ε_f) ∘ σ_M ∘ ε_{f'}⁻¹`, where `h^♭ : Lf^* Λ_Y ⟶ E` is the adjoint of `h`. -/
lemma homEquiv_symm_unit_comp_pushforwardExchange_app
    {E : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))}
    (h : 𝟙_ _ ⟶ R((f)_*⟦Λ⟧).obj E) :
    ((derivedUpperStarLowerStarAdjunction Λ f').homEquiv _ _).symm
        (N.unit Λ ≫ (N.nearbyCycles Λ).map h ≫ (φ.pushforwardExchange Λ).app E) =
      (leftDerivedUpperStarUnitIso Λ f').hom ≫ M.unit Λ ≫ (M.nearbyCycles Λ).map
        ((leftDerivedUpperStarUnitIso Λ f).inv ≫
          ((derivedUpperStarLowerStarAdjunction Λ f).homEquiv _ _).symm h) :=
  homEquiv_symm_comp_mateEquiv_aux' (derivedUpperStarLowerStarAdjunction Λ f)
    (derivedUpperStarLowerStarAdjunction Λ f') (φ.pullbackExchange Λ) (φ.pushforwardExchange Λ)
    rfl
    (N.unit Λ) (M.unit Λ) (leftDerivedUpperStarUnitIso Λ f') (leftDerivedUpperStarUnitIso Λ f)
    (φ.map_unit_comp_pullbackExchange_app Λ) h

/-- **Unit identity of the pushforward exchange** (blueprint
`proposition-specialization-trace-class`): `χ_f(Λ_X) ∘ Ψ_N(η_f) ∘ σ_N = Rf'_*(σ_M) ∘ η_{f'}`, up to
the unit comparisons `ε_f : Λ_X ≅ Lf^* Λ_Y` and `ε_{f'} : Λ_{X'} ≅ Lf'^* Λ_{Y'}`. -/
lemma unit_comp_map_comp_pushforwardExchange_app :
    N.unit Λ ≫ (N.nearbyCycles Λ).map ((derivedUpperStarLowerStarAdjunction Λ f).unit.app (𝟙_ _) ≫
        R((f)_*⟦Λ⟧).map (leftDerivedUpperStarUnitIso Λ f).hom) ≫
        (φ.pushforwardExchange Λ).app (𝟙_ _) =
      (derivedUpperStarLowerStarAdjunction Λ f').unit.app (𝟙_ _) ≫
        R((f')_*⟦Λ⟧).map ((leftDerivedUpperStarUnitIso Λ f').hom ≫ M.unit Λ) :=
  unit_comp_mateEquiv_aux' (derivedUpperStarLowerStarAdjunction Λ f)
    (derivedUpperStarLowerStarAdjunction Λ f') (φ.pullbackExchange Λ) (φ.pushforwardExchange Λ)
    rfl
    (N.unit Λ) (M.unit Λ) (leftDerivedUpperStarUnitIso Λ f') (leftDerivedUpperStarUnitIso Λ f)
    (φ.map_unit_comp_pullbackExchange_app Λ)

/-- The unit identity of the pushforward exchange in the form
`χ_f(Lf^* Λ_Y) ∘ Ψ_N(η_f) ∘ σ_N = Rf'_*(Ψ_M(ε_f) ∘ σ_M ∘ ε_{f'}⁻¹) ∘ η_{f'}`. -/
lemma unit_comp_map_unit_comp_pushforwardExchange_app :
    N.unit Λ ≫ (N.nearbyCycles Λ).map ((derivedUpperStarLowerStarAdjunction Λ f).unit.app (𝟙_ _)) ≫
        (φ.pushforwardExchange Λ).app _ =
      (derivedUpperStarLowerStarAdjunction Λ f').unit.app (𝟙_ _) ≫
        R((f')_*⟦Λ⟧).map ((leftDerivedUpperStarUnitIso Λ f').hom ≫ M.unit Λ ≫
          (M.nearbyCycles Λ).map (leftDerivedUpperStarUnitIso Λ f).inv) :=
  unit_comp_mateEquiv_aux₂ (derivedUpperStarLowerStarAdjunction Λ f)
    (derivedUpperStarLowerStarAdjunction Λ f') (φ.pullbackExchange Λ) (φ.pushforwardExchange Λ)
    rfl (N.unit Λ) (M.unit Λ) (leftDerivedUpperStarUnitIso Λ f') (leftDerivedUpperStarUnitIso Λ f)
    (φ.map_unit_comp_pullbackExchange_app Λ)

/-- If the pullback exchange `α_f : Lf'^* Ψ_N ⟶ Ψ_M Lf^*` is invertible at `K` and `Lf^* K`
vanishes, then so does `Lf'^* Ψ_N K`. -/
lemma isZero_upperStar_nearbyCycles_obj
    {K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y))}
    [IsIso ((φ.pullbackExchange Λ).app K)] (hK : IsZero ((L((f)^*⟦Λ⟧)).obj K)) :
    IsZero ((L((f')^*⟦Λ⟧)).obj ((N.nearbyCycles Λ).obj K)) :=
  (M.isZero_nearbyCycles_obj Λ hK).of_iso (asIso ((φ.pullbackExchange Λ).app K))

end Hom

end NearbyCyclesModel

end AlgebraicGeometry.ProEtale.CondensedRing
